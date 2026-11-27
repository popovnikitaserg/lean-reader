import Lean
import Lean.Elab.Frontend
import Lean.Elab.InfoTree
import Lean.Meta

open Lean Elab

def positionJson (ctx : ContextInfo) (pos : String.Pos.Raw) : Json :=
  let p := ctx.fileMap.toPosition pos
  Json.mkObj [("line", p.line), ("column", p.column)]

def syntaxRangeJson (ctx : ContextInfo) (stx : Syntax) : Json :=
  let startPos := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD startPos
  Json.mkObj [
    ("start", positionJson ctx startPos),
    ("end", positionJson ctx endPos),
  ]

def syntaxText (ctx : ContextInfo) (stx : Syntax) : IO String := do
  let fmt ← ctx.runMetaM {} (ctx.ppSyntax {} stx)
  let text := fmt.pretty
  if text.startsWith "failed to pretty print" then
    return stx.prettyPrint.pretty
  return text

def exprText (ctx : ContextInfo) (lctx : LocalContext) (mctx : MetavarContext) (expr : Expr) : IO String := do
  let fmt ← ctx.runMetaM lctx (Lean.Meta.withMCtx mctx (Lean.Meta.ppExpr expr))
  return fmt.pretty

def rawExpr (expr : Expr) : String :=
  s!"{repr expr}"

def rawExprId (projectId declName kind : String) (expr : Expr) : String :=
  s!"expr:{projectId}:{declName}:{kind}:{hash (rawExpr expr)}"

partial def collectExprSymbols (expr : Expr) (fvars : Array FVarId := #[])
    (consts : Array Name := #[]) : Array FVarId × Array Name :=
  match expr with
  | .fvar fvarId =>
      (if fvars.contains fvarId then fvars else fvars.push fvarId, consts)
  | .const name _ =>
      (fvars, if consts.contains name then consts else consts.push name)
  | .app fn arg =>
      let (fvars, consts) := collectExprSymbols fn fvars consts
      collectExprSymbols arg fvars consts
  | .lam _ type body _ =>
      let (fvars, consts) := collectExprSymbols type fvars consts
      collectExprSymbols body fvars consts
  | .forallE _ type body _ =>
      let (fvars, consts) := collectExprSymbols type fvars consts
      collectExprSymbols body fvars consts
  | .letE _ type value body _ =>
      let (fvars, consts) := collectExprSymbols type fvars consts
      let (fvars, consts) := collectExprSymbols value fvars consts
      collectExprSymbols body fvars consts
  | .mdata _ value => collectExprSymbols value fvars consts
  | .proj _ _ value => collectExprSymbols value fvars consts
  | _ => (fvars, consts)

def localDeclJson (ctx : ContextInfo) (projectId declName : String)
    (mctx : MetavarContext) (lctx : LocalContext) (localDecl : LocalDecl) : IO Json := do
  let (fvarId, userName, type, value?) :=
    match localDecl with
    | .cdecl _ fvarId userName type _ _ => (fvarId, userName, type, none)
    | .ldecl _ fvarId userName type value _ _ => (fvarId, userName, type, some value)
  let typePretty ← exprText ctx lctx mctx type
  let typeExprRaw := rawExpr type
  let valuePretty ← match value? with
    | some value => do
        let pretty ← exprText ctx lctx mctx value
        pure (Json.str pretty)
    | none => pure Json.null
  pure <| Json.mkObj [
    ("fvar_id", fvarId.name.toString),
    ("user_name", userName.toString),
    ("inaccessible_name", Json.bool (userName.isAnonymous || userName.toString.contains '✝')),
    ("type_pretty", typePretty),
    ("type_expr_id", rawExprId projectId declName "local-type" type),
    ("type_expr_raw", typeExprRaw),
    ("is_let", Json.bool value?.isSome),
    ("value_pretty", valuePretty),
  ]

def goalStateJson (ctx : ContextInfo) (projectId declName : String)
    (mctx : MetavarContext) (mvarId : MVarId) : IO Json := do
  match mctx.findDecl? mvarId with
  | none =>
      pure <| Json.mkObj [
        ("mvar_id", mvarId.name.toString),
        ("target_pretty", Json.null),
        ("target_expr_id", Json.null),
        ("target_expr_raw", Json.null),
        ("locals", Json.arr #[]),
      ]
  | some decl =>
      let targetPretty ← exprText ctx decl.lctx mctx decl.type
      let mut locals : Array Json := #[]
      for fvarId in decl.lctx.getFVarIds do
        if let some localDecl := decl.lctx.find? fvarId then
          locals := locals.push (← localDeclJson ctx projectId declName mctx decl.lctx localDecl)
      pure <| Json.mkObj [
        ("mvar_id", mvarId.name.toString),
        ("target_pretty", targetPretty),
        ("target_expr_id", rawExprId projectId declName "goal-type" decl.type),
        ("target_expr_raw", rawExpr decl.type),
        ("locals", Json.arr locals),
      ]

def usedFVarJson (ctx : ContextInfo) (projectId declName : String)
    (mctx : MetavarContext) (lctx : LocalContext) (fvarId : FVarId) : IO Json := do
  match lctx.find? fvarId with
  | none =>
      pure <| Json.mkObj [("fvar_id", fvarId.name.toString)]
  | some localDecl =>
      localDeclJson ctx projectId declName mctx lctx localDecl

unsafe def main (args : List String) : IO Unit := do
  let projectId :: moduleName :: fileName :: _ := args
    | throw <| IO.userError "usage: PassB project_id module_name file.lean"

  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let input ← IO.FS.readFile fileName
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  let (env, headerMessages) ← Elab.processHeader header {} headerMessages inputCtx
  let initialState := { Command.mkState env headerMessages {} with infoState.enabled := true }
  let frontendState ← IO.processCommands inputCtx parserState initialState
  let commandState := frontendState.commandState

  for message in commandState.messages.toList do
    let text ← message.toString
    if message.severity == MessageSeverity.error then
      IO.println <| Json.mkObj [
        ("schema_version", "2"),
        ("record", "error"),
        ("project_id", projectId),
        ("module", moduleName),
        ("message", text),
      ] |>.compress

  let ordinal ← IO.mkRef (0 : Nat)
  let tacticRecordIndex ← IO.mkRef (0 : Nat)
  let termRecordIndex ← IO.mkRef (0 : Nat)

  for tree in commandState.infoState.trees do
    tree.visitM'
      (preNode := fun _ info _ => do
        let current ← ordinal.get
        ordinal.set (current + 1)
        pure true)
      (postNode := fun ctx info _ => do
        let current ← ordinal.get
        match info with
        | .ofTacticInfo tactic =>
            let recordIndex ← tacticRecordIndex.get
            tacticRecordIndex.set (recordIndex + 1)
            let tacticText ← syntaxText ctx tactic.stx
            let synthetic := !tactic.stx.getHeadInfo matches .original .. 
            let declName := ctx.parentDecl?.map toString |>.getD "unknown"
            let mut assignments : Array Json := #[]
            for mvarId in tactic.goalsBefore do
              match tactic.mctxAfter.getExprAssignmentCore? mvarId with
              | some expr =>
                  let goalDecl? := tactic.mctxBefore.findDecl? mvarId
                  let lctx := goalDecl?.map (·.lctx) |>.getD {}
                  let expr ← ctx.runMetaM lctx
                    (Lean.Meta.withMCtx tactic.mctxAfter (Lean.instantiateMVars expr))
                  let pretty ← exprText ctx lctx tactic.mctxAfter expr
                  let (fvarIds, constNames) := collectExprSymbols expr
                  let mut usedFVars : Array Json := #[]
                  for fvarId in fvarIds do
                    usedFVars := usedFVars.push
                      (← usedFVarJson ctx projectId declName tactic.mctxAfter lctx fvarId)
                  assignments := assignments.push <| Json.mkObj [
                    ("mvar_id", mvarId.name.toString),
                    ("kind", "direct"),
                    ("expr_pretty", pretty),
                    ("expr_raw", rawExpr expr),
                    ("expr_id", rawExprId projectId declName s!"proof-term-{current}" expr),
                    ("used_fvars", Json.arr usedFVars),
                    ("used_consts", Json.arr (constNames.map fun name => Json.str name.toString)),
                  ]
              | none =>
                  if tactic.mctxAfter.getDelayedMVarAssignmentCore? mvarId |>.isSome then
                    assignments := assignments.push <| Json.mkObj [
                      ("mvar_id", mvarId.name.toString),
                      ("kind", "delayed"),
                      ("expr_pretty", Json.null),
                    ]
                  else
                    assignments := assignments.push <| Json.mkObj [
                      ("mvar_id", mvarId.name.toString),
                      ("kind", "unassigned"),
                      ("expr_pretty", Json.null),
                    ]
            let mut goalsBefore : Array Json := #[]
            for mvarId in tactic.goalsBefore do
              goalsBefore := goalsBefore.push
                (← goalStateJson ctx projectId declName tactic.mctxBefore mvarId)
            let mut goalsAfter : Array Json := #[]
            for mvarId in tactic.goalsAfter do
              goalsAfter := goalsAfter.push
                (← goalStateJson ctx projectId declName tactic.mctxAfter mvarId)
            let allUsedFVars := assignments.foldl
              (fun result assignment =>
                match assignment.getObjValAs? (Array Json) "used_fvars" with
                | .ok values => result ++ values
                | .error _ => result)
              (#[] : Array Json)
            let allUsedConsts := assignments.foldl
              (fun result assignment =>
                match assignment.getObjValAs? (Array Json) "used_consts" with
                | .ok values => result ++ values
                | .error _ => result)
              (#[] : Array Json)
            IO.println <| Json.mkObj [
              ("schema_version", "2"),
              ("record", "tactic"),
              ("project_id", projectId),
              ("module", moduleName),
              ("record_index", recordIndex),
              ("ordinal", current),
              ("syntax_kind", tactic.stx.getKind.toString),
              ("tactic_text", tacticText),
              ("range", syntaxRangeJson ctx tactic.stx),
              ("synthetic_syntax", Json.bool synthetic),
              ("elaborator", tactic.elaborator.toString),
              ("goals_before", Json.arr goalsBefore),
              ("goals_after", Json.arr goalsAfter),
              ("assignments", Json.arr assignments),
              ("used_fvars", Json.arr allUsedFVars),
              ("used_consts", Json.arr allUsedConsts),
            ] |>.compress
        | .ofTermInfo term =>
            let recordIndex ← termRecordIndex.get
            termRecordIndex.set (recordIndex + 1)
            let declName := ctx.parentDecl?.map toString |>.getD "unknown"
            let exprPretty ← exprText ctx term.lctx ctx.mctx term.expr
            let exprRaw := rawExpr term.expr
            let (fvarIds, constNames) := collectExprSymbols term.expr
            let mut usedFVars : Array Json := #[]
            for fvarId in fvarIds do
              usedFVars := usedFVars.push
                (← usedFVarJson ctx projectId declName ctx.mctx term.lctx fvarId)
            let (expected, expectedTypeId, expectedTypeRaw) ←
              match term.expectedType? with
              | some expected => do
                  let pretty ← exprText ctx term.lctx ctx.mctx expected
                  pure (
                    pretty,
                    Json.str (rawExprId projectId declName s!"term-expected-{recordIndex}" expected),
                    Json.str (rawExpr expected)
                  )
              | none => pure ("<none>", Json.null, Json.null)
            IO.println <| Json.mkObj [
              ("schema_version", "2"),
              ("record", "term"),
              ("project_id", projectId),
              ("module", moduleName),
              ("record_index", recordIndex),
              ("ordinal", current),
              ("syntax_kind", term.stx.getKind.toString),
              ("term_text", term.stx.prettyPrint.pretty),
              ("expr_pretty", exprPretty),
              ("expr_id", rawExprId projectId declName s!"term-{recordIndex}" term.expr),
              ("expr_raw", exprRaw),
              ("used_fvars", Json.arr usedFVars),
              ("used_consts", Json.arr (constNames.map fun name => Json.str name.toString)),
              ("expected_type_pretty", expected),
              ("expected_type_expr_id", expectedTypeId),
              ("expected_type_expr_raw", expectedTypeRaw),
              ("range", syntaxRangeJson ctx term.stx),
              ("synthetic_syntax", Json.bool (!term.stx.getHeadInfo matches .original ..)),
              ("is_binder", Json.bool term.isBinder),
            ] |>.compress
        | .ofMacroExpansionInfo macroInfo =>
            IO.println <| Json.mkObj [
              ("schema_version", "2"),
              ("record", "macro"),
              ("project_id", projectId),
              ("module", moduleName),
              ("ordinal", current),
              ("syntax_kind", macroInfo.stx.getKind.toString),
              ("output_kind", macroInfo.output.getKind.toString),
              ("range", syntaxRangeJson ctx macroInfo.stx),
              ("synthetic_syntax", Json.bool (!macroInfo.stx.getHeadInfo matches .original ..)),
            ] |>.compress
        | _ => pure ())
