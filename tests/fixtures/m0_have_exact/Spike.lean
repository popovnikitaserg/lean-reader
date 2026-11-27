import Lean
import Lean.Elab.Frontend

open Lean Elab

def posText (ctx : ContextInfo) (stx : Syntax) : String :=
  let startPos := stx.getPos?.map ctx.fileMap.toPosition
  let endPos := stx.getTailPos?.map ctx.fileMap.toPosition
  s!"{startPos}..{endPos}"

def ppExprAfter (ctx : ContextInfo) (mctx : MetavarContext) (e : Expr) : IO String := do
  let fmt ← ctx.runMetaM {} (Meta.withMCtx mctx (Meta.ppExpr e))
  return fmt.pretty

partial def walk (tree : InfoTree) : IO Unit := do
  tree.visitM'
    (postNode := fun ctx info _ => do
      match info with
      | .ofTacticInfo ti =>
          let tacticText ← ctx.runMetaM {} (ctx.ppSyntax {} ti.stx)
          IO.println s!"TACTIC | kind={ti.stx.getKind} range={posText ctx ti.stx} text={tacticText.pretty}"
          IO.println s!"  goalsBefore={ti.goalsBefore.map (fun m => m.name.toString)}"
          IO.println s!"  goalsAfter={ti.goalsAfter.map (fun m => m.name.toString)}"
          for mvarId in ti.goalsBefore do
            match ti.mctxAfter.getExprAssignmentCore? mvarId with
            | some expr =>
                let exprText ← ppExprAfter ctx ti.mctxAfter expr
                IO.println s!"  assigned {mvarId.name} := {exprText}"
            | none =>
                if ti.mctxAfter.getDelayedMVarAssignmentCore? mvarId |>.isSome then
                  IO.println s!"  assigned {mvarId.name} := <delayed>"
                else
                  IO.println s!"  {mvarId.name} := <unassigned>"
      | .ofMacroExpansionInfo mi =>
          IO.println s!"MACRO | range={posText ctx mi.stx} outputKind={mi.output.getKind}"
      | _ => pure ())

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile "Main.lean"
  let inputCtx := Parser.mkInputContext input "Main.lean"
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  let (env, headerMessages) ← Elab.processHeader header {} headerMessages inputCtx
  let initialState := { Command.mkState env headerMessages {} with infoState.enabled := true }
  let frontendState ← IO.processCommands inputCtx parserState initialState
  let commandState := frontendState.commandState
  let messages := commandState.messages.toList
  let trees := commandState.infoState.trees.toList
  IO.println s!"MESSAGE_COUNT={messages.length} TREE_COUNT={trees.length}"
  for message in messages do
    let text ← message.toString
    IO.println s!"MESSAGE | {message.severity.toString} | {text}"
  for name in commandState.env.constants.toList.map (fun p => p.1) do
    if name.toString.startsWith "Main." || name.toString == "have_exact" then
      if let some ci := commandState.env.find? name then
        let kind :=
          match ci with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "def"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quot"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        let value := match ci.value? (allowOpaque := true) with
          | some value => s!"{repr value}"
          | none => "<none>"
        IO.println s!"DECL | {name} | {kind} | type={repr ci.type} | value={value}"
  for tree in trees do
    walk tree

#eval main
