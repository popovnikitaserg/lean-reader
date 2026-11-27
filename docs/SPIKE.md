# M0 Spike: InfoTree и proof term в Lean 4.36.0

## Среда

- Toolchain: Lean `4.36.0`, коммит `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`.
- Lake: `5.0.0-src+611c117`.
- `lean --print-prefix`: `/home/nikita/.elan/toolchains/leanprover--lean4---v4.36.0`.
- Фикстура: `tests/fixtures/m0_have_exact/`.
- Команда: `lake env lean Spike.lean`.

## Исходники и API

Проверены:

- `src/lean/Lean/Elab/Frontend.lean`;
- `src/lean/Lean/Elab/InfoTree.lean`;
- `src/lean/Lean/Elab/InfoTree/Types.lean`;
- `src/lean/Lean/Elab/InfoTree/Main.lean`;
- `src/lean/Lean/Elab/InfoTree/Util.lean`;
- `src/lean/Lean/DeclarationRange.lean`;
- `src/lean/Lean/DocString.lean`;
- `src/lean/Lean/Util/CollectAxioms.lean`;
- `src/lean/Lean/Environment.lean`;
- Lean REPL (`leanprover-community/repl`, `REPL/Frontend.lean`, `REPL/Lean/InfoTree/ToJson.lean`).

Для повторной элаборации подходит фронтенд-последовательность REPL:

1. `Parser.mkInputContext`;
2. `Parser.parseHeader`;
3. `Elab.processHeader`;
4. `IO.processCommands` с `Command.State.infoState.enabled := true`.

Для этой последовательности обязательны `Lean.initSearchPath`, `Lean.findSysroot` и
`Lean.enableInitializersExecution`; последний API запускается в spike как unsafe.

## Наблюдения

### Environment

В Environment theorem действительно имеет полноценное значение (`ConstantInfo.value? (allowOpaque := true)`).
Для fixture:

- `have_exact` хранится как `Lean.Expr.lam` с вложенным `Lean.Expr.letE`;
- `have` представляется `letE hpq` со значением `And.intro hp hq`;
- `simp` и `omega` создают конкретные доказательные термы в value theorem;
- для theorem не используется строковое описание тактик как единственный след доказательства.

Это подтверждает принцип сырых данных: и type, и value theorem должны сохраняться раздельно.

### InfoTree

`TacticInfo` содержит `stx`, `goalsBefore`, `goalsAfter`, `mctxBefore` и `mctxAfter`.
Диапазон берётся из `Syntax.getPos?`/`getTailPos?` и `ContextInfo.fileMap.toPosition`.

Прямое присвоение цели находится по `ti.mctxAfter.getExprAssignmentCore? mvarId`.
Отложенное присвоение проверяется через `getDelayedMVarAssignmentCore?`.

Реальный `have` даёт:

```text
TACTIC kind=Lean.Parser.Tactic.tacticHave__
goalsBefore=[_uniq.15]
goalsAfter=[_uniq.24]
assignment: _uniq.15 := have hpq := ⟨...⟩; ?m.4
```

`exact hpq` затем закрывает метапеременную:

```text
TACTIC kind=Lean.Parser.Tactic.exact
goalsBefore=[_uniq.24]
goalsAfter=[]
assignment: _uniq.24 := _fvar.hpq
```

В дереве есть как авторские узлы, так и синтетические wrapper-узлы (`focus`, `refine`,
`tacticSeq`, `by`, `Term.byTactic`, macro nodes). Разделение авторского синтаксиса от
синтетических узлов должно основываться на диапазоне и `Syntax.getHeadInfo`, а не только
на имени tactic kind.

### calc

Для `calc` появился узел `Lean.calcTactic`, который закрывает цель присвоением
`trans ... ...`. `Lean.calcSteps` дополнительно сохраняет диапазоны шагов цепочки.
Граф должен хранить chain как несколько claims только при наличии достаточной структуры;
иначе `status: partial`.

### simp и omega

- `simp [h]` имеет присвоение с `of_eq_true`, `Eq.trans`, `congr`, `congrArg`, `eq_true`,
  `and_self` и локальной гипотезой.
- `omega` имеет присвоение через `Decidable.byContradiction` и сгенерированную
  вспомогательную декларацию `omega_example._proof_1`.

Поэтому автоматику нельзя сводить к названию тактики: в сырых данных сохраняется полный
терм присвоения, а для графа используются non-infrastructure константы и fvars.

### first/backtracking

В fixture `first | exact hp | exact hp` в spike сохранилась только первая прошедшая ветка
`exact hp` как тактический узел; второй альтернативный узел не появился. `TacticInfo`
содержит только узлы выбранного elaboration path, но сами отменённые попытки не обязаны
быть представлены явно в этой версии.

Для будущего экспортёра:

- live-шаг определяется по присвоению и достижимости от корневой цели;
- снятые откаты не считаются live-шагами;
- при наличии отложенных либо недоказанных assignments шаг помечается `partial`;
- отменённые/недостижимые узлы должны сохраняться в raw, а в claim graph не попадать.

## Решения для следующего этапа

1. Узел proof claim строится по `TacticInfo`, а не по всем узлам дерева.
2. Тело имеет/let будет детектироваться по присвоению на один уровень и выражениям `letE`/`letFun`.
3. Сводные wrapper-узлы не являются inference: живые авторские шаги фильтруются по диапазону,
   существу присвоения и достижимости цели.
4. `calc`, `simp`, `omega` и другие автоматические тактики сначала сохраняются как raw
   `TacticInfo`/терм присвоения; heuristic-классификация выполняется уже в Python.
5. Для `mctxAfter` один уровень подстановки обязателен; рекурсивная instantiation запрещена.
