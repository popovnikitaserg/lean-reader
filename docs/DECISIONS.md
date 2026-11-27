# Decisions

## M0-001: Информация Lean 4.36.0

- Допустимый способ повторной элаборации: frontend sequence из Lean REPL с включённым InfoTree.
- В Environment theorem доступно значение через `ConstantInfo.value? (allowOpaque := true)`.
- Сырые Expr и MetavarContext сохраняются до нормализации.

Дата: 2026-11-18.
