# lean-parser / lean2graph

`lean2graph` извлекает детерминированные графы доказательств из Lean 4 проектов.
На этапе M1 реализованы загрузка проектов, безопасное распаковывание архивов,
синтетические Lake-проекты, сборка через elan/lake и manifest отчёта.

На этапе M2 доступен Pass A: Environment-export, SQLite raw store,
Import graph и Declaration DAG в JSON/GraphML. Отчёты M2 включают V1, V3–V5 и V11.

На этапе M3 доступен Pass B: сырой InfoTree экспорт из TacticInfo, TermInfo
и MacroExpansionInfo, включая goal states и mvar assignments в SQLite.

На этапе M4 live/dead/partial шаги сопоставляются с доказательными термами;
V6 и V7 добавляют отчёты о liveness и trace coverage.

На этапе M5 theorem/lemma получают proof claim graph в JSON/GraphML.
Команда `lean2graph inspect DIR DECL` печатает гипотезы, шаги, леммы и итог.

На этапе M6 отчёт содержит V1–V13 checks (где применимо), сводные metrics,
source integrity и deterministic graph hash.

На этапе M7 доступны cache и resume:

```bash
lean2graph analyze project --out out --resume
lean2graph batch ./projects --out out --jobs 4
```

Lean/Lake workspace cache не зависит от `--out` и по умолчанию хранится в
`~/.cache/lean2graph`. Можно задать другой путь через `--cache-dir` или
`LEAN2GRAPH_CACHE_DIR`. Для архивов и git-входов там сохраняется рабочая копия
проекта вместе с `.lake`, поэтому зависимости Mathlib и Lake переиспользуются
между запусками. В Docker-режиме установленный на хосте elan/toolchain также
монтируется в контейнер.

## Установка

Требуется Python 3.11+.

```bash
python3 -m venv .venv
.venv/bin/pip install -e '.[test]'
```

Lean toolchain устанавливается через `elan`. Для сборки проекта запустите:

```bash
.venv/bin/lean2graph analyze /path/to/project --out out --scope project
```

Поддерживаемые входы:

- каталог Lean/Lake проекта;
- один `.lean` файл;
- `.zip`, `.tar.gz`, `.tgz`, `.tar`;
- git URL с опциональным `--rev`;
- каталог нескольких проектов через `lean2graph batch`.

Примеры:

```bash
lean2graph analyze ./Main.lean --out out
lean2graph analyze project.zip --out out
lean2graph analyze https://github.com/org/repo.git --out out --rev main
lean2graph batch ./projects --out out --jobs 4
lean2graph validate ./out
```

## Логи выполнения

Для вывода всех этапных событий используйте `--verbose`:

```bash
lean2graph analyze ./Main.lean --out out --verbose
```

Дополнительный файл лога задаётся через `--log-file`:

```bash
lean2graph analyze ./Main.lean --out out --verbose --log-file lean2graph.log
```

После каждого запуска также сохраняется
`out/<project_id>/reports/execution.log`.
В нем есть события загрузки входа, сборки, Pass A/B, cache hit, построения
proof graphs и завершения валидации.

## Оптимизация standalone `.lean` с Mathlib

Для повторного запуска одного файла используется persistent workspace:

```text
out/.lean-projects/project-<hash>/
```

Lake, manifest и `.lake` этого workspace переиспользуются. По умолчанию
полный cache downloader не запускается:

```bash
lean2graph analyze File.lean --out out --mathlib-cache none
```

Опция `full` скачивает cache всех Mathlib `.olean` файлов и требует много диска:

```bash
lean2graph analyze File.lean --out out --mathlib-cache full
```

Перед запуском проверяется свободное место:

```bash
lean2graph analyze File.lean --out out --required-free-gb 10
```

Для каталогов sandbox по умолчанию не используется. Для архива или git URL
по умолчанию используется Docker:

```bash
lean2graph analyze project.tar.gz --out out --sandbox docker
```

Docker-сборка запускает Lake без сети и ограничивает CPU и память. Для сборки образа
используется [Dockerfile](Dockerfile).

## Полный пример

```bash
lean2graph analyze ./MyLeanProject \
  --out ./out \
  --scope project \
  --jobs 4 \
  --timeout-module 300 \
  --timeout-decl 60

lean2graph inspect ./out MyTheorem
lean2graph validate ./out
```

## Структура вывода

```text
out/<project_id>/
  run_manifest.json
  raw/facts.sqlite
  graphs/import_graph.{json,graphml}
  graphs/declaration_dag.{json,graphml}
  graphs/proofs/<decl>.{json,graphml}
  reports/validation.{json,md}
  reports/errors.jsonl
  reports/build.log
```


## Ограничения

- Основной протестированный Lean toolchain: 4.36.0.
- На других toolchain Lean API совместимость не гарантирована.
- Declaration ranges и docstring могут быть synthetic до реализации полного CoreM API.
- Live-step и proof-term coverage являются эвристическими.
- `case_branch`, `suffices`, `calc` и сложные macro-случаи могут иметь `status: partial`.
- Отложенные metavariable assignments не должны интерпретироваться как готовое доказательство.
- `--jobs` пока влияет на batch projects, а не на независимый execution каждого Lean module.
- Docker build должен быть собран локально в [Dockerfile](Dockerfile); режим `docker`
  не доступен без Docker daemon.
