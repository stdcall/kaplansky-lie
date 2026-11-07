# Machine settings such as LEAN_MATHLIB may be kept in a local .env file.
set dotenv-load

python := "uv run --locked python"

default: build

# Validated PDF, with cached no-op when source files have not changed.
build:
    {{python}} scripts/project.py build

# CI gate: format, lint, PDF links/layout, tests, corrections.
check:
    {{python}} scripts/project.py check

# Formatter check, source rules and the evaluated document (T000-T099).
lint:
    {{python}} scripts/project.py lint

# Format the Typst sources in place (Typstyle with the Tinymist settings).
fmt:
    {{python}} scripts/project.py fmt

# Unit tests: corrections schema, labels, bibliography, numbering, lint rules.
test:
    {{python}} scripts/project.py test

# The reader's list of corrections: build/kaplansky-lie.corrections.pdf
corrections:
    {{python}} scripts/project.py corrections

# Remove build/ and the build cache (`cache` in config/project.json).
clean:
    {{python}} scripts/project.py clean

# Exact Sage checks: every checks/sage/*.py with `sage -python`, as CI runs
# them; each script is plain Python importing sage.all (checks/README.md).
check-sage:
    sage -python scripts/check_sage.py

# Lean checks of checks/lean-proofs.json: compile, no warnings, standard
# axioms. With LEAN_MATHLIB set, against a prebuilt mathlib checkout of the
# pinned commit (nothing is built or fetched); otherwise in checks/lean after
# `lake build` there.
check-lean:
    {{python}} checks/lean/check_axioms.py

# Advisory prose check (Vale, Russian); rules in config/vale.
check-prose:
    {{python}} scripts/check_prose.py
