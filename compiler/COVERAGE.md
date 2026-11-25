# Coverage of the analysis engine

Run `python3 coverage.py` from the repository root for the whole workspace, or
`python3 coverage.py -p shapelint-driver --test cargo_check_only` for a focused
suite. `-E` accepts a nextest filter expression. `--release` applies to both the
instrumented test build and report generation.

The runner uses `cargo llvm-cov nextest` with branch instrumentation using the workspace
toolchain. It cleans previous coverage artifacts before each run and keeps its build
under `target/coverage/build`. The HTML report is
`target/coverage/html/index.html`. `coverage.json` contains function, region and
branch counts. `run.json` records the test command and the test/report exit codes.
The report includes both workspace packages and excludes test and fixture source.
Production modules named `artifacts` are included.

Tests continue after a failure. Reports are still generated, and the runner
returns the failing status. A report from a failing test includes only the code
that test executed before its failure. Coverage builds are separate from native
performance measurements.
