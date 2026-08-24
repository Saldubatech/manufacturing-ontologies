# decomposed-exec

Minimal driver exposing Alloy 6 / Pardinus capabilities the `exec` CLI hides
(DT-024 §9/§10): decomposed solving (`A4Options.decompose_mode` 0 off / 1 hybrid /
2 parallel, `decompose_threads`) and groundwork for headless unsat-core extraction.

Build + run:

    javac -cp ~/tools/alloy/alloy.jar -d tools/decomposed-exec tools/decomposed-exec/DecomposedExec.java
    java  -cp ~/tools/alloy/alloy.jar:tools/decomposed-exec DecomposedExec <file.als> <command> <mode> <threads> [solver]

Spike findings (2026-08-24): mode 0 and mode 1 (hybrid — batch problem raced
against the decomposed one) verified correct on a smoke model; mode 2 (pure
parallel) HANGS without a configuration partition — hypothesis: Pardinus derives
the partition from the static/variable relation split of temporal models, and our
explicit-time static models offer none. Treat mode 2 as unavailable until the
partition API is driven explicitly.
