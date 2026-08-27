# unit-seeding

Harvest root-level proven units from a cached CNF and seed future solver runs
(DT-024 §10 E6). Sound: every unit is implied by the formula, so seeding never
changes the verdict; valid only against the SAME DIMACS file (variable numbering).

Build (needs a CaDiCaL checkout with `libcadical.a` built):

    c++ -O2 -std=c++17 -I<cadical>/src -o extract-units extract-units.cpp <cadical>/build/libcadical.a

Run:

    extract-units <in.cnf> <out.units> [conflict-budget]

Measured on the receiving-soak CNF (2026-08-24, 2.34M vars): budget 0
(preprocess-only) → 94,345 units in seconds; budget 100k conflicts → 186,327
units (~8% of variables) in minutes — ≈55% of what the 12h gimsatul 8t run had
proven (335,476). Seed by appending the units and bumping the p-line clause
count. For harvesting units AS A BYPRODUCT of big gimsatul runs, see DT-024 §10
E6 options: post-hoc re-derivation (this tool, zero run cost), DRAT-stream unit
filtering (native gimsatul proof output, ~10-20% overhead), or a root-trail
dump patch (zero overhead, fork maintenance).
