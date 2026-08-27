// extract-units — derive root-level fixed literals ("proven units") from a DIMACS
// CNF and emit them as unit clauses for seeding future runs (DT-024 §10 E6).
//
// Sound by construction: every emitted literal is implied by the formula at root
// level (CaDiCaL's `fixed()` API), so appending the units never changes the
// SAT/UNSAT verdict. Seeding is valid ONLY against the exact same DIMACS file
// (variable numbering must match — our CNF cache guarantees that per key).
//
// Usage: extract-units <in.cnf[.gz…]> <out.units> [conflict-budget]
//   conflict-budget 0 (default) = preprocessing only (cheap, seconds..minutes);
//   N > 0 additionally searches for N conflicts before the fixed() sweep, which
//   recovers part of the "solving-fixed" population a long run would find.
// Output: one DIMACS unit clause per line ("lit 0"). Concatenate to the original
// CNF (and bump the p-line clause count) to build the seeded formula.

#include <cstdio>
#include <cstdlib>
#include "cadical.hpp"

int main (int argc, char **argv) {
  if (argc < 3 || argc > 4) {
    fprintf (stderr, "usage: extract-units <in.cnf> <out.units> [conflict-budget]\n");
    return 2;
  }
  const char *in = argv[1], *out = argv[2];
  long budget = argc > 3 ? atol (argv[3]) : 0;

  CaDiCaL::Solver solver;
  int vars = 0;
  const char *err = solver.read_dimacs (in, vars, 1);
  if (err) { fprintf (stderr, "parse error: %s\n", err); return 1; }
  fprintf (stderr, "c parsed %d variables\n", vars);

  int res = 0;
  if (budget > 0) {
    solver.limit ("conflicts", budget);
    res = solver.solve ();          // bounded search; 0 = budget exhausted (UNKNOWN)
  } else {
    res = solver.simplify (3);      // preprocessing rounds only
  }
  fprintf (stderr, "c phase result %d (10 SAT / 20 UNSAT / 0 unknown)\n", res);
  if (res == 20) {
    fprintf (stderr, "c formula is UNSAT outright — no seeding needed, record the verdict!\n");
    return 20;
  }

  FILE *f = fopen (out, "w");
  if (!f) { perror ("open out"); return 1; }
  long n = 0;
  for (int v = 1; v <= vars; v++) {
    int fx = solver.fixed (v);      // >0: v implied true; <0: implied false; 0: open
    if (fx > 0) { fprintf (f, "%d 0\n", v);  n++; }
    else if (fx < 0) { fprintf (f, "%d 0\n", -v); n++; }
  }
  fclose (f);
  fprintf (stderr, "c extracted %ld root-fixed units of %d variables (%.2f%%)\n",
           n, vars, vars ? 100.0 * n / vars : 0.0);
  printf ("%ld\n", n);
  return res == 10 ? 10 : 0;
}
