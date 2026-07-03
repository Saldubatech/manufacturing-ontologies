# Manufacturing-ontologies — analysis tasks.
#
# Tools (Alloy, ROBOT) are fetched pinned + checksum-verified into tools/ by
# tools/get-tools.sh (reusing ~/tools when present). tools/*.jar is gitignored.
# Run targets from the repo root.

ALLOY := tools/alloy.jar
ROBOT := tools/robot.jar
# Alloy exec output (receipts + solution dumps) goes here — gitignored; never committed.
# `out/` is in .gitignore; wipe it with `make clean`.
OUT := out/alloy

.PHONY: tools alloy check-layering check-alloy check-examples test-unit test-sys report report-examples check clean

## tools: fetch/verify the pinned analysis tools (Alloy, ROBOT)
tools:
	@bash tools/get-tools.sh

$(ALLOY) $(ROBOT):
	@bash tools/get-tools.sh

## alloy: launch the Alloy Analyzer GUI (then File-Open a ROOT, e.g. alloy/resources/tests/kanban.als)
alloy: $(ALLOY)
	@java -jar $(ALLOY) &

# NOTE: commands carry `expect 1` (SAT) / `expect 0` (UNSAT); a result that does not match its
# `expect` makes the Alloy CLI return a non-zero exit. The recipes below capture that per-root exit
# code (a plain pipe would mask it) and fail the target on any mismatch — so a guard-rejection that
# silently flips to SAT, or a check that develops a counterexample, breaks the build.

## check-layering: enforce the DT-001.12 layer law — meta never opens shared; meta/shared never open a domain
DOMAIN_DIRS := system|reference_data|resources|procurement|shop_access|fulfillment|operations|receiving|shipping|oam|workflows_and_integrations
check-layering:
	@fail=0; \
	if grep -rn '^open shared/' alloy/meta --include='*.als'; then \
	  echo "FAIL: meta must not open shared (DT-001.12 layer law)"; fail=1; fi; \
	if grep -rnE '^open ($(DOMAIN_DIRS))/' alloy/meta alloy/shared --include='*.als'; then \
	  echo "FAIL: meta/shared must not open a domain (DT-001.12 layer law)"; fail=1; fi; \
	if grep -rn '^open resources/inventory_item/legacy' alloy --include='*.als' | grep -v 'alloy/resources/inventory_item/legacy/'; then \
	  echo "FAIL: only legacy/ may open legacy/ (DT-011 — the frozen var carrier is isolated)"; fail=1; fi; \
	[ $$fail -eq 0 ] && echo "OK: layering respected (meta -/-> shared -/-> domains; legacy isolated)" || exit 1

## check-alloy: run every command in every test root (any alloy/**/tests/*.als); fail on expect mismatch
check-alloy: $(ALLOY) check-layering
	@mkdir -p $(OUT); fail=0; \
	for f in $$(find alloy -path '*/tests/*.als' ! -path '*/legacy/*' | sort); do \
	  echo "== $$f =="; \
	  java -jar $(ALLOY) -D info exec -c "*" -o $(OUT) -f "$$f" > out/.run.log 2>&1 || fail=1; \
	  grep -iE 'SAT|UNSAT|error|against expectation' out/.run.log | grep -ivE 'symmetr|kodkod|cnf|translat|solving' || true; \
	done; \
	if [ $$fail -ne 0 ]; then echo "FAIL: a command did not match its expect (see 'against expectation' above)"; exit 1; fi; \
	echo "OK: all commands matched their expect"

## check-examples: run every command in the modeling cookbook (alloy/meta/examples/*.als)
check-examples: $(ALLOY)
	@mkdir -p $(OUT); fail=0; \
	for f in $$(find alloy/meta/examples -name '*.als' ! -name 'ex00_*' | sort); do \
	  echo "== $$f =="; \
	  java -jar $(ALLOY) -D info exec -c "*" -o $(OUT) -f "$$f" > out/.run.log 2>&1 || fail=1; \
	  grep -iE 'SAT|UNSAT|error|against expectation' out/.run.log | grep -ivE 'symmetr|kodkod|cnf|translat|solving' || true; \
	done; \
	if [ $$fail -ne 0 ]; then echo "FAIL: a command did not match its expect (see 'against expectation' above)"; exit 1; fi; \
	echo "OK: all commands matched their expect"

## test-unit: run only unit_* commands across all test roots
test-unit: $(ALLOY)
	@mkdir -p $(OUT); fail=0; \
	for f in $$(find alloy -path '*/tests/*.als' ! -path '*/legacy/*' | sort); do \
	  echo "== $$f =="; \
	  java -jar $(ALLOY) exec -c "unit_*" -o $(OUT) -f "$$f" > out/.run.log 2>&1 || fail=1; \
	  grep -iE 'SAT|UNSAT|error|against expectation' out/.run.log | grep -ivE 'symmetr|kodkod|cnf|translat|solving' || true; \
	done; \
	if [ $$fail -ne 0 ]; then echo "FAIL: a command did not match its expect"; exit 1; fi; \
	echo "OK: all unit_* commands matched their expect"

## test-sys: run the whole-system suite (sys_* in alloy/tests/system.als)
test-sys: $(ALLOY)
	@mkdir -p $(OUT); \
	java -jar $(ALLOY) exec -c "sys_*" -o $(OUT) -f alloy/tests/system.als > out/.run.log 2>&1; rc=$$?; \
	grep -iE 'SAT|UNSAT|error|against expectation' out/.run.log | grep -ivE 'symmetr|kodkod|cnf|translat|solving' || true; \
	if [ $$rc -ne 0 ]; then echo "FAIL: a command did not match its expect"; exit 1; fi

## profiles: per gate root, print the adopted modeling profiles (transitive open walk — DT-012)
profiles:
	@for f in $$(find alloy -path '*/tests/*.als' ! -path '*/legacy/*' | sort); do \
	  seen=""; queue="$$f"; \
	  while [ -n "$$queue" ]; do \
	    cur=$$(echo "$$queue" | head -1); queue=$$(echo "$$queue" | tail -n +2); \
	    case " $$seen " in *" $$cur "*) continue;; esac; seen="$$seen $$cur"; \
	    deps=$$(grep -E '^open [a-z]' "$$cur" 2>/dev/null | awk '{print $$2}' | sed 's|\[.*||; s|$$|.als|; s|^|alloy/|'); \
	    for d in $$deps; do [ -f "$$d" ] && queue=$$(printf '%s\n%s' "$$queue" "$$d"); done; \
	  done; \
	  profs=$$(echo "$$seen" | tr ' ' '\n' | grep 'meta/profiles/' | grep -v 'profile.als' | grep -v '/tests/' | sed 's|.*profiles/||; s|.als||' | sort -u | tr '\n' ' '); \
	  echo "$$f: $${profs:-<a la carte>}"; \
	done

## report: run every test-root command and print its LOGICAL outcome (exists/forall/forbidden, ok/mismatch)
report: $(ALLOY)
	@bash tools/alloy-report.sh

## report-examples: same, for the modeling cookbook
report-examples: $(ALLOY)
	@bash tools/alloy-report.sh --examples

# NOTE: the former `check-owl` target validated the authored owl/kanban.ttl, which has been
# removed (we no longer maintain an authored ontology). ROBOT is retained (`make tools`) for
# ad-hoc consultation of the vendored public standards under owl/imports/ — see owl/README.md.

## check: run all checks
check: check-alloy check-examples

## clean: remove generated Alloy exec output
clean:
	@rm -rf out
