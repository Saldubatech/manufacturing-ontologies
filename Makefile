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

.PHONY: tools alloy check-alloy check-examples test-unit test-sys report report-examples check clean

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

## check-alloy: run every command in every test root (any alloy/**/tests/*.als); fail on expect mismatch
check-alloy: $(ALLOY)
	@mkdir -p $(OUT); fail=0; \
	for f in $$(find alloy -path '*/tests/*.als' | sort); do \
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
	for f in $$(find alloy -path '*/tests/*.als' | sort); do \
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
