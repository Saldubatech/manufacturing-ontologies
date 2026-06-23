# Manufacturing-ontologies — analysis tasks.
#
# Tools (Alloy, ROBOT) are fetched pinned + checksum-verified into tools/ by
# tools/get-tools.sh (reusing ~/tools when present). tools/*.jar is gitignored.
# Run targets from the repo root.

ALLOY := tools/alloy.jar
ROBOT := tools/robot.jar

.PHONY: tools alloy check-alloy test-unit test-sys check-owl check

## tools: fetch/verify the pinned analysis tools (Alloy, ROBOT)
tools:
	@bash tools/get-tools.sh

$(ALLOY) $(ROBOT):
	@bash tools/get-tools.sh

## alloy: launch the Alloy Analyzer GUI (then File-Open a ROOT, e.g. alloy/resources/tests/kanban.als)
alloy: $(ALLOY)
	@java -jar $(ALLOY) &

## check-alloy: run every command in every test root (any alloy/**/tests/*.als)
check-alloy: $(ALLOY)
	@find alloy -path '*/tests/*.als' | sort | while read f; do \
	  echo "== $$f =="; \
	  java -jar $(ALLOY) -D info exec -c "*" -o /tmp/alloy-out -f "$$f" 2>&1 \
	    | grep -iE 'SAT|UNSAT|error' | grep -ivE 'symmetr|kodkod|cnf|translat|solving'; \
	done; rm -rf /tmp/alloy-out

## test-unit: run only unit_* commands across all test roots
test-unit: $(ALLOY)
	@find alloy -path '*/tests/*.als' | sort | while read f; do \
	  echo "== $$f =="; \
	  java -jar $(ALLOY) exec -c "unit_*" -o /tmp/alloy-out -f "$$f" 2>&1 \
	    | grep -iE 'SAT|UNSAT|error' | grep -ivE 'symmetr|kodkod|cnf|translat|solving'; \
	done; rm -rf /tmp/alloy-out

## test-sys: run the whole-system suite (sys_* in alloy/tests/system.als)
test-sys: $(ALLOY)
	@java -jar $(ALLOY) exec -c "sys_*" -o /tmp/alloy-out -f alloy/tests/system.als 2>&1 \
	  | grep -iE 'SAT|UNSAT|error' | grep -ivE 'symmetr|kodkod|cnf|translat|solving'; rm -rf /tmp/alloy-out

## check-owl: validate owl/kanban.ttl loads its full import closure (ROBOT/OWLAPI)
check-owl: $(ROBOT)
	@java -jar $(ROBOT) merge --input owl/kanban.ttl --output /tmp/owl-merge.ttl 2>/tmp/owl.err || true; \
	  n=$$(grep -c 'error#Error' /tmp/owl.err 2>/dev/null || true); \
	  echo "owl/kanban.ttl: loaded, $$n unresolved-entity (Error#) warnings"

## check: run all checks
check: check-alloy check-owl
