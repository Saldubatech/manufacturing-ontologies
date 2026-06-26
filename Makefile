# Manufacturing-ontologies — analysis tasks.
#
# Tools (Alloy, ROBOT) are fetched pinned + checksum-verified into tools/ by
# tools/get-tools.sh (reusing ~/tools when present). tools/*.jar is gitignored.
# Run targets from the repo root.

ALLOY := tools/alloy.jar
ROBOT := tools/robot.jar

.PHONY: tools alloy check-alloy check-examples test-unit test-sys check

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

## check-examples: run every command in the modeling cookbook (alloy/meta/examples/*.als)
check-examples: $(ALLOY)
	@find alloy/meta/examples -name '*.als' ! -name 'ex00_*' | sort | while read f; do \
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

# NOTE: the former `check-owl` target validated the authored owl/kanban.ttl, which has been
# removed (we no longer maintain an authored ontology). ROBOT is retained (`make tools`) for
# ad-hoc consultation of the vendored public standards under owl/imports/ — see owl/README.md.

## check: run all checks
check: check-alloy check-examples
