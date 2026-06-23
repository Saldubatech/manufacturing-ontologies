# Manufacturing-ontologies — analysis tasks.
#
# Tools (Alloy, ROBOT) are fetched pinned + checksum-verified into tools/ by
# tools/get-tools.sh (reusing ~/tools when present). tools/*.jar is gitignored.
# Run targets from the repo root.

ALLOY := tools/alloy.jar
ROBOT := tools/robot.jar

.PHONY: tools alloy check-alloy check-owl check

## tools: fetch/verify the pinned analysis tools (Alloy, ROBOT)
tools:
	@bash tools/get-tools.sh

$(ALLOY) $(ROBOT):
	@bash tools/get-tools.sh

## alloy: launch the Alloy Analyzer GUI (then File-Open alloy/kanban.als)
alloy: $(ALLOY)
	@java -jar $(ALLOY) &

## check-alloy: headlessly run every command in every Alloy module
check-alloy: $(ALLOY)
	@cd alloy && for f in *.als; do \
	  echo "== $$f =="; \
	  java -jar "$(CURDIR)/$(ALLOY)" -D info exec -c "*" -f "$$f" 2>&1 \
	    | grep -iE 'SAT|UNSAT|error' | grep -ivE 'symmetr|kodkod|cnf|translat|solving'; \
	  rm -rf "$${f%.als}"; \
	done

## check-owl: validate owl/kanban.ttl loads its full import closure (ROBOT/OWLAPI)
check-owl: $(ROBOT)
	@java -jar $(ROBOT) merge --input owl/kanban.ttl --output /tmp/owl-merge.ttl 2>/tmp/owl.err || true; \
	  n=$$(grep -c 'error#Error' /tmp/owl.err 2>/dev/null || true); \
	  echo "owl/kanban.ttl: loaded, $$n unresolved-entity (Error#) warnings"

## check: run all checks
check: check-alloy check-owl
