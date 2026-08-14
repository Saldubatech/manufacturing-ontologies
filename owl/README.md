# `owl/` — vendored public standards (reference cache, not a maintained ontology)

This project **no longer maintains an authored OWL ontology.** The former
`kanban.ttl` + `WIRING.md` were removed; their useful content was harvested into the
workbook note **`domain-ontology/additional-info.md`** (class alignments, open issues,
and the public-standard IRIs).

What remains here is a **read-only reference cache** of the **public standard ontologies**
that stay our **source-of-truth** for modeling — consulted when grounding the Alloy
`meta/std/{bfo,iof,qudt}` boundary stubs (DT-002). We do **not** edit or re-publish them.

## Contents

```
owl/
├── catalog-v001.xml   # import-IRI → local-file map (offline resolution for Protégé/ROBOT)
└── imports/           # vendored public standards: BFO 2020, IOF Core + Annotation Vocab, full QUDT
```

See `imports/.vendor-map.json` for the IRI → file mapping, or
`domain-ontology/additional-info.md` §1 for the same table with versions.

## How to consult

- **Protégé (offline):** open any file under `imports/`; `catalog-v001.xml` resolves
  cross-imports to the local copies.
- **ROBOT (CLI):** `java -jar tools/robot.jar …` from the repo root — `extract --method MIREOT`
  to pull a boundary module, `query` for SPARQL lookups, `merge` to inspect a closure.
  `make tools` fetches ROBOT (pinned, checksum-verified).

## Posture

These standards are **references**, not a deliverable. Any **departure** from them in the
Alloy model must be **justified and documented** in the relevant decision/thread (DT-002).

---

Copyright: (c) Arda Systems 2025-2026, All rights reserved
