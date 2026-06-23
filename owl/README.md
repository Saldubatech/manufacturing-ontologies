# Manufacturing Kanban Ontology — `owl/`

OWL ontology authored in **Turtle (`.ttl`)** and opened with **Protégé**.

## How to open

Open **`kanban.ttl`** in Protégé. `catalog-v001.xml` (same directory) maps each
imported ontology IRI to its local file under `imports/`, so the vendored
reference ontologies load offline.

## Layout

```
owl/
├── kanban.ttl              # the ontology — open/edit this
├── catalog-v001.xml        # import-IRI → local-file map (vendored externals)
└── imports/                # vendored reference ontologies (BFO 2020, IOF Core + AV, full QUDT)
```

## Content

`kanban.ttl` models pull-based shop-floor execution: Kanban cards and their
8-state lifecycle, Jobs, Stations (source/sink/processing), Resources
(atomic/composite, equipment/personnel/loop), and an ITU-T X.731 three-vector
resource state model (operational / usage / administrative). See the companion
document for the full conceptual walkthrough.

Ontology IRI: `http://manufacturing.ontology/kanban` · entity namespace
`http://manufacturing.ontology/kanban#`.

## Alignment to the vendored ontologies

The ontology is intended to align to **IOF Core** (which transitively imports
**BFO 2020**) and may use **QUDT** for capacity quantities. The vendored closure
lives under `imports/` and resolves via `catalog-v001.xml`. See
`imports/README.md` for the vendored inventory and `WIRING.md` (if present) for
the alignment plan and its status.

## Adding an external ontology

See `imports/README.md`: vendor the file under `imports/`, map its IRI in
`catalog-v001.xml`, then add an `owl:imports` to `kanban.ttl`.

---

Copyright: (c) Arda Systems 2025-2026, All rights reserved
