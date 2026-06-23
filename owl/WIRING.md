# Kanban Ontology — Alignment Wiring

How `kanban.ttl` connects to the vendored reference ontologies under `imports/`.

## Import

`kanban.ttl` declares a single import:

```turtle
owl:imports <https://spec.industrialontologies.org/ontology/core/Core/>
```

IOF Core transitively imports **BFO 2020** and the **IOF Annotation Vocabulary**,
so one import brings the whole upper/mid-level stack. All resolve offline through
`catalog-v001.xml` → `imports/`. Validated with ROBOT: clean load, 0 errors,
5,731 triples in the closure.

## Namespace correction

As delivered the ontology used `iof-core:` = `…/ontology/core/Core/` and declared
local stub classes there. The vendored IOF Core publishes its classes under
`…/ontology/construct/`, so the prefix was corrected and the stubs removed:

```turtle
@prefix iof: <https://spec.industrialontologies.org/ontology/construct/> .
```

## Class alignment (applied)

| Local class | IOF/BFO superclass | Notes |
|---|---|---|
| `:Equipment`, `:Station` | `iof:MaterialResource` | exact IOF Core match |
| `:ControlArtifact` (→ `:KanbanCard`, `:Job`) | `iof:InformationContentEntity` | exact match |
| `:MaterialEntity` | `bfo:BFO_0000030` (object) | exact BFO match |
| `:Personnel` | `iof:Agent` | IOF Core has no `HumanResource`; `Agent` is the closest. Revisit if an IOF person/HR domain ontology is vendored. |
| `:Loop` | `iof:EngineeredSystem` | IOF Core has no `ManufacturingSystem`; `EngineeredSystem` is the closest Core concept. |
| `:ItemType` | `iof:DescriptiveInformationContentEntity` | IOF Core has no `ProductDesign`; a catalog/design spec is a descriptive ICE. |

The last three were substitutions: those classes do not exist in IOF Core
(Release_202602). Alternative to the substitutions: vendor an IOF *domain*
ontology that defines them.

## Not done (deferred)

- **QUDT capacity** — `:hasTheoreticalCapacityValue` / `:hasEffectiveCapacityValue`
  remain `xsd:float` with a free-text `:hasCapacityUnit` string. To use real
  units, model capacity as a QUDT quantity (`qudt:Unit` + `qudt:QuantityKind`)
  and add `owl:imports <http://qudt.org/vocab/unit>`. This re-introduces the 32
  cosmetic QUDT load warnings, so it is opt-in.

## Open modeling questions (not wiring)

- `:Station ⊑ iof:MaterialResource` — the companion describes a Station as a
  *location/space*, which in BFO is a `site` (BFO_0000029), not a material
  entity. Category mismatch worth revisiting.
- `:hasPart` (`:CompositeResource` → `:Resource`) duplicates BFO `has part`
  (BFO_0000051); consider reusing the BFO relation.

---

Copyright: (c) Arda Systems 2025-2026, All rights reserved
