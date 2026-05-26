# External ontology catalog

This catalog summarizes the ontology sources referenced in the pull request
discussion and provides a one-line description for each ontology or ontology
artifact that is directly available from those sources.

## Source handling notes

- **Industrial Ontologies Foundry (IOF)**, **QUDT**, and **Schema.org** publish
  ontology artifacts that can be imported directly into local ontology work.
- **LOV** is a curated catalog for discovering vocabularies, not a single
  ontology to import, so this document catalogs LOV itself as a source rather
  than attempting to inline its full vocabulary inventory.
- **Gemini** is not an ontology repository or ontology distribution endpoint.

## Industrial Ontologies Foundry (IOF)

Source:
- https://github.com/iofoundry/ontology

| Ontology | Description |
| --- | --- |
| `core/Core` | IOF Core is the common mid-level ontology that provides shared manufacturing terms and a foundation for IOF domain ontologies. |
| `core/meta/AnnotationVocabulary` | IOF Annotation Vocabulary defines annotation properties used to document IOF and related ontologies. |
| `core/commonstocoremapping/MappingCommonsToIOF` | MappingCommonsToIOF aligns OMG Commons identifier-related concepts with IOF Core for interoperability. |
| `core/commonstocoremapping/meta/MappingAnnotationVocabularyToCommons` | MappingAnnotationVocabularyToCommons maps IOF annotation terms to the OMG Commons annotation vocabulary. |
| `maintenance/Maintenance` | Maintenance is the IOF reference ontology for maintenance management, procedures, asset failure, and FMEA concepts. |
| `supplychain/SupplyChain` | SupplyChain extends IOF Core with supply-chain and logistics concepts for semantic interoperability. |
| `productionplanning/mfg-planning` | mfg-planning is listed by IOF as an in-development ontology for production planning concepts. |
| `productservicesystems/pss-ontology2` | pss-ontology2 is listed by IOF as an in-development ontology for product-service-system concepts. |

## QUDT

Source:
- https://www.qudt.org/
- https://github.com/qudt/qudt-public-repo

| Ontology | Description |
| --- | --- |
| `QUDT-all-in-one-OWL.ttl` | The all-in-one OWL distribution bundles the QUDT schema and vocabularies into a single importable Turtle file. |
| `QUDT-all-in-one-SHACL.ttl` | The all-in-one SHACL distribution bundles the QUDT graphs together for SHACL-oriented validation and modeling workflows. |
| `SCHEMA_QUDT.ttl` | SCHEMA_QUDT is the core QUDT ontology schema for quantities, units, dimensions, and related modeling constructs. |
| `SCHEMA_QUDT-DATATYPE.ttl` | SCHEMA_QUDT-DATATYPE defines the QUDT datatype layer used to describe quantity and unit datatypes. |
| `SCHEMA_QUDT-COORDINATES.ttl` | SCHEMA_QUDT-COORDINATES provides QUDT schema terms for coordinate modeling. |
| `SCHEMA-FACADE_QUDT.ttl` | SCHEMA-FACADE_QUDT provides a compact facade over parts of the broader QUDT schema. |
| `VOCAB_QUDT-CONSTANTS.ttl` | The constants vocabulary provides named physical and mathematical constants. |
| `VOCAB_QUDT-COORDINATES.ttl` | The coordinates vocabulary provides coordinate-system and coordinate-value resources. |
| `VOCAB_QUDT-UNITS-CURRENCY.ttl` | The currency vocabulary provides unit resources for currencies. |
| `VOCAB_QUDT-DIMENSION-VECTORS.ttl` | The dimension-vectors vocabulary provides reusable dimension-vector resources for dimensional analysis. |
| `VOCAB_QUDT-PREFIXES.ttl` | The prefixes vocabulary provides metric and numeric prefix resources. |
| `VOCAB_QUDT-QUANTITIES.ttl` | The quantities vocabulary provides reusable quantity resources. |
| `VOCAB_QUDT-QUANTITY-KINDS-ALL.ttl` | The quantity-kinds vocabulary provides reusable quantity-kind resources such as mass, length, or temperature. |
| `VOCAB_QUDT-SYSTEM-OF-QUANTITY-KINDS-ALL.ttl` | The systems-of-quantity-kinds vocabulary groups quantity kinds into reusable systems. |
| `VOCAB_QUDT-SYSTEM-OF-UNITS-ALL.ttl` | The systems-of-units vocabulary provides resources for systems such as SI and related unit systems. |
| `VOCAB_QUDT-DATATYPES.ttl` | The datatypes vocabulary provides reusable QUDT datatype resources. |
| `VOCAB_QUDT-UNITS-ALL.ttl` | The units vocabulary provides the reusable QUDT unit resources used across the ontology collection. |

## Schema.org

Source:
- https://schema.org/docs/schemas.html
- https://github.com/schemaorg/schemaorg

| Ontology | Description |
| --- | --- |
| `data/schema.ttl` | The main Schema.org vocabulary is published in Turtle as the primary schema file for core terms. |
| `data/ext/attic/attic.ttl` | Attic contains retired or superseded Schema.org terms kept for historical compatibility. |
| `data/ext/auto/auto.ttl` | Auto is the Schema.org hosted extension for automotive terms. |
| `data/ext/bib/bsdo-1.0.ttl` | BIB is the Schema.org hosted extension for bibliographic terms. |
| `data/ext/health-lifesci/med-health-core.ttl` | Health-Lifesci core provides the main health and life sciences extension terms. |
| `data/ext/health-lifesci/physical-activity-and-exercise.ttl` | Physical-activity-and-exercise extends the health/life-sciences area with exercise-related terms. |
| `data/ext/meta/meta.ttl` | Meta contains Schema.org meta-vocabulary terms used by the project itself. |
| `data/ext/pending/*.ttl` | Pending is a collection of issue-scoped Turtle files containing candidate Schema.org terms that are published for feedback before promotion. |

## LOV

Source:
- https://lov.linkeddata.es/dataset/lov/
- https://github.com/pyvandenbussche/lov

| Catalog entry | Description |
| --- | --- |
| `LOV` | Linked Open Vocabularies is a curated discovery catalog of hundreds of vocabularies, so users should import the original ontology they find through LOV rather than LOV itself. |

## Gemini

Source:
- https://gemini.google.com/

| Source entry | Description |
| --- | --- |
| `Gemini` | Gemini is not an ontology repository or ontology distribution endpoint, so there are no ontology artifacts to catalog from the provided URL. |
