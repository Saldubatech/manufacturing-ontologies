# manufacturing-ontologies

OWL specifications of manufacturing systems.

## Protégé Desktop OWL 2 template

This repository includes a starter ontology for developing OWL 2 models with
Protégé Desktop at `templates/protege/owl2-model-template.ttl`.

The template provides:

- an ontology IRI and version IRI to replace in your own model
- basic ontology metadata annotations
- starter classes for manufacturing entities, processes, and resources
- example object and data properties
- example named individuals that can be renamed or removed

## How to use the template

1. Copy `templates/protege/owl2-model-template.ttl` to the ontology name you
   want to develop.
2. Open the copied file in Protégé Desktop.
3. Update the ontology IRI, version IRI, and prefixes for your project.
4. Rename or remove the placeholder classes, properties, and individuals.
5. Extend the ontology with your domain axioms and save it in the syntax you
   prefer.

The template is stored in Turtle syntax so it opens cleanly in Protégé Desktop,
is easy to diff in version control, and can be validated with standard RDF
tooling.

## Examples of importing external ontologies

The template now includes commented examples for adding reusable ontologies in
Turtle. The following pattern can be copied into your ontology and adapted to
the vocabulary IRIs you want to reuse:

```turtle
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix iof-av: <https://spec.industrialontologies.org/ontology/annotation/> .
@prefix qudt: <http://qudt.org/schema/qudt/> .
@prefix unit: <http://qudt.org/vocab/unit/> .
@prefix schema: <https://schema.org/> .
@prefix skos: <http://www.w3.org/2004/02/skos/core#> .

<https://example.com/my-ontology>
    a owl:Ontology ;
    owl:imports
        <https://spec.industrialontologies.org/ontology/core/Core/> ,
        <https://spec.industrialontologies.org/ontology/core/meta/AnnotationVocabulary/> ,
        <http://qudt.org/2.1/schema/qudt> ,
        <http://qudt.org/2.1/vocab/unit> ,
        <https://schema.org/version/latest/schemaorg-current.ttl> ,
        <http://www.w3.org/2004/02/skos/core> ;
    iof-av:maturity iof-av:Provisional .

:ExampleAsset a schema:Thing ;
    skos:prefLabel "example asset"@en .
```

Notes for the sources mentioned in the review:

- **Industrial Ontologies Foundry (IOF)**: import the IOF ontology IRI you need,
  such as `https://spec.industrialontologies.org/ontology/core/Core/`, and add
  the corresponding prefix declarations for the symbols you will use.
- **QUDT**: import the specific QUDT vocabularies you need, commonly the schema
  plus units and quantity kinds.
- **Schema.org**: use the published Turtle release file as the import target,
  then use the `schema:` prefix in your ontology.
- **LOV**: LOV is a catalog for discovering vocabularies. Do not import LOV
  itself; import the ontology that you found through LOV, such as SKOS or FOAF.
- **Gemini**: Gemini is not an ontology distribution endpoint, so it cannot be
  added with `owl:imports`. It can still help draft terminology or mappings
  before you connect your ontology to real imported vocabularies.

For a compact markdown catalog of the referenced external sources and ontology
artifacts, see `docs/external-ontology-catalog.md`.
