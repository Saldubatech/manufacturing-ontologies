# `imports/` — vendored external ontologies

External reference/upper ontologies are **vendored** here as local copies so the
project opens in Protégé without network access and pins to a known version.

## Currently vendored (full closure, 17 files)

| Ontology | Import IRI | Local file |
|---|---|---|
| BFO 2020 | `http://purl.obolibrary.org/obo/bfo/2020/bfo.owl` | `bfo.owl` |
| IOF Core | `https://spec.industrialontologies.org/ontology/core/Core/` | `iof-core.rdf` |
| IOF Annotation Vocabulary | `…/ontology/202602/core/meta/AnnotationVocabulary/` | `iof-annotation-vocabulary.rdf` |
| QUDT units | `http://qudt.org/vocab/unit` | `qudt-org-vocab-unit.ttl` |
| QUDT quantity kinds | `http://qudt.org/vocab/quantitykind` | `qudt-org-vocab-quantitykind.ttl` |
| QUDT schema + deps | `http://qudt.org/schema/qudt` (+ facade, datatype, coordinateSystems, prefix, sou, soqk, dimensionvector) | `qudt-org-*.ttl` |
| LinkedModel dtype / vaem | `http://www.linkedmodel.org/schema/{dtype,vaem}` | `www-linkedmodel-org-schema-*.rdf` |
| SKOS Core | `http://www.w3.org/2004/02/skos/core` | `www-w3-org-2004-02-skos-core.rdf` |

`.vendor-map.json` records the complete import-IRI → file mapping (used to
regenerate `../catalog-v001.xml`). Filenames other than the curated roots are
slugified from the IRI.

## Re-vendoring / adding a new external ontology

The full closure above was fetched transitively from seed IRIs (IOF Core +
QUDT unit/quantitykind) — following each file's `owl:imports` and saving every
dependency. To add another external ontology:

1. **Download** the ontology file into this directory, e.g.:

   ```bash
   # BFO 2020 (OWL)
   curl -L -o bfo.owl https://raw.githubusercontent.com/BFO-ontology/BFO-2020/master/src/owl/bfo-core.owl
   # IOF Core — see https://spec.industrialontologies.org/ for the current release artifact
   ```

2. **Map** its ontology IRI to the local file in `../catalog-v001.xml`:

   ```xml
   <uri name="http://purl.obolibrary.org/obo/bfo.owl" uri="imports/bfo.owl"/>
   ```

3. **Activate** the import in the module that aligns to it (normally
   `../modules/core/core.ttl`) by adding to its `owl:Ontology` block:

   ```turtle
   owl:imports <http://purl.obolibrary.org/obo/bfo.owl> ;
   ```

4. **Re-parent** domain classes (e.g. `core:Entity rdfs:subClassOf <bfo class>`)
   and run a reasoner in Protégé to confirm the alignment is consistent.

## Notes

- Use the ontology's **canonical IRI** as the catalog `name` — that is the IRI
  other files import, regardless of the local filename.
- Keep one upper-ontology alignment point (`core`) so the whole project shares a
  single foundational commitment.
- Record the source URL and version of each vendored file in its catalog comment
  or here, for reproducibility.
