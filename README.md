# manufacturing-ontologies

OWL specifications of manufacturing systems.

## Protégé Desktop OWL 2 template

This repository includes a starter ontology for developing OWL 2 models with
Protégé Desktop at `templates/protege/owl2-model-template.owl`.

The template provides:

- an ontology IRI and version IRI to replace in your own model
- basic ontology metadata annotations
- starter classes for manufacturing entities, processes, and resources
- example object and data properties
- example named individuals that can be renamed or removed

## How to use the template

1. Copy `templates/protege/owl2-model-template.owl` to the ontology name you
   want to develop.
2. Open the copied file in Protégé Desktop.
3. Update the ontology IRI, version IRI, and prefixes for your project.
4. Rename or remove the placeholder classes, properties, and individuals.
5. Extend the ontology with your domain axioms and save it in the syntax you
   prefer.

The template is stored as RDF/XML so it opens cleanly in Protégé Desktop and is
easy to validate with standard XML tooling.
