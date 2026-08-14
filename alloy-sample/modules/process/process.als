module modules/process/process

open modules/core/core
open modules/material/material
open modules/resource/resource

/*
 * Manufacturing processes and operations. The module that demonstrates
 * multi-module composition: its relations target signatures defined in the
 * material and resource modules. Mirrors owl/modules/process/process.ttl.
 */

sig Operation extends Entity {
  usesResource:     set Resource,
  consumesMaterial: set Material,
  producesMaterial: set Material
}

sig ManufacturingProcess extends Entity {
  hasOperation: some Operation
}

-- The domain relations are specializations of core:relatesTo, so every
-- related entity is also reachable through relatesTo (analogue of the
-- rdfs:subPropertyOf core:relatesTo declarations in the OWL module).
fact DomainRelationsRefineRelatesTo {
  all o: Operation |
    o.usesResource + o.consumesMaterial + o.producesMaterial in o.relatesTo
  all p: ManufacturingProcess |
    p.hasOperation in p.relatesTo
}
