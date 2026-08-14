module modules/core/core

/*
 * Core module — the foundational signature shared by every
 * manufacturing-systems module. Alloy analogue of owl/modules/core/core.ttl
 * (the class core:Entity and the relatesTo association). Domain modules
 * `extend` Entity.
 *
 * Alloy has no upper-ontology import, so there is no BFO/IOF alignment here;
 * Entity is the local top signature.
 */

abstract sig Entity {
  -- Generic association between domain entities, specialized by the
  -- relations declared in the domain modules (see process / quantity).
  relatesTo: set Entity
}
