module modules/material/material

open modules/core/core

/*
 * Materials, parts and products: the things a manufacturing process consumes
 * and produces. Mirrors owl/modules/material/material.ttl.
 */

abstract sig Material extends Entity {}

sig Part    extends Material {}
sig Product extends Material {}
