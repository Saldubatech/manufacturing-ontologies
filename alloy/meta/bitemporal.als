module meta/bitemporal

/*
 * STUB — bitemporal versioning layer (DT-001.03). Worked out later. Domain modules
 * do NOT open this; only temporal test roots will. An Entity is the `subject` of
 * its versions; time coordinates carry effective + recorded later.
 */
open meta/kernel

sig TimeCoordinates {}                                   // placeholder: effective + recorded later
sig Version { subject: one Entity, coords: one TimeCoordinates }   // placeholder relation
