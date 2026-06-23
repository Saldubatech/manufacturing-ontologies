module meta/examples/ex04_type_and_instance

/*
 * PATTERN:  Type / instance — an EXTENSIBLE classification catalog vs. the physical
 *           things classified by it.
 * UML:      «type» / «instance»; a classification (powertype) association.
 * FP:       A reference into an open lookup table — not a closed sum type.
 * USE WHEN:  Categories are DATA that grows at runtime (add a kind without a code
 *            change). Contrast 07-enumerations, a CLOSED, code-level set.
 * AVOID:     Modeling an open, business-extensible classification as an Alloy enum.
 * SEE ALSO:  reference_data Item vs InventoryItem (DT-002.03); 02-scoping; 07-enumerations.
 *
 * RoomType (Suite, King, Double Queen, Single, Beach View, Patio View, …) is reference
 * data: new kinds are new ATOMS, not new code. A Room (instance) is classified by one.
 */

open meta/kernel

// The classification catalog — extensible reference data, scoped to a hotel.
sig RoomType extends Scoped {}
fact RoomTypeRefs { all rt: RoomType | no rt.dataRefs }

// A physical room is classified by exactly one RoomType (a soft reference).
sig Room extends Scoped {
  roomTypeRef: one EntityId          // → RoomType
}
fact RoomRefs { all r: Room | r.dataRefs = r.roomTypeRef }

// Tight by default: a resolved classification handle is actually a RoomType.
fact RoomTypeIntegrity {
  all r: Room | let rt = resolve[r.roomTypeRef] | some rt implies rt in RoomType
}

// SAT: a room classified by a room type in the same hotel.
run typeInstance_ok {
  some r: Room | some rt: RoomType | resolve[r.roomTypeRef] = rt
} for 5

// SAT: the catalog is EXTENSIBLE — several room types coexist (Suite, King, Beach View …).
// (This is the contrast with a closed enum: kinds are atoms you can add freely.)
run extensibleCatalog { #RoomType >= 3 } for 6

// UNSAT: a room cannot be classified by a room type from another hotel
// (kernel cross-tenant isolation).
run crossTenantType {
  some r: Room | let rt = resolve[r.roomTypeRef] |
    some rt and rt in RoomType and rt.tenantId != r.tenantId
} for 5
