module resources/inventory_item/inventory_item

open meta/profiles/baseline          // PROFILE (DT-012): structural — identity/refs/tenancy
open meta/kernel                  // Entity/Scoped, EntityId, resolve, refs
open shared/values                // Quantity (minQuantity)
open reference_data/item/item     // Item — the primary classifier

/*
 * InventoryItem — a discrete, homogeneous, non-overlapping amount of goods/materials under a
 * tenant's control, classified by an Item (DT-004).
 *
 * CANONICAL = LOG-CARRIED (DT-011, 2026-07-02): this entity is IDENTITY ONLY — the immutable fields
 * that make an InventoryItem the same thing across its whole history. Its MUTABLE payload is the
 * `InventoryItemState` record (item_state.als); its behavior is the occurrence log
 * (occurrences.als: kinds, witnessed guards, `stateAt`/`liveAt` projections); its operation
 * semantics are the shared transition cores (transitions.als). There is NO `var` here — the
 * canonical module is fully static, per the single-carrier decision.
 *
 * The original Phase-B `var`/LTL carrier (var state fields + transition predicates + its three
 * suites, D1–D17 as originally verified) was preserved VERBATIM in `legacy/` and, at full parity
 * of the log suite (44/44, 2026-07-02), ARCHIVED to `../alloy-sample/inventory_item_legacy/`
 * (see its README to run it). See DT-011 and the kanban `baseline/` precedent (KC-MH-9).
 */

// ── module-local value / handle types ──────────────────────────────────────────────
/** LicensePlate — an InventoryItem's handling-unit identity (D9), distinct from `eId`;
    opaque; non-reusable, unique per tenant (we enforce global uniqueness here). Structure
    deferred (proposed topic). */
sig LicensePlate {}
/** SerialNumber — a product-instance individualizer (D10); opaque; unique within (tenant, Item).
    Presence ⇒ the item is "serialized" (all-or-nothing — an operation-level rule). */
sig SerialNumber {}
/** LotNumber — a lot/batch individualizer (D11); opaque; a state carries a SET (commingled
    provenance — not a per-unit discriminator, excluded from the cell key). */
sig LotNumber {}
/** Text — an opaque free-text value (a String); carries the AdjustProperties-editable
    descriptive attributes (notes, colorCode) on the state record. */
sig Text {}
/** Individualizer — generic placeholder for future individualizers (D3); serialNumber and
    lotNumbers are the concrete ones so far. */
sig Individualizer {}

// ── region value sets (the state record's enums; semantics in item_state.als) ────────────────
/** OperationalState — worthiness for consumption (DERIVED, D14): ENABLED vs DISABLED. */
enum OperationalState { ENABLED, DISABLED }
/** AvailabilityStatus — X.731 availability-status qualifier (DERIVED): DEGRADED. */
enum AvailabilityStatus { DEGRADED }
/** FillState — stock-fill level (D16): SEALED (operator-asserted as-intended), OPEN (working),
    EMPTY (zero; EMPTY ⟺ actual = 0 — a record fact). */
enum FillState { SEALED, OPEN, EMPTY }
/** AdministrativeState — authorization / hold (set by Lock/Unlock): UNLOCKED / LOCKED. */
enum AdministrativeState { UNLOCKED, LOCKED }

// ── the entity: IDENTITY ONLY (immutable for the item's whole existence) ─────────────────────
/** InventoryItem — the identity of a discrete amount of goods under a tenant, classified by an
    Item; its mutable payload lives on `InventoryItemState` records in the occurrence log. */
sig InventoryItem extends Scoped {
  itemRef:         one EntityId,          // → Item (required, immutable — D1/G7)
  licensePlate:    one LicensePlate,      // handling-unit identity (D9); immutable, globally unique
  serialNumber:    lone SerialNumber,     // D10 individualizer; immutable, persists (even through empty)
  minQuantity:     one Quantity,          // reorder threshold (default zero); not used by Fill
  individualizers: set Individualizer     // D3 placeholder
}

/** isSerialized — the item carries a serial number (D10). */
pred isSerialized[ii: InventoryItem] { some ii.serialNumber }

// ── structural facts (all fields immutable — plain, non-temporal) ─────────────────────────────
// Outgoing soft references: the classifier only.
fact InventoryItemRefs { all ii: InventoryItem | ii.dataRefs = ii.itemRef }

// A resolved classifier is actually an Item (dangling/cross-Universe allowed — soft ref).
fact ItemClassifierIntegrity {
  all ii: InventoryItem | let i = resolve[ii.itemRef] | some i implies i in Item
}

// D9 / G5 — license plates are unique (no two items EVER share one); non-reusability comes from the
// log's no-resurrection guard (occurrences.als) rather than a Retired axis.
fact LicensePlateUnique { all disj a, b: InventoryItem | a.licensePlate != b.licensePlate }

// D10 / G6 — a present serialNumber is unique within (tenant, Item).
fact SerialNumberUniquePerItem {
  all disj a, b: InventoryItem |
    (a.tenantId = b.tenantId and a.itemRef = b.itemRef and some a.serialNumber)
      implies a.serialNumber != b.serialNumber
}

// Tight by default — no orphan handle atoms tied to the IMMUTABLE identity. (LotNumber/Text are
// carried by state records/occurrence params, so their no-orphan rules live at the DAG sink,
// occurrences.als; Quantity/PhysicalLocator are shared value objects, orphan-EXEMPT, D8.)
fact NoOrphanLicensePlate   { all x: LicensePlate   | x in InventoryItem.licensePlate }
fact NoOrphanSerialNumber   { all x: SerialNumber   | x in InventoryItem.serialNumber }
fact NoOrphanIndividualizer { all x: Individualizer | x in InventoryItem.individualizers }
