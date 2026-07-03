module reference_data/item/item_types

/*
 * ITEM — TYPES (DT-017 four-file architecture: types / contracts / implementation / mock).
 * The naked signatures, fields, and read-API of the item module: what any consumer may see.
 * NO laws here beyond field typing — the module's laws are named predicates in
 * `item_contracts.als`, asserted by `item_implementation.als` (integration) and
 * `item_mock.als` (consumer unit roots).
 *
 * Absorbs the former item.als + item_supply.als (strict renames, 2026-07-03); the UoM vocabulary
 * stays in uom.als as an INTERNAL VOCABULARY file opened here — so the arity-4 collapse root can
 * depend on it without paying this file's full cone (a DT-017 finding: types may be layered from
 * internal vocabulary files; value well-formedness like UomSchemeWF is DEFINITIONAL and rides
 * with the vocabulary, not the contract). NB a STATIC reference module has no time-indexed
 * observables to reify — its fields ARE its observables.
 */

open meta/profiles/baseline          // PROFILE (DT-012): structural — identity/refs/tenancy
open meta/kernel                     // Scoped, EntityId, resolve
open shared/values                   // Quantity, Money, Unit
open reference_data/item/uom         // UomScheme, Each, toEach, units (internal vocabulary, DT-009)
open reference_data/business_affiliate/business_affiliate   // SupplierReference (ItemSupply field type)

// ── supply sources ───────────────────────────────────────────────────────────────────────────────
/** OrderMethod — how an item is ordered from a supplier. */
enum OrderMethod {
  UNKNOWN, PURCHASE_ORDER, EMAIL, PHONE, IN_STORE, ONLINE, RFQ, PRODUCTION, TASK, THIRD_PARTY, OTHER
}

/** ItemSupply — a supply source for an Item (vendor, order method, cost, lead time);
    a child entity of Item, first-class as the target of Item.defaultSupply. */
sig ItemSupply extends Scoped {
  supplier:        one SupplierReference,
  orderMethod:     lone OrderMethod,
  orderQuantity:   lone Quantity,
  unitCost:        lone Money,
  averageLeadTime: lone Duration
}

// ── the Item ─────────────────────────────────────────────────────────────────────────────────────
/** Item — reference-data master for a material/product (the TYPE); InventoryItems and
    supply records classify against it. Tenant-scoped. */
sig Item extends Scoped {
  supplies:      set ItemSupply,   // parent → child aggregation (no backref)
  defaultSupply: lone EntityId,    // soft ref → one of this item's ItemSupply
  uom:           lone UomScheme    // present ⟺ inventory-TRACKED (DT-009); immutable (no mode change)
}

/** inventoryTracked — an Item is inventory-tracked iff it carries a UoM scheme (DT-009). */
pred inventoryTracked[i: Item] { some i.uom }

// ── definitional facts ───────────────────────────────────────────────────────────────────────────
// These DEFINE the module's shape (outgoing-ref wiring for the kernel's generic rules; the
// tight-by-default closed universe, modeling-conventions §6) — they are not promises about
// content. Laws about content live in item_contracts.als.

// Outgoing soft references (the parent→child `supplies` is a direct relation, not a soft ref).
fact ItemRefs { all i: Item | i.dataRefs = i.defaultSupply }
fact ItemSupplyRefs {
  all s: ItemSupply | s.dataRefs = s.supplier.vendorRef + s.supplier.affiliateRef
}

// Tight by default: no orphan value/handle atoms. Money/Duration/SupplierReference remain
// ItemSupply-exclusive (within this module's view). Quantity is SHARED and no-orphan-EXEMPT
// (DT-004 Q8; see modeling-conventions §6).
fact NoOrphanSupplierReference { all sr: SupplierReference | sr in ItemSupply.supplier }
fact NoOrphanItemSupplyValues {
  all m: Money    | m in ItemSupply.unitCost
  all d: Duration | d in ItemSupply.averageLeadTime
}
