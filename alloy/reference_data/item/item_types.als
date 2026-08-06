module reference_data/item/item_types

// QUASI-STATIC SCOPE (MP ruling 2026-07-08): this module is modeled IMMUTABLE because items are
// SLOW-CHANGING relative to the model's trace window — a timescale scope decision, not an
// omission. The real system's horizon (audit spans) DOES include their changes, so the
// IMPLEMENTATION MUST provide pinning semantics (record rId / as-of reads) for every frozen
// holder. Consumer freeze laws to AUDIT if this module gains a log: procurement/order
// `lineDescriptorFrozen` (PIN-covered — §7 re-basing 2026-08-05; the handle is
// `ItemDescriptorPin` below) and every consumer reading item structure
// from a frozen document. See modeling-conventions §7.

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
open reference_data/business_affiliate/business_affiliate_types   // SupplierReference (ItemSupply field type; laws via root mock/impl — DT-017)

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

/** ItemDescriptorPin — a PINNED view of an Item's descriptive data (§7 pin canon, re-based
    2026-08-05): the model-side handle for the record `rId` a frozen holder captures at its
    freeze moment. The target is QUASI-STATIC, so the pin is reified as an uninterpreted
    handle carrying its target (the Station-stub precedent) — model the PIN, not the log.
    Atoms are NOMINAL: two pins of the same Item may be distinct captured records, so there
    is deliberately NO extensional fact. Never dangles by construction (`pinOf` is a direct
    reference — the canon's "a pin never dangles"). NO orphan fact — the SupplierReference /
    DT-004 Q8 precedent for shared value sigs (per-consumer orphan facts conflict at the
    second consumer); roots pin scopes instead. */
sig ItemDescriptorPin { pinOf: one Item }

// ── definitional facts ───────────────────────────────────────────────────────────────────────────
// These DEFINE the module's shape (outgoing-ref wiring for the kernel's generic rules; the
// tight-by-default closed universe, modeling-conventions §6) — they are not promises about
// content. Laws about content live in item_contracts.als.

// Outgoing soft references (the parent→child `supplies` is a direct relation, not a soft ref).
fact ItemRefs { all i: Item | i.dataRefs = i.defaultSupply }
fact ItemSupplyRefs {
  all s: ItemSupply | s.dataRefs = s.supplier.vendorRef + s.supplier.affiliateRef
}

// Tight by default: no orphan value/handle atoms. Money/Duration remain ItemSupply-exclusive
// (within this module's view). Quantity is SHARED and no-orphan-EXEMPT (DT-004 Q8; see
// modeling-conventions §6). SupplierReference became a SHARED HANDLE at the DT-018 order
// build (2026-07-08): the former module-local NoOrphanSupplierReference fact was RETIRED
// (it forced every order-carried reference to ALSO be an item supply's supplier, where
// supplierRefsSound then outlawed the order module's wrong-role refusal witness model-wide).
// Per the §6 handle-closure REFINEMENT (MP ruling): this module EXPORTS its carrier set;
// heavy ROOTS assert the closure over their cone's carriers. Each consumer states its own
// soundness over the references it carries (item: supplierRefsSound; order: its guard).
/** itemCarriedSupplierRefs — the SupplierReference atoms THIS module carries (for root-side
    closure facts — modeling-conventions §6, handles). */
fun itemCarriedSupplierRefs: set SupplierReference { ItemSupply.supplier }
// ItemDescriptorPin is likewise SHARED and no-orphan-EXEMPT (declared above; the same Q8 /
// SupplierReference reasoning) — this module carries none itself.
fact NoOrphanItemSupplyValues {
  all m: Money    | m in ItemSupply.unitCost
  all d: Duration | d in ItemSupply.averageLeadTime
}
