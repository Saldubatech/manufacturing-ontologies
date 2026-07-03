module reference_data/item/item_contracts

/*
 * ITEM — CONTRACTS (DT-017). The module's laws as NAMED predicates: everything a consumer may
 * rely on, and nothing else. types + contracts = the DOMAIN statement of this module.
 *
 * Curated deliberately small (few, strong promises — DT-017 §contract-curation): a law that is
 * true of the implementation but absent here is NOT part of the module's promise; publishing it
 * later is a compatible extension. Consumers assume these via `item_mock.als` (unit roots);
 * integration roots discharge nothing here — for a STATIC reference module the laws are axioms,
 * not theorems, so the suite's obligation is joint SATISFIABILITY (witnesses), not proof.
 */

open reference_data/item/item_types

// ── C1: supply ownership ─────────────────────────────────────────────────────────────────────────
/** Every ItemSupply belongs to exactly one Item and inherits its tenant; an Item's default
    supply, when it resolves, is one of that item's own supplies. Consumers may navigate
    Item→supplies as a strict in-tenant tree and trust defaultSupply resolution. */
pred supplyOwnership {
  all c: ItemSupply | one i: Item | c in i.supplies
  all i: Item, c: i.supplies | c.tenantId = i.tenantId
  all i: Item | let d = resolve[i.defaultSupply] | some d implies d in i.supplies
}

// ── C2: UoM schemes are owned (DT-009) ──────────────────────────────────────────────────────────
// Scheme VALUE well-formedness (each = 1.0, no zero factors) is DEFINITIONAL and lives with the
// vocabulary (uom.als `UomSchemeWF`) — consumers get it for free from the types cone; only the
// RELATIONAL law is contractual here. (DT-017 finding: bundling the two would force an owning
// Item into every scheme-consuming universe — fatal for the arity-4 collapse root. Consumers may
// also assume contract laws À LA CARTE: open item_contracts + fact { <the preds relied on> }.)

/** Every UomScheme belongs to exactly one Item (no orphan schemes). */
pred uomSchemesSound { all s: UomScheme | one i: Item | i.uom = s }

// ── C3: supplier references are sound ───────────────────────────────────────────────────────────
/** Tight by default (modeling-conventions §6): a supplier's vendor ref, when it resolves in
    scope, is a VENDOR BusinessRole; a resolved affiliate ref is a BusinessAffiliate; and when
    both resolve, the vendor role belongs to that affiliate. Dangling refs are allowed — the
    'soft' (cross-Universe) case. */
pred supplierRefsSound {
  all s: ItemSupply | let v = resolve[s.supplier.vendorRef] |
    some v implies (v in BusinessRole and v.role = VENDOR)
  all s: ItemSupply |
    let ar = resolve[s.supplier.affiliateRef], vr = resolve[s.supplier.vendorRef] {
      some ar implies ar in BusinessAffiliate
      (some vr and some ar) implies vr in ar.roles
    }
}

// ── the promise ──────────────────────────────────────────────────────────────────────────────────
/** guarantees — the module's full promise: the conjunction of the published laws. */
pred guarantees { supplyOwnership and uomSchemesSound and supplierRefsSound }
