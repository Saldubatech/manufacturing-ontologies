module resources/inventory_item/inventory_item

open meta/kernel
open meta/values               // PhysicalLocator, Quantity
open meta/x731_state/state     // OperationalState, UsageState, AdministrativeState (X.731 regions)
open reference_data/item/item       // Item — the primary classifier

/*
 * InventoryItem — a discrete amount of goods/materials under a tenant's control,
 * distinct (non-overlapping) from other InventoryItems. Tenant-scoped aggregate.
 *
 * PRIMARY CLASSIFIER: itemRef → Item — required, immutable for the item's life. Many
 * InventoryItems may share one Item (different "chunks" of the same material);
 * descriptive/shared properties (name, url, image, UoM, …) live on the Item.
 *
 * AVAILABILITY is the ITU-T X.731 tri-region model (DT-004), reusing meta/x731_state's
 * regions with INVENTORY semantics:
 *   - operational (ENABLED / DISABLED)            : fit for consumption vs spoiled/broken
 *   - usage (IDLE / ACTIVE / BUSY)                : IDLE = unopened, ACTIVE = opened/partial,
 *                                                   BUSY = depleted (nothing left to consume)
 *   - administrative (UNLOCKED / LOCKED / SHUTTING_DOWN): authorized for regular consumption
 *
 * NOTE: InventoryItem is NOT a meta/x731_state.Resource — it only reuses the region
 * state vocabularies. The standard resource interlock "DISABLED ⇒ IDLE" does NOT hold
 * here (a spoiled item may be partially consumed), so the interlocks are inventory-specific.
 *
 * Many things are still OPEN (see workbook inventory-item-model.md): the operational
 * "reason"/DEGRADED qualifier, the operational/administrative ↔ usage interlocks,
 * the "no overlap" representation, reservations & expected additions (forecast
 * quantities), a MultiQuantity algebra, and the individualizer-modeling blend.
 */

// Open-ended immutable individualizers (lot/serial/…). Generic placeholder for now;
// the named-typed vs conditional-bundle vs (key,value,type) blend is open (DT-004).
sig Individualizer {}

sig InventoryItem extends Scoped {
  // primary classifier
  itemRef:               one EntityId,          // → Item (required, immutable)
  // immutable individualizers (open-ended for now)
  individualizers:       set Individualizer,
  // availability — X.731 tri-region (one current state per region)
  operationalState:      one OperationalState,
  usageState:            one UsageState,
  administrativeState:   one AdministrativeState,
  // quantity bundle — `actual` is always present and may be zero; the rest are optional
  // pending use-case-driven constraints (min ≤ actual ≤ max?, nominal, replenishment…)
  actualQuantity:        one Quantity,
  nominalQuantity:       lone Quantity,
  minQuantity:           lone Quantity,
  maxQuantity:           lone Quantity,
  replenishmentQuantity: lone Quantity,
  initialQuantity:       lone Quantity,
  // mutable operational
  locator:               lone PhysicalLocator
}

// Outgoing soft references.
fact InventoryItemRefs { all ii: InventoryItem | ii.dataRefs = ii.itemRef }

// Tight by default: a resolved primary classifier is actually an Item. (Dangling /
// cross-Universe refs allowed — the soft-reference case.)
fact ItemClassifierIntegrity {
  all ii: InventoryItem | let i = resolve[ii.itemRef] | some i implies i in Item
}

// Interlock (proposed, DT-004 §2.5): an item is depleted (usage BUSY) exactly when its
// actual quantity is the zero MultiQuantity (an empty unit→amount map). Other interlocks
// (operational/administrative ↔ usage) remain open.
fact DepletionInterlock {
  all ii: InventoryItem | ii.usageState = BUSY iff isZero[ii.actualQuantity.byUnit]
}

// Tight by default: no orphan individualizers (a module-local handle type). Quantity
// and PhysicalLocator are SHARED value objects, hence orphan-EXEMPT (DT-004 Q8) — no
// no-orphan rule for them.
fact NoOrphanIndividualizer { all x: Individualizer | x in InventoryItem.individualizers }
