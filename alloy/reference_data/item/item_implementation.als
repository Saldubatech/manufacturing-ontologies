module reference_data/item/item_implementation

/*
 * ITEM — IMPLEMENTATION (DT-017). Integration roots open this file to get the REAL module.
 *
 * Since the DT-023 cut 7a log conversion the module is NO LONGER static-degenerate: the
 * lifecycle machinery (chaining, reason-precise admission, effects) lives here, and the
 * contract's lifecycle laws are THEOREMS of it (proven in tests/item.als). The CONTENT laws
 * (ownership/refs — C1..C3) remain asserted axioms: nothing deeper derives them.
 */

open reference_data/item/item_contracts
open meta/subject_log/subject_log[Item, ItemState] as ilog   // same params ⇒ the SAME spine instance as item_types

// ── the spine adoptions ─────────────────────────────────────────────────────────────────────────
fact ItemChain { ilog/chained }
fact ItemCommitPolicy { ilog/commitAlwaysAccepts }

// ── reason-precise admission (the witnessing idiom) ─────────────────────────────────────────────
/** createItemViol — Create refuses only an already-created subject. */
fun createItemViol[o: CreateItemOcc]: set Reason { (some o.pre => RItemExists else none) }
/** itemMutateViol — Update/Delete refuse an uncreated or retired subject. */
fun itemMutateViol[o: ItemOcc]: set Reason {
  ((no o.pre) => RItemNotCreated else none)
  + ((some o.pre and o.pre.sStatus = RD_RETIRED) => RItemRetired else none)
}

fact ItemAdmissionWitnessed {
  all o: CreateItemOcc | (o.admission = Accepted iff no createItemViol[o]) and (o.admission in Rejected implies o.admission.because = createItemViol[o])
  all o: UpdateItemOcc | (o.admission = Accepted iff no itemMutateViol[o]) and (o.admission in Rejected implies o.admission.because = itemMutateViol[o])
  all o: DeleteItemOcc | (o.admission = Accepted iff no itemMutateViol[o]) and (o.admission in Rejected implies o.admission.because = itemMutateViol[o])
}

// ── effects (SET semantics on the write kinds; Delete carries content forward) ─────────────────
fact ItemEffects {
  all o: ItemWriteOcc | committed[o] implies {
    o.post.sStatus              = RD_LIVE
    o.post.sSupplies            = o.supplies
    o.post.sDefaultSupply       = o.defaultSupply
    o.post.sCardMinimumQuantity = o.cardMinimumQuantity
  }
  all o: DeleteItemOcc | committed[o] implies {
    o.post.sStatus              = RD_RETIRED
    o.post.sSupplies            = o.pre.sSupplies
    o.post.sDefaultSupply       = o.pre.sDefaultSupply
    o.post.sCardMinimumQuantity = o.pre.sCardMinimumQuantity
  }
}

// ── the content axioms (C1..C3 — see the contracts header for why these are facts) ─────────────
fact ItemContentLaws { supplyOwnership and uomSchemesSound and supplierRefsSound }
