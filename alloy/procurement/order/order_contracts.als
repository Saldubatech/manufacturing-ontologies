module procurement/order/order_contracts

/*
 * ORDER — CONTRACTS (DT-018/DT-017). The module's laws as NAMED predicates — curated few and
 * strong, each tagged with its consistency class per the kit MATRIX (interaction kind × module
 * boundary; deployment plays no role):
 *
 *  - Order ↔ OrderLine laws are SAME-MODULE (both subjects live here) → ATOMIC invariants.
 *  - Order ↔ demand interactions are DIFFERENT-MODULE Operations → CONVERGENT/OPERATION with
 *    the CALL-FIRST saga shape (the O2/O3 rulings): the caller drives the DEMAND operation
 *    first (Submit's per-item StartProduction — demand's own service op carries its member-
 *    cycle legs down the ladder Order → Demand → Kanban); the order guard is the saga's
 *    commit gate, READING the serviced items' current states. In-flight intermediates are
 *    LEGAL (suite boundary witnesses): items IN_PROCESS under a still-DRAFT order.
 *    Attach/Detach pair with NO demand operation at all (O3: demand stays sovereign and
 *    ignorant; the gate is order-side only).
 *  - The receipt accrual is CONVERGENT/NOTIFICATION (F7: received-ness rides the DEMAND edge —
 *    demand RecordProduction notifications drive order RecordReceipt postings; the listener
 *    converges, the runtime law probe's SELF-HEAL is mandatory). Since cut 9 (MP ruling
 *    2026-08-14) the edge is BIDIRECTIONAL in effect: a demand-side Revoke/ExtractProduction
 *    drives the COMPENSATING order ReverseReceipt posting (F9b — the received quantity is
 *    financially binding, so a revoked delivery decrements it). Both directions share the one
 *    quiescence law (`receiptsSettledAt`), t-parameterized — witnessed on settled traces, NEVER
 *    a global fact (that would outlaw the legal missed-notification window).
 *
 * There is NO amendment protocol (F4), NO ScheduleLine (F2), NO order-value sum anywhere in
 * the model (F9/F10 — the denormalized-observables convention: `sReceived` is stored and
 * incrementally maintained; `open` is a pairwise derived read).
 */

open procurement/order/order_types

// ── C1 · the freeze family (F5) — ATOMIC (same-module, both subjects) ───────────────────────────
/** Structural mutators commit only while the ORDER is DRAFT (Submit is the freeze instant).
    Order-subject mutators read their own record; line-subject mutators (genesis included) read
    the PARENT order's log — same module, so the guard reads it directly. */
pred frozenOutsideDraft {
  all o: orderStructuralMutators | committed[o] implies oPre[o].sStatus = OS_DRAFT
  all o: lineStructuralMutators  | committed[o] implies
    orderStatusAt[parentOf[o.subject], o.tick] = OS_DRAFT
}

// ── C2 · demand indivisibility (F7) — ATOMIC order-side ─────────────────────────────────────────
/** A DemandItem is serviced by AT MOST ONE live line at any moment (the cycleIndivisible analog
    one rung up). Deliberately 0..1: the 0 case is load-bearing for Blind Receiving (rung 4 —
    demand items servable outside any order). */
pred demandIndivisible { all t: Tick, d: DemandItem | lone holdingLineOf[d, t] }

// ── C3 · the attach gate (F6/O3) — CONVERGENT/OPERATION, order-side only ────────────────────────
/** A committed attach saw the demand item RELEASED (it is in the order queue) and live. No
    demand-side operation pairs with it (O3: the holder carries the refs; the held module knows
    nothing). Dangling refs refuse conservatively (the guard), so committed ⇒ resolvable. */
pred attachRequiresReleased {
  all o: AttachDemandOcc | committed[o] implies
    demandStatusAt[resolve[o.demand] & DemandItem, o.tick] = DS_RELEASED
  all o: AddLineOcc | (committed[o] and some o.demand) implies
    demandStatusAt[resolve[o.demand] & DemandItem, o.tick] = DS_RELEASED
}

// ── C3b · the attach item-agreement (MP ruling 2026-07-10, PR operations#225) — ATOMIC ──────────
/** A committed demand pairing (AttachDemand, or AddLine's demand arm) is DENOMINATED in the
    line's item: the serviced DemandItem's pinned item equals the line's item IDENTITY
    (ENTITY-level — versions may differ; cut 10: the line carries identity only). Corollary: a
    FREE-FORM line (no itemRef) services NOTHING — the design's "documentary only, no demand
    pairing" (F7 flag 3) is structural, since a DemandItem always carries exactly ONE itemPin
    and the equality can never hold against an empty resolution. The guard refuses
    RDemandIneligible (wrong item, or a free-form target line). Unlike C3's status read, both
    compared fields are IMMUTABLE identity-structure, so the gate cannot go stale — no
    convergence window, no probe obligation. The invariant protects the line's own arithmetic
    (sReceived accrual, openOf, the receipts drill-down all denominate in the line's item). */
pred attachItemAgrees {
  all o: AttachDemandOcc | committed[o] implies
    (resolve[o.demand] & DemandItem).itemPin.subject = resolve[o.subject.itemRef] & Item
  all o: AddLineOcc | (committed[o] and some o.demand) implies
    (resolve[o.demand] & DemandItem).itemPin.subject = resolve[o.subject.itemRef] & Item
}

// ── C4 · the Submit gate (O2) — CONVERGENT/OPERATION, call-first ────────────────────────────────
/** A committed Submit saw EVERY serviced DemandItem at IN_PROCESS (their StartProduction — the
    saga's first legs, each internally starting its member cycles — already committed). The
    in-flight intermediate (items started, order still DRAFT) is LEGAL; convergence = retry. */
pred submitRequiresStarted {
  all o: SubmitOcc | committed[o] implies
    (all d: servicedOf[o.subject, o.tick] | demandStatusAt[d, o.tick] = DS_IN_PROCESS)
}

// ── C5 · the receipt accrual (F9) — incremental-effect theorem ──────────────────────────────────
/** A committed RecordReceipt's effect is EXACTLY sReceived += qty (pairwise — no fold anywhere;
    the denormalized-observables convention). Over-receipt is admissible; `open` may go negative. */
pred receiptAccrues {
  all o: RecordReceiptOcc | committed[o] implies
    qtyMap[lPost[o].sReceived] = add[qtyMap[lPre[o].sReceived], qtyMap[o.qty]]
}

// ── C5b · the receipt reversal (F9b, cut 9) — incremental-effect theorem ────────────────────────
/** A committed ReverseReceipt's effect is EXACTLY sReceived −= qty (pairwise — the accrual's
    compensating mirror; MP 2026-08-14: the received quantity prices the order at close, so a
    revoked delivery must come OFF it). A reversal may precede its own accrual in the missed-
    notification window (sReceived transiently negative) — the over-receipt admissibility
    stance; quiescence balances it. */
pred receiptReverses {
  all o: ReverseReceiptOcc | committed[o] implies
    qtyMap[lPost[o].sReceived] = add[qtyMap[lPre[o].sReceived], negate[qtyMap[o.qty]]]
}

// ── C6 · the receipt quiescence (F7) — CONVERGENT/NOTIFICATION, t-parameterized ─────────────────
/** receiptsSettledAt — the demand ↔ order logs are settled at `t`, BOTH directions (cut 9):
    every committed demand-side accrual (RecordProduction) on an item serviced by a live line has
    been posted to that line (a later committed RecordReceipt), and every committed demand-side
    reversal (ExtractProduction — the Revoke pairing) likewise has its compensating posting (a
    later committed ReverseReceipt). Holds at notification quiescence; legally FALSE in the
    missed/in-flight window — the runtime law probe watches it, and its MANDATORY self-heal
    (the drill-down recompute) restores it. NEVER a global fact; NOT in `guarantees`.
    NB the reversal clause quantifies over holdingLineOf AT `t` like the accrual clause: a
    revocation whose line has closed (or whose order has terminated) by `t` is OUT of the
    settled obligation — the refusal-and-ALARM posture (MP 2026-08-14), not silent convergence. */
pred receiptsSettledAt[t: Tick] {
  all rp: RecordProductionOcc |
    (committed[rp] and notAfter[rp.tick, t] and some holdingLineOf[rp.subject, t]) implies
      (some rr: RecordReceiptOcc | committed[rr] and rr.subject in holdingLineOf[rp.subject, t]
         and precedes[rp.tick, rr.tick] and notAfter[rr.tick, t])
  all xp: ExtractProductionOcc |
    (committed[xp] and notAfter[xp.tick, t] and some holdingLineOf[xp.subject, t]) implies
      (some rv: ReverseReceiptOcc | committed[rv] and rv.subject in holdingLineOf[xp.subject, t]
         and precedes[xp.tick, rv.tick] and notAfter[rv.tick, t])
}

// ── C7 · closure by act (F7) — ATOMIC ───────────────────────────────────────────────────────────
/** A line stands L_CLOSED only through a committed CloseLine — NO arithmetic transition exists
    (full receipt makes closure AVAILABLE, never actual); and closure is permanent. */
pred lineClosureByAct {
  all l: OrderLine, t: Tick | lineStatusAt[l, t] = L_CLOSED implies
    (some c: CloseLineOcc | committed[c] and c.subject = l and notAfter[c.tick, t])
  all l: OrderLine, t1, t2: Tick |
    (notAfter[t1, t2] and lineStatusAt[l, t1] = L_CLOSED) implies lineStatusAt[l, t2] = L_CLOSED
}

// ── C8 · order closure (F5) — ATOMIC ────────────────────────────────────────────────────────────
/** A committed Close saw every live line already L_CLOSED (the CloseAllShort composite is
    client-side sugar over CloseLine* + Close). */
pred closeRequiresSettled {
  all o: CloseOrderOcc | committed[o] implies
    (all l: liveLinesOf[o.subject, o.tick] | lineStatusAt[l, o.tick] = L_CLOSED)
}

// ── C9 · the supplier freeze (F8) — ATOMIC ──────────────────────────────────────────────────────
/** The binding is unchanged by every occurrence that reads a post-DRAFT record (Submit itself
    reads DRAFT and carries the binding over — the freeze instant). */
pred supplierBindingFrozen {
  all o: orderOccKinds |
    (committed[o] and some oPre[o] and oPre[o].sStatus != OS_DRAFT) implies
      oPost[o].sSupplier = oPre[o].sSupplier
}

// ── C9b · the item-descriptor pin-freeze — DISSOLVED (cut 7a), re-derived (cut 10) ─────────────
// The former `lineDescriptorFrozen` law stays dissolved, but the freeze SEMANTICS moved from
// genesis to Submit (PDEV-1536): the line stores the item IDENTITY only (`itemRef`), and the
// effective version is the read-time derivation `effectiveItemAt` — current while DRAFT, frozen
// at the parent's Submit tick after (the one retrieval-rule change). Vendor commitments stay
// repeatable/auditable — the frozen denotation is the SUBMIT-time version, which is what was
// agreed with the vendor (the genesis version was the wrong freeze whenever the item was edited
// during DRAFT). Runtime coordinate after Submit: (eId, rId).

// ── C11 · the header-detail freeze (DT-022 TQ-7, cut 6) — ATOMIC ────────────────────────────────
/** Priority, assignee, and the vendor-facing notes are unchanged by every occurrence that
    reads a post-DRAFT record (the C9 shape — Submit itself reads DRAFT and carries them
    over, the freeze instant). sInternalNotes is DELIBERATELY absent: internal notes are
    editable at any time (TQ-7(c)) — witnessed, not legislated. */
pred headerDetailFrozen {
  all o: orderOccKinds |
    (committed[o] and some oPre[o] and oPre[o].sStatus != OS_DRAFT) implies {
      oPost[o].sPriority = oPre[o].sPriority
      oPost[o].sAssignee = oPre[o].sAssignee
      oPost[o].sNotes    = oPre[o].sNotes
    }
}

// ── C10 · terminal closure (SL-4) — ATOMIC ──────────────────────────────────────────────────────
/** Once CLOSED/CANCELED, forever closed (Delete keeps the terminal record — tombstoned
    retirement). */
pred orderTerminalClosure {
  all o: Order, t1, t2: Tick |
    (notAfter[t1, t2]
       and (some s: orderStateAt[o, t1] | s.sStatus in OS_CLOSED + OS_CANCELED))
      implies orderStatusAt[o, t2] in OS_CLOSED + OS_CANCELED
}

// ── the promise ─────────────────────────────────────────────────────────────────────────────────
/** guarantees — the module's full promise: the conjunction of the published laws.
    (`receiptsSettledAt` is deliberately NOT here — t-parameterized quiescence, not an
    invariant.) */
pred guarantees {
  frozenOutsideDraft
  and demandIndivisible
  and attachRequiresReleased
  and attachItemAgrees
  and submitRequiresStarted
  and receiptAccrues
  and receiptReverses
  and lineClosureByAct
  and closeRequiresSettled
  and supplierBindingFrozen
  and headerDetailFrozen
  and orderTerminalClosure
}
