module procurement/order/order_types

/*
 * ORDER — TYPES (DT-018; DT-017 four-file architecture). The Order is the AGREEMENT DOCUMENT at
 * the boundary of a Source station (DT-014 rung 3): it collates released demand — DemandItems —
 * into a single-supplier commitment, is negotiated through submission and (possibly WAIVED)
 * acknowledgment, and closes as material arrives through receiving. First module of the
 * procurement/ domain; the runtime rides the operations COMPONENT (component ≠ domain).
 *
 * TWO SUBJECTS on the log spine — the Order and its OrderLines (each `open` of subject_log
 * mints its OWN spine: olog and llog below are independent chaining laws and read APIs). The
 * composition is ENTITY-CARRIED ON THE CHILD (O5): a line's `orderRef` is immutable
 * identity-structure; `linesOf` is a derived read; NO record-side line set exists.
 *
 * PUBLIC OPERATION SURFACE (DT-017 L9): the 17 kinds, the Reason taxonomy, and the read API
 * live here. Laws are named predicates in order_contracts.als; machinery in
 * order_implementation.als; consumers' unit roots open order_mock.als.
 *
 * NAMING (Occ ruling (c) + flat-namespace survey): model sigs carry the `Occ` register marker;
 * product surfaces use the bare verb. Collision-dodging model names: CreateOrderOcc /
 * CancelOrderOcc / CloseOrderOcc / DeleteOrderOcc / AnnotateOrderOcc (demand owns
 * CreateDemandOcc / CancelOcc / DeleteDemandOcc in this cone; Close/Annotate take the
 * subject-qualified form for symmetry with their line twins). Statuses carry the OS_ prefix
 * (the DS_/PS_ precedent); OS_CANCELED is the en-US single-L spelling (the DS_CANCELED
 * precedent). REASONS: five atoms are REUSED from the demand vocabulary in this cone (RFrozen,
 * RBadState, RForeignRef, RNotAttached, RNotTerminal — same meaning one rung up); the
 * order-specific ones are declared below.
 *
 * MODEL SIMPLIFICATIONS (documented, not modeled — design doc §4): orderNumber (identity is the
 * atom; the number is a runtime writer policy), line rank/document ordering, currency/terms,
 * notes-as-record-fields (notes are occurrence payloads), the supplier snapshot's field-level
 * detail (an opaque atom + an overrides marker suffice for the freeze/reset laws — only the
 * NAME is first-class, because Submit's RNoSupplier and F8's "all fields but the name" need it).
 */

open meta/profiles/domain_log                        // PROFILE (DT-012): log anatomy + group/order premises
open meta/kernel                                     // Scoped, EntityId, resolve
open meta/subject_log/subject_log[Order, OrderState] as olog          // the ORDER log spine
open meta/subject_log/subject_log[OrderLine, OrderLineState] as llog  // the LINE log spine
open shared/values                                   // Quantity (+ keyed-map add/negate)
open operations/demand/demand_types                  // DemandItem + statuses + reads (TYPES only)
open reference_data/business_affiliate/business_affiliate_types      // SupplierReference [F8/O6]

// ── the status vocabulary ───────────────────────────────────────────────────────────────────────
/** OrderStatus — the FOUR stored states (O7); CONFIRMED and RECEIVING are DERIVED READINGS over
    SUBMITTED (see confirmedReadingAt / receivingReadingAt), never stored transitions. */
abstract sig OrderStatus {}
one sig OS_DRAFT, OS_SUBMITTED, OS_CLOSED, OS_CANCELED extends OrderStatus {}

/** liveOrderStatuses — the order is LIVE in these; CLOSED/CANCELED are terminal closure. */
fun liveOrderStatuses: set OrderStatus { OS_DRAFT + OS_SUBMITTED }

/** OrderLineStatus — the line's closure facet (F7: lines close ONLY by act; "short" is derived). */
abstract sig OrderLineStatus {}
one sig L_OPEN, L_CLOSED extends OrderLineStatus {}

// ── the supplier binding (F8/O6) ────────────────────────────────────────────────────────────────
/** SupplierName — the vendor's name: the ONE first-class snapshot field (Submit requires it —
    RNoSupplier; F8: the only field overrides may NOT touch). */
sig SupplierName {}
/** SupplierData — the OPAQUE snapshot/override content (field-level detail is runtime — §4). */
sig SupplierData {}
/** SupplierBinding — snapshot + typed reference + per-order overrides (F8): chooseable and
    overridable while DRAFT; `ResetToSupplier` discards `overrides`; FROZEN at Submit. The
    reference is the EXISTING SupplierReference value (O6) — both handles lone INSIDE it, so an
    unlinked, name-only supplier stays legal (PDEV-241). */
sig SupplierBinding {
  name:      lone SupplierName,      // may be the ONLY content (PDEV-241)
  reference: one  SupplierReference, // typed handles → BusinessRole(VENDOR) + BusinessAffiliate
  base:      one  SupplierData,      // the snapshot taken at choose time
  overrides: lone SupplierData       // present iff any field is overridden (F8)
}
// Value semantics: a binding IS its fields.
fact SupplierBindingExtensional {
  all disj a, b: SupplierBinding |
    a.name != b.name or a.reference != b.reference or a.base != b.base or a.overrides != b.overrides
}

// ── the confirmation facet (F3) ─────────────────────────────────────────────────────────────────
/** Disposition — the vendor's per-line answer; WAIVED = an acknowledgment recorded WITHOUT an
    explicit vendor answer (the F3 auto-confirm, trusting the user act). */
abstract sig Disposition {}
one sig DISP_ACCEPTED, DISP_CHANGED, DISP_BACKORDERED, DISP_REJECTED, DISP_SUBSTITUTED, DISP_WAIVED
  extends Disposition {}

/** Confirmation — the vendor's answer on a line (requested vs confirmed — the X12 855 lesson);
    notes ride the occurrence payload, not the record. */
sig Confirmation {
  disposition:  one  Disposition,
  confirmedQty: lone Quantity
}
fact ConfirmationExtensional {
  all disj a, b: Confirmation | a.disposition != b.disposition or a.confirmedQty != b.confirmedQty
}

// ── the entities: IDENTITY + IMMUTABLE STRUCTURE (O5) ───────────────────────────────────────────
/** Order — the agreement document. Identity only; everything mutable rides the log. (The
    orderNumber is a documented simplification — runtime writer policy, no law touches it.) */
sig Order extends Scoped {}
fact OrderRefs { all o: Order | no o.dataRefs }   // the supplier binding is RECORD-carried

/** OrderLine — a structure WITH IDENTITY (the UBL lesson): immutable parent + immutable
    optional item. A line with no item is FREE-FORM: documentary only — no demand pairing, no
    received tracking (F7 flag 3). Changing a line's item = Remove + Add (O5). */
sig OrderLine extends Scoped {
  orderRef: one  EntityId,   // → Order: the parent (lines never move — O5); entity-carried composition
  itemRef:  lone EntityId    // → Item: WHAT is ordered; absent = free-form
}
fact OrderLineRefs { all l: OrderLine | l.dataRefs = l.orderRef + l.itemRef }   // kernel isolation covers them
fact OrderLineRefIntegrity {
  all l: OrderLine {
    (let o = resolve[l.orderRef] | some o implies o in Order)
    (let i = resolve[l.itemRef]  | some i implies i in Item)
  }
}

// ── the state records ───────────────────────────────────────────────────────────────────────────
/** OrderState — one moment's mutable payload of an Order (a value; extensional). */
sig OrderState extends Snapshot {
  sStatus:   one OrderStatus,     // where the document stands (F5/O7: the stored core)
  sSupplier: one SupplierBinding  // the F8 binding (frozen at Submit)
}
fact OrderStateExtensional {
  all disj a, b: OrderState | a.sStatus != b.sStatus or a.sSupplier != b.sSupplier
}
// The binding's typed handles are RECORD-carried → tenancy/role integrity is guard-side
// (the DT-015 finding: kernel isolation reaches only entity dataRefs); typing is definitional:
fact OrderSupplierRefIntegrity {
  all s: OrderState {
    (let v = resolve[s.sSupplier.reference.vendorRef]    | some v implies v in BusinessRole)
    (let a = resolve[s.sSupplier.reference.affiliateRef] | some a implies a in BusinessAffiliate)
  }
}

/** OrderLineState — one moment's mutable payload of an OrderLine (a value; extensional). */
sig OrderLineState extends Snapshot {
  sQuantity:     lone Quantity,        // requested (buyer facet)
  sConfirmation: lone Confirmation,    // the vendor's answer (F3); none until acknowledged
  sReceived:     lone Quantity,        // STORED, incrementally maintained (F9); none = the keyed zero
  sLineStatus:   one  OrderLineStatus, // L_OPEN / L_CLOSED (closure by act — F7)
  sDemand:       set  EntityId         // → DemandItem: the serviced demand (O3: the HOLDER carries the refs)
}
fact OrderLineStateExtensional {
  all disj a, b: OrderLineState |
    a.sQuantity != b.sQuantity or a.sConfirmation != b.sConfirmation or a.sReceived != b.sReceived
    or a.sLineStatus != b.sLineStatus or a.sDemand != b.sDemand
}
// Record-carried refs are TYPED (soft — dangling allowed; tenancy is guard-side).
fact OrderLineDemandRefIntegrity {
  all s: OrderLineState | all m: s.sDemand | let d = resolve[m] | some d implies d in DemandItem
}

// ── the kinds — ORDER subject (product-register names in comments) ──────────────────────────────
/** Create — start an order (births DRAFT; seeds the supplier binding — name may be the only
    content, PDEV-241). */
sig CreateOrderOcc extends olog/SubjectOcc { supplier: one SupplierBinding }
  { bindings = subject + supplier }
/** UpdateSupplier — choose/override the supplier while composing (F8). */
sig UpdateSupplierOcc extends olog/SubjectOcc { supplier: one SupplierBinding }
  { bindings = subject + supplier }
/** ResetToSupplier — discard the per-order overrides (F8). */
sig ResetToSupplierOcc extends olog/SubjectOcc {} { bindings = subject }
/** Submit — commit: freeze + snapshot + transmit (the freeze instant — F5). C/OP call-first
    (O2): the caller drives demand.StartProduction per serviced item FIRST (demand's own service
    op carries its member-cycle legs); this commit GATES on every serviced item IN_PROCESS. */
sig SubmitOcc extends olog/SubjectOcc {} { bindings = subject }
/** Close — order done, by act (requires every live line closed). */
sig CloseOrderOcc extends olog/SubjectOcc {} { bindings = subject }
/** Cancel — abandon while composing (DRAFT-ONLY — O4: post-submission cancellation retracts
    vendor commitments; a parked seam, not a casual operation). */
sig CancelOrderOcc extends olog/SubjectOcc {} { bindings = subject }
/** Annotate — a note on the order (any live-or-terminal state; the F4 vehicle for
    out-of-system revisions; payload rides the occurrence, not the record). */
sig AnnotateOrderOcc extends olog/SubjectOcc {} { bindings = subject }
/** Delete — retire the closed order (tombstoned; lines retire with it at runtime). */
sig DeleteOrderOcc extends olog/SubjectOcc {} { bindings = subject }

// ── the kinds — LINE subject ────────────────────────────────────────────────────────────────────
/** AddLine — line genesis: from a DemandItem, from an Item, or free-form (F6). The on-the-fly
    card-less DemandItem for a naked-item line is the CALLER's demand-side Create — order-side
    this is just genesis + attach. orderRef/itemRef ride the ENTITY. */
sig AddLineOcc extends llog/SubjectOcc { qty: lone Quantity, demand: lone EntityId }
  { bindings = subject + qty + demand }
/** UpdateLine — edit the requested quantity (SET; the item is immutable — O5). */
sig UpdateLineOcc extends llog/SubjectOcc { qty: one Quantity } { bindings = subject + qty }
/** LineDemandOcc — the abstract parent of the demand-addressing line kinds (`demand` declared
    once — the MemberOcc precedent). */
abstract sig LineDemandOcc extends llog/SubjectOcc { demand: one EntityId }
/** AttachDemand — service a further DemandItem (C/OP gate order-side: item observed RELEASED,
    not held; NO demand-side operation pairs with attach — O3). */
sig AttachDemandOcc extends LineDemandOcc {} { bindings = subject + demand }
/** DetachDemand — stop servicing an item (it is simply back in the queue; pairs with nothing). */
sig DetachDemandOcc extends LineDemandOcc {} { bindings = subject + demand }
/** RemoveLine — retire a line while composing (tombstone; its demand refs drop — back in the
    queue). */
sig RemoveLineOcc extends llog/SubjectOcc {} { bindings = subject }
/** RecordAcknowledgment — the vendor's answer, or the WAIVED auto-confirm (F3). */
sig RecordAcknowledgmentOcc extends llog/SubjectOcc { confirmation: one Confirmation }
  { bindings = subject + confirmation }
/** RecordReceipt — the accrual posting (F7/F9: the C/NOTIF reaction to demand
    RecordProduction notifications; the SAME kind is the manual repair / probe re-drive).
    Incremental: sReceived += qty — pairwise, no fold anywhere. */
sig RecordReceiptOcc extends llog/SubjectOcc { qty: one Quantity } { bindings = subject + qty }
/** CloseLine — line done, BY DECREE (F7: full receipt makes closure available, never actual;
    "short" = the derived reading open ≠ 0 at the close tick). */
sig CloseLineOcc extends llog/SubjectOcc {} { bindings = subject }
/** AnnotateLine — a note on the line (any state). */
sig AnnotateLineOcc extends llog/SubjectOcc {} { bindings = subject }

/** orderCarriedSupplierRefs — the SupplierReference atoms THIS module carries: record state
    AND occurrence payloads (a refused create legally carries a binding no record ever held).
    For root-side closure facts — modeling-conventions §6, handles (MP ruling 2026-07-08). */
fun orderCarriedSupplierRefs: set SupplierReference {
  OrderState.sSupplier.reference
  + CreateOrderOcc.supplier.reference + UpdateSupplierOcc.supplier.reference
}

/** orderStructuralMutators — the ORDER-subject mutators under the F5 freeze (DRAFT-only). */
fun orderStructuralMutators: set olog/SubjectOcc { UpdateSupplierOcc + ResetToSupplierOcc }
/** lineStructuralMutators — the LINE-subject mutators under the F5 freeze (the parent order
    must be DRAFT; includes line genesis). */
fun lineStructuralMutators: set llog/SubjectOcc {
  AddLineOcc + UpdateLineOcc + AttachDemandOcc + DetachDemandOcc + RemoveLineOcc
}
/** orderOccKinds / lineOccKinds — the module families, alias-free for roots. */
fun orderOccKinds: set olog/SubjectOcc { olog/SubjectOcc }
fun lineOccKinds:  set llog/SubjectOcc { llog/SubjectOcc }

// ── refusal reasons (order-specific; five shared atoms reused from the demand vocabulary) ───────
one sig ROrderStarted,      // create: this order already has committed history (genesis-once)
        ROrderClosed,       // the order is not live (never started, or CLOSED/CANCELED/deleted)
        RLineStarted,       // add-line: this line already has committed history (genesis-once)
        RLineClosed,        // the line is unusable (never started, removed, or L_CLOSED)
        RNoLines,           // submit: no live lines
        RNoSupplier,        // submit: the supplier binding carries no name (PDEV-241 floor)
        RDemandHeld,        // attach: the demand item is already serviced by a live line (demandIndivisible)
        RDemandIneligible,  // attach/submit C/OP gate: the demand item is dangling, not live, or
                            //   not at the expected saga state (RELEASED for attach; IN_PROCESS at submit)
        RLinesOpen,         // close: a live line is still L_OPEN
        RNoDemand           // record-receipt: the line is free-form (no received tracking — F7)
        extends Reason {}

// ── the read API (per-role; L9) ─────────────────────────────────────────────────────────────────
/** oPre / oPost / lPre / lPost — an occurrence's records, TYPED (the DT-017 Snapshot
    field-name collision fix, per subject). */
fun oPre [o: olog/SubjectOcc]: lone OrderState { o.pre  & OrderState }
fun oPost[o: olog/SubjectOcc]: lone OrderState { o.post & OrderState }
fun lPre [o: llog/SubjectOcc]: lone OrderLineState { o.pre  & OrderLineState }
fun lPost[o: llog/SubjectOcc]: lone OrderLineState { o.post & OrderLineState }

/** orderStateAt / orderStatusAt — LOCF reads of the order log. */
fun orderStateAt [o: Order, t: Tick]: lone OrderState { olog/recordAt[o, t] }
fun orderStatusAt[o: Order, t: Tick]: lone OrderStatus { orderStateAt[o, t].sStatus }
/** liveOrderAt — started and in a live status (status-derived; NB the `some` conjunct — the
    demand precedent: `in` is subset, an empty read would be vacuously live). */
pred liveOrderAt[o: Order, t: Tick] {
  some s: orderStateAt[o, t] | s.sStatus in liveOrderStatuses
}
/** orderDeletedAt — the terminal order has been deleted/retired (tombstone). */
pred orderDeletedAt[o: Order, t: Tick] {
  some d: DeleteOrderOcc | committed[d] and d.subject = o and notAfter[d.tick, t]
}

/** lineStateAt / lineStatusAt — LOCF reads of the line log. */
fun lineStateAt [l: OrderLine, t: Tick]: lone OrderLineState { llog/recordAt[l, t] }
fun lineStatusAt[l: OrderLine, t: Tick]: lone OrderLineStatus { lineStateAt[l, t].sLineStatus }
/** lineRemovedAt — a committed RemoveLine tombstone exists at-or-before `t`. */
pred lineRemovedAt[l: OrderLine, t: Tick] {
  some r: RemoveLineOcc | committed[r] and r.subject = l and notAfter[r.tick, t]
}
/** startedLineAt / startedOrderAt — spine reads exported by name (module aliases are
    file-local; the sibling files and roots read through these). */
pred startedLineAt [l: OrderLine, t: Tick] { llog/startedAt[l, t] }
pred startedOrderAt[o: Order, t: Tick]     { olog/startedAt[o, t] }
/** liveLineAt — started and not removed (L_CLOSED lines are still LIVE — closure is a facet,
    removal is retirement). */
pred liveLineAt[l: OrderLine, t: Tick] { startedLineAt[l, t] and not lineRemovedAt[l, t] }

/** parentOf — the line's order (entity-carried composition, O5). */
fun parentOf[l: OrderLine]: lone Order { resolve[l.orderRef] & Order }
/** linesOf — the ENTITY composition read (no record-side line set exists — O5). */
fun linesOf[o: Order]: set OrderLine { { l: OrderLine | parentOf[l] = o } }
/** liveLinesOf — the order's live (started, unremoved) lines. */
fun liveLinesOf[o: Order, t: Tick]: set OrderLine { { l: linesOf[o] | liveLineAt[l, t] } }
/** retiredLinesOf — the removed lines (audit surface; their history stays on the log). */
fun retiredLinesOf[o: Order, t: Tick]: set OrderLine {
  { l: linesOf[o] | startedLineAt[l, t] and lineRemovedAt[l, t] }
}
/** freeForm — the line orders no Item: documentary only (F6/F7). */
pred freeForm[l: OrderLine] { no l.itemRef }

/** servicedAt — a line's serviced DemandItems, RESOLVED (soft refs may dangle out of scope). */
fun servicedAt[l: OrderLine, t: Tick]: set DemandItem {
  { d: DemandItem | some m: lineStateAt[l, t].sDemand | resolve[m] = d }
}
/** servicedOf — every DemandItem serviced by the order's LIVE lines (Submit's gate domain). */
fun servicedOf[o: Order, t: Tick]: set DemandItem {
  { d: DemandItem | some l: liveLinesOf[o, t] | d in servicedAt[l, t] }
}
/** holdingLineOf — the derived INVERSE of servicing (O3: the demand side carries no back-pointer;
    "is this item spoken for?" is THIS read). ≤1 by demandIndivisible. THE HOLD DIES WITH THE
    ORDER (scenario 6/O4: cancel — or close — returns the serviced items to the queue; no
    line-by-line choreography), hence the parent-liveness conjunct. */
fun holdingLineOf[d: DemandItem, t: Tick]: set OrderLine {
  { l: OrderLine | liveLineAt[l, t] and liveOrderAt[parentOf[l], t] and d in servicedAt[l, t] }
}

/** effectiveLineQty — confirmed-else-requested, as a keyed map (the reconciliation read). */
fun effectiveLineQty[s: OrderLineState]: Unit -> lone Scalar {
  some s.sConfirmation.confirmedQty => qtyMap[s.sConfirmation.confirmedQty] else qtyMap[s.sQuantity]
}
/** openOf — the derived open quantity: confirmed-else-requested − sReceived (pairwise; MAY go
    negative — over-receipt is admissible, the advisory stance F9). */
fun openOf[l: OrderLine, t: Tick]: Unit -> lone Scalar {
  add[effectiveLineQty[lineStateAt[l, t]], negate[qtyMap[lineStateAt[l, t].sReceived]]]
}

/** confirmedReadingAt — the O7 derived CONFIRMED reading: SUBMITTED and every live line has a
    recorded answer (incl. WAIVED). May be transient — a reading, never a transition. */
pred confirmedReadingAt[o: Order, t: Tick] {
  orderStatusAt[o, t] = OS_SUBMITTED
  all l: liveLinesOf[o, t] | some lineStateAt[l, t].sConfirmation
}
/** receivingReadingAt — the O7 derived RECEIVING reading: SUBMITTED and material has arrived
    (trumps CONFIRMED in the product's status view). */
pred receivingReadingAt[o: Order, t: Tick] {
  orderStatusAt[o, t] = OS_SUBMITTED
  some l: liveLinesOf[o, t] | some qtyMap[lineStateAt[l, t].sReceived]
}
