module reference_data/business_affiliate/business_affiliate_types

// LOG-CARRIED since DT-023 cut 7b (MP rulings 2026-08-10; supersedes the QUASI-STATIC scope
// ruling of 2026-07-08): the BusinessAffiliate rides the subject_log spine with the SIMPLE
// reference-data lifecycle — Create -> Live, Update -> Live, Delete -> Retired (terminal).
// WHY: same resolution as the item conversion (cut 7a) — references become VERSION PINS into
// this log. The denormalized handle values (`SupplierReference` here, `CarrierReference` in
// receiving) DISSOLVE into pin + role-selector pairs on their holders: order supplier
// bindings pin at their capture writes and freeze at Submit, receiver carriers freeze with
// the captured facts, item supply rows hold vendor pins. Rename propagation dies by
// construction (pinned holders show their pinned version; floating reads read latest);
// stale-supply becomes a DERIVED reading. Runtime pin coordinate: (entityId, rId).

/*
 * BUSINESS AFFILIATE — TYPES (DT-017 four-file architecture). The naked signatures, the
 * state record, the operation kinds, the Reason taxonomy, and the read API: what any
 * consumer may see. Laws in `business_affiliate_contracts.als`; machinery in
 * `business_affiliate_implementation.als`; consumers' unit roots open the mock.
 *
 * IDENTITY vs STATE (DT-011): the affiliate's identity is bare (tenant-scoped legal entity);
 * the ROLE MEMBERSHIP is versioned state (`BusinessAffiliateState.sRoles`), folded per
 * DT-023 Q-C — a role grant/revoke IS an affiliate version. `BusinessRole` rows are
 * IMMUTABLE child entities (changing one is replacing it in the next state).
 */

open meta/profiles/domain_log        // PROFILE (DT-012): log anatomy + group/order premises
open meta/kernel                     // Scoped, EntityId, resolve
open meta/subject_log/subject_log[BusinessAffiliate, BusinessAffiliateState] as balog  // the SPINE
open reference_data/shared/lifecycle // RdStatus (RD_LIVE/RD_RETIRED) + RRetiredRef (DT-023)

// ── the role vocabulary ─────────────────────────────────────────────────────────────────────────
/** BusinessRoleType — the kind of role a business affiliate plays. */
enum BusinessRoleType { VENDOR, CUSTOMER, CARRIER, OPERATOR, OTHER }

/** BusinessRole — a role a BusinessAffiliate plays (e.g. VENDOR); an IMMUTABLE child entity
    FOLDED into the affiliate's versioned state (DT-023 Q-C) — membership is version-carried
    (`BusinessAffiliateState.sRoles`). First-class as the ROLE-SELECTOR half of a consumer's
    pin + selector pair (the dissolved-handle form). */
sig BusinessRole extends Scoped { role: one BusinessRoleType }

// No outgoing soft references (must be pinned, or `refs` is under-constrained).
fact BusinessRoleRefs { all r: BusinessRole | no r.dataRefs }

// ── the entity: IDENTITY only (log-carried, DT-011) ─────────────────────────────────────────────
/** BusinessAffiliate — a legal entity participating in a tenant's transactions (as vendor,
    customer, carrier, …). Identity is bare; the role membership and lifecycle status ride
    the log (BusinessAffiliateState records + occurrences). */
sig BusinessAffiliate extends Scoped {}

fact BusinessAffiliateRefs { all b: BusinessAffiliate | no b.dataRefs }

// ── the state record ────────────────────────────────────────────────────────────────────────────
/** BusinessAffiliateState — one moment's versioned payload of an affiliate (a value;
    extensional): the lifecycle status and the folded role membership. */
sig BusinessAffiliateState extends Snapshot {
  sStatus: one RdStatus,        // Live / Retired (DT-023 R1)
  sRoles:  set BusinessRole     // the folded children (Q-C)
}
// Value semantics: a state IS its fields.
fact BusinessAffiliateStateExtensional {
  all disj a, b: BusinessAffiliateState | a.sStatus != b.sStatus or a.sRoles != b.sRoles
}

// ── the kinds — the reference-data lifecycle (DT-023 R1) ────────────────────────────────────────
/** BaOcc — the affiliate log's occurrence family; the PIN TYPE (DT-023 R3): a version pin is
    a reference to one of these atoms (the version it created). */
abstract sig BaOcc extends balog/SubjectOcc {}

/** BaWriteOcc — the content-carrying kinds' shared payload (SET semantics): the full role
    membership each write states. */
abstract sig BaWriteOcc extends BaOcc {
  roles: set BusinessRole
} { bindings = subject + roles }

/** Create — births the BusinessAffiliate LIVE with its initial roles. */
sig CreateBaOcc extends BaWriteOcc {}
/** Update — SETs the role membership; the affiliate stays LIVE. */
sig UpdateBaOcc extends BaWriteOcc {}
/** Delete — retires the BusinessAffiliate (terminal; content carried forward for history). */
sig DeleteBaOcc extends BaOcc {} { bindings = subject }

// ── the Reason taxonomy (module-sovereign atoms; RRetiredRef is shared via lifecycle) ───────────
one sig RBaExists, RBaNotCreated, RBaRetired extends Reason {}

// ── the read API ────────────────────────────────────────────────────────────────────────────────
/** baStateAt — the affiliate's versioned content as of `t` (LOCF; none before Create). */
fun baStateAt[b: BusinessAffiliate, t: Tick]: lone BusinessAffiliateState { balog/recordAt[b, t] }
/** baVersionAt — the affiliate's CURRENT VERSION at `t`: the occurrence a new pin must
    reference (DT-023 Q-A "compatible and current"). */
fun baVersionAt[b: BusinessAffiliate, t: Tick]: lone BaOcc { balog/lastTouch[b, t] & BaOcc }
/** baLiveAt — the affiliate exists and is Live at `t` (the reference-target guard read). */
pred baLiveAt[b: BusinessAffiliate, t: Tick] { baStateAt[b, t].sStatus = RD_LIVE }
/** pinsCurrentBa — `p` is the current version of its own affiliate at `t` (pin currency). */
pred pinsCurrentBa[p: BaOcc, t: Tick] { p = baVersionAt[p.subject, t] }
/** baPinnableAt — the D2 guard in one read: `p` is current at `t` AND its version is Live —
    the version a committed introducing occurrence may pin; anything else refuses with
    `RRetiredRef` (retired-current) or is unrepresentable (stale pin). */
pred baPinnableAt[p: BaOcc, t: Tick] { pinsCurrentBa[p, t] and (p.post & BusinessAffiliateState).sStatus = RD_LIVE }

/** roleSelectorAgrees — the shared shape of every consumer's pin + role-selector pair
    (the dissolved-handle form): the selector is a role of the pinned VERSION with the
    expected type. Consumers state it over their own fields. */
pred roleSelectorAgrees[p: BaOcc, r: BusinessRole, rt: BusinessRoleType] {
  r in p.post.sRoles and r.role = rt
}
