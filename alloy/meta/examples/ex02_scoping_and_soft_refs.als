module meta/examples/ex02_scoping_and_soft_refs

/*
 * PATTERN:  Tenant scoping + soft (cross-aggregate) references + `resolve`.
 * UML:      Association realized by a foreign key; a multi-tenant partition.
 * FP:       An opaque id looked up in an environment — not a direct pointer.
 * USE WHEN:  An entity references another aggregate (possibly in another module /
 *            Universe) and tenant isolation must hold.
 * AVOID:     A hard Alloy relation across aggregate/module boundaries (it would
 *            invert the dependency DAG and bypass the isolation rule).
 * SEE ALSO:  meta/kernel.als; modeling-conventions §5; reference_data/* (real use).
 *
 * The kernel states cross-tenant isolation ONCE (over every Scoped entity's refs),
 * so this file does not repeat it — it just shows it biting.
 */

/*
  Structure at a glance — preview with the VS Code PlantUML plugin:

@startuml
hide empty members
entity Hotel <<tenant>>
entity Guest <<Scoped>>
entity Reservation <<Scoped>> {
  guestRef : EntityId
}
Reservation ..> Guest : guestRef (soft ref, resolve)
Guest --> Hotel : tenantId
Reservation --> Hotel : tenantId
note as C#white
//{ Guest.tenantId = Reservation.tenantId }//
end note
C .> (Guest, Hotel)
(Reservation, Hotel) <. C
@enduml
*/

open meta/kernel

// A Hotel is the tenant boundary; its eId is the tenantId every scoped entity carries.
sig Hotel extends Entity {}
fact HotelRefs { all h: Hotel | no h.dataRefs }

// A Guest is scoped to a hotel.
sig Guest extends Scoped {}
fact GuestRefs { all g: Guest | no g.dataRefs }

// A Reservation is scoped to a hotel and holds a SOFT reference to its Guest.
sig Reservation extends Scoped {
  guestRef: one EntityId             // → Guest (resolved with `resolve`)
}
fact ReservationRefs { all r: Reservation | r.dataRefs = r.guestRef }

// Tight by default: a tenantId resolves (if at all) to a Hotel; a resolved guest
// handle is actually a Guest. (Dangling soft refs are allowed — the cross-Universe case.)
fact TenantIsHotel    { all s: Scoped | let t = resolve[s.tenantId] | some t implies t in Hotel }
fact GuestRefIntegrity { all r: Reservation | let g = resolve[r.guestRef] | some g implies g in Guest }

// SAT: a hotel with a reservation that references a guest — all in the same tenant.
run scoping_ok {
  some h: Hotel, r: Reservation, g: Guest |
    r.tenantId = h.eId and resolve[r.guestRef] = g
} for 5

// UNSAT: a reservation cannot reference a guest in a DIFFERENT hotel
// (kernel CrossTenantIsolation forbids it — stated once, in meta/kernel).
run crossTenantGuest {
  some r: Reservation | let g = resolve[r.guestRef] |
    some g and g in Guest and g.tenantId != r.tenantId
} for 5
