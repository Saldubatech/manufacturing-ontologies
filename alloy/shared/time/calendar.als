module shared/time/calendar

/*
 * CALENDARING — the REAL-WORLD time vocabulary (DT-001.12 earmark, fulfilled 2026-07-02): standard
 * period units and time zones, binding the ABSTRACT period machinery (`meta/time/time.PeriodSpec`)
 * to the world. Future tenant time-zones, standard durations (DAY/WEEK), `endOfDay` land here.
 *
 * Grounded on W3C OWL-Time: PeriodUnit ~ time:TemporalUnit individuals; TimeZone ~ time:TimeZone.
 * The actual calendar arithmetic (which Instant IS a day boundary in a zone) is a time:TRS / clock
 * concern (DT-001.03) — abstract laws only. See shared/std/owl_time for the MIREOT mapping.
 */

open meta/time/time               // the abstract PeriodSpec/endOfPeriod/samePeriod/calendarAxioms + axis

/** PeriodUnit — a standard calculation-period length (OWL-Time time:unitHour/unitDay/unitWeek).
    MONTH/YEAR (variable length) deferred. */
enum PeriodUnit { HOUR, DAY, WEEK }

/** TimeZone — a named time zone (opaque; an IANA tz name). Day/week boundaries are zone-relative,
    so the real-world period spec carries one. */
sig TimeZone {}

/** CalendarSpec — a PeriodSpec BOUND to the real world: this unit, in this zone. */
sig CalendarSpec extends PeriodSpec {
  unit: one PeriodUnit,
  zone: one TimeZone
}
/** At most one calendar spec per (unit, zone). */
fact OneSpecPerUnitZone { all disj p, q: CalendarSpec | p.unit != q.unit or p.zone != q.zone }

/** specFor — the calendar spec for a (unit, zone), if one exists. */
fun specFor[u: PeriodUnit, z: TimeZone]: lone CalendarSpec {
  { p: CalendarSpec | p.unit = u and p.zone = z }
}
