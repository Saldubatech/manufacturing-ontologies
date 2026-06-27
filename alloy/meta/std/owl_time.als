module meta/std/owl_time

/*
 * STUB — vendored OWL-Time (W3C Time Ontology, http://www.w3.org/2006/time#) boundary terms
 * (MIREOT). Only the terms our meta/time entities touch, each tagged with its source IRI. Empty for
 * now; populated per DT-002. The public OWL-Time standard (cached read-only at
 * ../../../owl/imports/www-w3-org-2006-time.ttl) is the source-of-truth; departures are documented.
 *
 * Term mapping (meta/time → OWL-Time):
 *   Instant       → time:Instant             (http://www.w3.org/2006/time#Instant)
 *   TimeInterval  → time:ProperInterval      (#ProperInterval; #hasBeginning / #hasEnd → Instant)
 *   Duration      → time:Duration            (#Duration / #TemporalDuration)
 *   PeriodUnit    → time:TemporalUnit individuals: time:unitHour / time:unitDay / time:unitWeek
 *                                            (#unitHour, #unitDay, #unitWeek; MONTH/YEAR deferred)
 *   TimeZone      → time:TimeZone             (#TimeZone; #timeZone / #inTimeZone)
 *   atOrBefore    → time:before / time:after  (#before, #after) — point order
 *   (interval rel)→ time:intervalMeets/During/Starts/Finishes/Overlaps/Equals (Allen relations)
 *   endOfPeriod   → no direct term: a period close is a TRS (time:TRS) computation over
 *                   time:DateTimeDescription; we characterize it ABSTRACTLY (laws only) until the
 *                   real clock lands (DT-001.03).
 *
 * Upper grounding: time:Instant ⊑ BFO zero-dimensional temporal region; time:Interval ⊑
 *   one-dimensional temporal region (IOF defers temporal modeling to BFO + OWL-Time).
 * Lexical layer: ISO 8601 / xsd:dateTimeStamp (requires a zone offset), xsd:duration (P1D/PT1H/P1W).
 * Concrete zones: the IANA tz database (e.g. "Europe/Madrid") fills time:TimeZone.
 *
 * DEPARTURE NOTE: meta/time models the period close as an abstract, axiomatized function
 * (at/after + idempotent + monotone), NOT OWL-Time's description-based calendar arithmetic — a
 * deliberate simplification pending the TRS/clock (DT-001.03), justified here per DT-002.
 */
