module meta/values

/*
 * Universal value-object stubs for the first pass. Opaque on purpose — fields and
 * the QUDT bridge (units/quantity kinds for Money, Duration, Quantity) are deferred
 * to DT-002. They exist now only as typed slots.
 */
sig Money {}
sig Quantity {}
sig Duration {}
