module modules/resource/resource

open modules/core/core

/*
 * Resources that perform work: machines, workstations and other
 * capacity-bearing equipment. Mirrors owl/modules/resource/resource.ttl.
 */

abstract sig Resource extends Entity {}

sig Machine     extends Resource {}
sig Workstation extends Resource {}
