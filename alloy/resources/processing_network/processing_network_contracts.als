module resources/processing_network/processing_network_contracts

/*
 * PROCESSING NETWORK — CONTRACTS (DT-017). One law for the stub: loops are well-formed routes.
 * Curated deliberately small; grows when the network model grows (source/sink purity, topology).
 */

open resources/processing_network/processing_network_types

/** A Loop's endpoints are distinct stations in the loop's own tenant — consumers may treat a
    resolved Loop as a real in-tenant route. */
pred loopWellFormed {
  all l: Loop {
    l.source != l.sink
    l.source.tenantId = l.tenantId and l.sink.tenantId = l.tenantId
  }
}

/** guarantees — the module's full promise. */
pred guarantees { loopWellFormed }
