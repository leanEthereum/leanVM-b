import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedPrivateSampling

/-!
# Probe-free private-boundary safety

A computation that issues no probes cannot create a private structural first fire. This supplies the signing-query case of the materialized private-boundary probability lift.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

theorem DeferredContext.Valid.addPending_of_value_none
    {context : DeferredContext} (hvalid : context.Valid)
    (coordinate : Coordinate) (candidate : Digest)
    (hvalue : context.state.values coordinate = none) :
    ({ context with state := context.state.addPending coordinate candidate } :
      DeferredContext).Valid := by
  constructor
  · exact hvalid.1
  · intro other output hother
    change context.state.values other = some output at hother
    by_cases heq : other = coordinate
    · subst other
      rw [hvalue] at hother
      contradiction
    · rw [hitAt_addPending_of_ne context.state coordinate other candidate output (Ne.symm heq)]
      exact hvalid.2 other output hother

end SphincsSecurity.Concrete.OtsProbeSimulation
