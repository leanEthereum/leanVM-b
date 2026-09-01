import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalCoupling

/-!
# Operational global root coupling

The adaptive induction in this file has a deliberately small successful postcondition. Source
chronology and comparison observation tracking are unary support invariants, so the two-run kernel
only carries snapshot alignment and the final value at a retained private witness.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def SnapshotObservedValueRel
    (table : OtsSecretIndex → HashOutput)
    (source : PrivateWitnessSnapshotOutput)
    (observed : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))) : Prop :=
  observed = none ∨
    ∃ result, observed = some result ∧
      SnapshotsObservedAt table source.2 result.observations ∧
      ∀ witness, source.1 = some witness →
        result.state.values (.position witness.position) = some witness.output

theorem SnapshotObservedValueRel.to_rootRel
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {observed : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))}
    (hrelation : SnapshotObservedValueRel table source observed)
    (hsource : SourceSnapshotStopInvariant source)
    (htracked : ∀ result, observed = some result →
      CleanProbeObservationsTrackedBy result.observations result.state) :
    SnapshotObservedRootRel source observed := by
  rcases hrelation with hfailed | ⟨result, hresult, haligned, hstored⟩
  · exact Or.inl hfailed
  · right
    intro hfirst
    subst observed
    exact witnessFirstUsesSomeDelayedLayerRootSnapshot_of_aligned_tracked_sourceInvariant
      hsource haligned hfirst (htracked result rfl) (by
        intro witness hwitness
        exact hstored witness (by simpa [erasePrivateWitnessSnapshotOutput] using hwitness))

theorem relTriple_snapshotObservedRoot_of_valueRel
    {table : OtsSecretIndex → HashOutput}
    {source : ProbComp PrivateWitnessSnapshotOutput}
    {observed : ProbComp (Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)))}
    (hrelation : RelTriple source observed (SnapshotObservedValueRel table))
    (hsource : ∀ output ∈ support source, SourceSnapshotStopInvariant output)
    (htracked : ∀ output ∈ support observed, ∀ result, output = some result →
      CleanProbeObservationsTrackedBy result.observations result.state) :
    RelTriple source observed SnapshotObservedRootRel := by
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hrelation
      SourceSnapshotStopInvariant hsource
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro left right hfacts
  exact hfacts.1.1.to_rootRel hfacts.1.2 fun result hresult =>
    htracked right hfacts.2 result hresult

end SphincsSecurity.Concrete.OtsProbeSimulation
