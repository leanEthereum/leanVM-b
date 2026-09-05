import SphincsSecurity.Proof.OtsProbeLiveJointCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeProbeCutAt (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    Nat → OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α) :=
  OracleComp.construct (fun value _ => pure (.done value))
    (fun input next recursivelyCut ordinal =>
      if LazyRevealProbe.IsProbe input then
        match ordinal with
        | 0 => pure (.query input next)
        | ordinal + 1 => (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun output => recursivelyCut output ordinal
      else (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun output => recursivelyCut output ordinal) computation

theorem nativeProbeCutAt_query_bind
    (input : (LazyRevealProbe.World Coordinate).Domain)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α) (ordinal : Nat) :
    nativeProbeCutAt ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) ordinal =
      (if LazyRevealProbe.IsProbe input then
        match ordinal with
        | 0 => pure (.query input next)
        | ordinal + 1 => (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun output => nativeProbeCutAt (next output) ordinal
      else (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun output => nativeProbeCutAt (next output) ordinal) := rfl

theorem nativeProbeCutAt_resume (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (ordinal : Nat) :
    nativeProbeCutAt computation ordinal >>= PrivateValueCut.resume = computation := by
  induction computation using OracleComp.inductionOn generalizing ordinal with
  | pure value => rfl
  | query_bind input next ih =>
      rw [nativeProbeCutAt_query_bind]
      split_ifs
      · cases ordinal with
        | zero => rfl
        | succ ordinal =>
            rw [bind_assoc]
            exact bind_congr fun output => ih output ordinal
      · rw [bind_assoc]
        exact bind_congr fun output => ih output ordinal

theorem nativeProbeCutAt_probeBound (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (ordinal : Nat) :
    (nativeProbeCutAt computation ordinal).IsQueryBoundP LazyRevealProbe.IsProbe ordinal := by
  induction computation using OracleComp.inductionOn generalizing ordinal with
  | pure value => simp [nativeProbeCutAt]
  | query_bind input next ih =>
      rw [nativeProbeCutAt_query_bind]
      by_cases hprobe : LazyRevealProbe.IsProbe input
      · rw [if_pos hprobe]
        cases ordinal with
        | zero => simp
        | succ ordinal =>
            rw [OracleComp.isQueryBoundP_query_bind_iff]
            exact ⟨Or.inr (by omega), fun output => by simpa only [if_pos hprobe, Nat.add_sub_cancel] using ih output ordinal⟩
      · rw [if_neg hprobe, OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl hprobe, fun output => by simpa only [if_neg hprobe] using ih output ordinal⟩

def nativeCutCandidate (_context : DeferredContext) : PrivateValueCut α → Option Probe
  | .query (.probe coordinate digest) _ => some ⟨coordinate, digest⟩
  | _ => none

noncomputable def sampledNativeProbeCut
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel ordinal : Nat) :
    ProbComp (Option (ResolvedRunResult (PrivateValueCut α))) := do
  let table ← sampleOtsHashTable
  runResolvedFromTable { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel table (nativeProbeCutAt computation ordinal)

theorem probEvent_sampledNativeProbeCut_unresolvedStart_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel ordinal : Nat)
    (hordinal : ordinal ≤ 2 ^ 126) :
    Pr[LiveUnresolvedStartHit nativeCutCandidate | sampledNativeProbeCut computation fuel ordinal] ≤
      (∑' result, Pr[= result | sampledNativeProbeCut computation fuel ordinal] *
        historyUnresolvedStartCharge nativeCutCandidate (retainCompletableResult result)) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [probEvent_liveUnresolvedStartHit_eq_expected]
  exact expected_live_sampled_runResolved_empty_unresolvedStart_le (nativeProbeCutAt computation ordinal)
    fuel ordinal nativeCutCandidate (nativeProbeCutAt_probeBound computation ordinal) hordinal

theorem sum_sampledNativeProbeCut_unresolvedStart_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel q : Nat)
    (hq : q ≤ 2 ^ 126) :
    (∑ ordinal ∈ Finset.range q,
      Pr[LiveUnresolvedStartHit nativeCutCandidate | sampledNativeProbeCut computation fuel ordinal]) ≤
      (∑ ordinal ∈ Finset.range q, ∑' result,
        Pr[= result | sampledNativeProbeCut computation fuel ordinal] *
          historyUnresolvedStartCharge nativeCutCandidate (retainCompletableResult result)) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  calc
    _ ≤ ∑ ordinal ∈ Finset.range q,
        (∑' result, Pr[= result | sampledNativeProbeCut computation fuel ordinal] *
          historyUnresolvedStartCharge nativeCutCandidate (retainCompletableResult result)) *
          ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
      apply Finset.sum_le_sum
      intro ordinal hmem
      exact probEvent_sampledNativeProbeCut_unresolvedStart_le computation fuel ordinal
        ((Nat.le_of_lt (Finset.mem_range.mp hmem)).trans hq)
    _ = _ := (Finset.sum_mul _ _ _).symm

end SphincsSecurity.Concrete.OtsProbeSimulation
