import SphincsSecurity.Proof.OtsProbeNativeCandidateRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def privateProbeInputAllowance (target : Position) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) : LazyRevealProbe.Query Coordinate → ENNReal
  | .probe coordinate digest => if coordinate = .position target then
      candidateFailureAllowance table context (some ⟨coordinate, digest⟩) else 0
  | _ => 0

theorem privateProbeInputAllowance_of_not_probe
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (input : LazyRevealProbe.Query Coordinate) (hprobe : ¬IsPrivatePositionProbe target input) :
    privateProbeInputAllowance target table context input = 0 := by
  cases input <;> simp_all [privateProbeInputAllowance, IsPrivatePositionProbe]

noncomputable def privateLiveProbeAllowance
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ => 0)
    (fun input _ next context fuel table =>
      if DeferredCompletable table context then
        if IsPrivatePositionDisclosure target input then 0
        else privateProbeInputAllowance target table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
            match result with
            | none => 0
            | some result => next result.value result.context result.remaining result.table
      else 0) computation

noncomputable def privateLiveProbeOrdinalAllowance
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    Nat → DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next ordinal context fuel table =>
      if DeferredCompletable table context then
        if IsPrivatePositionDisclosure target input then 0
        else if IsPrivatePositionProbe target input ∧ ordinal = 0 then privateProbeInputAllowance target table context input
        else ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
          match result with
          | none => 0
          | some result => next result.value (if IsPrivatePositionProbe target input then ordinal - 1 else ordinal)
              result.context result.remaining result.table
      else 0) computation

theorem privateLiveProbeAllowance_query_bind
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    privateLiveProbeAllowance target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context fuel table =
      (if DeferredCompletable table context then
        if IsPrivatePositionDisclosure target input then 0
        else privateProbeInputAllowance target table context input +
          ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
            match result with
            | none => 0
            | some result => privateLiveProbeAllowance target (next result.value) result.context result.remaining result.table
      else 0) := rfl

theorem privateLiveProbeOrdinalAllowance_query_bind
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    privateLiveProbeOrdinalAllowance target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) ordinal context fuel table =
      (if DeferredCompletable table context then
        if IsPrivatePositionDisclosure target input then 0
        else if IsPrivatePositionProbe target input ∧ ordinal = 0 then privateProbeInputAllowance target table context input
        else ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
          match result with
          | none => 0
          | some result => privateLiveProbeOrdinalAllowance target (next result.value)
              (if IsPrivatePositionProbe target input then ordinal - 1 else ordinal) result.context result.remaining result.table
      else 0) := rfl

theorem sum_privateLiveProbeOrdinalAllowance_eq
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP (IsPrivatePositionProbe target) q) :
    (∑ ordinal ∈ Finset.range q, privateLiveProbeOrdinalAllowance target computation ordinal context fuel table) =
      privateLiveProbeAllowance target computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing q context fuel table with
  | pure value => simp [privateLiveProbeOrdinalAllowance, privateLiveProbeAllowance]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [privateLiveProbeAllowance_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete]
        by_cases hdisclose : IsPrivatePositionDisclosure target input
        · simp [privateLiveProbeOrdinalAllowance_query_bind, hcomplete, hdisclose]
        · rw [if_neg hdisclose]
          have htail (n : Nat) (hnext : ∀ reply, (next reply).IsQueryBoundP (IsPrivatePositionProbe target) n) :
              (∑ ordinal ∈ Finset.range n, ∑' result,
                Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
                  match result with
                  | none => 0
                  | some result => privateLiveProbeOrdinalAllowance target (next result.value) ordinal result.context result.remaining result.table) =
              ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
                match result with
                | none => 0
                | some result => privateLiveProbeAllowance target (next result.value) result.context result.remaining result.table := by
            rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
            apply tsum_congr
            intro result
            cases result with
            | none => simp
            | some result =>
                simp only [← Finset.mul_sum]
                rw [ih result.value n result.context result.remaining result.table (hnext result.value)]
          by_cases hprobe : IsPrivatePositionProbe target input
          · cases q with
            | zero => simp [hprobe] at hbound
            | succ q =>
                rw [Finset.sum_range_succ']
                simp only [privateLiveProbeOrdinalAllowance_query_bind, if_pos hcomplete, if_neg hdisclose,
                  hprobe, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel, and_self, if_true]
                exact (congrArg (fun value => value + privateProbeInputAllowance target table context input)
                  (htail q (fun reply => by simpa only [if_pos hprobe, Nat.add_sub_cancel] using hbound.2 reply))).trans (add_comm _ _)
          · simp only [privateLiveProbeOrdinalAllowance_query_bind, if_pos hcomplete, if_neg hdisclose,
              hprobe, false_and, if_false, privateProbeInputAllowance_of_not_probe target table context input hprobe, zero_add]
            exact htail q (fun reply => by simpa only [if_neg hprobe] using hbound.2 reply)
      · simp [privateLiveProbeOrdinalAllowance_query_bind, hcomplete]

end SphincsSecurity.Concrete.OtsProbeSimulation
