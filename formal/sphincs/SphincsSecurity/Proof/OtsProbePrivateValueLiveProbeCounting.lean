import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueLiveProbeCut
import SphincsSecurity.Proof.OtsProbePrivateValueProbeCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedLiveResolvedQueryCharge
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ => 0)
    (fun input _ next context fuel table =>
      if DeferredCompletable table context then
        charge input + ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
          match result with
          | none => 0
          | some result => next result.value result.context result.remaining result.table
      else 0) computation

theorem expectedLiveResolvedQueryCharge_query_bind
    (charge : LazyRevealProbe.Query Coordinate → ENNReal) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveResolvedQueryCharge charge ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context fuel table =
      (if DeferredCompletable table context then
        charge input + ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
          match result with
          | none => 0
          | some result => expectedLiveResolvedQueryCharge charge (next result.value) result.context result.remaining result.table
      else 0) := rfl

theorem expectedLiveResolvedQueryCharge_eq_zero_of_not_completable
    (charge : LazyRevealProbe.Query Coordinate → ENNReal) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (hdoomed : ¬DeferredCompletable table context) :
    expectedLiveResolvedQueryCharge charge computation context fuel table = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next _ => rw [expectedLiveResolvedQueryCharge_query_bind, if_neg hdoomed]

noncomputable def privateLiveProbeOrdinalMass
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    Nat → DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next ordinal context fuel table =>
      if DeferredCompletable table context then
        if IsPrivatePositionDisclosure target input then 0
        else if IsPrivatePositionProbe target input ∧ ordinal = 0 then 1
        else ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
          match result with
          | none => 0
          | some result => next result.value (if IsPrivatePositionProbe target input then ordinal - 1 else ordinal)
              result.context result.remaining result.table
      else 0) computation

theorem privateLiveProbeOrdinalMass_query_bind
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    privateLiveProbeOrdinalMass target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      ordinal context fuel table =
      (if DeferredCompletable table context then
        if IsPrivatePositionDisclosure target input then 0
        else if IsPrivatePositionProbe target input ∧ ordinal = 0 then 1
        else ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
          match result with
          | none => 0
          | some result => privateLiveProbeOrdinalMass target (next result.value)
              (if IsPrivatePositionProbe target input then ordinal - 1 else ordinal) result.context result.remaining result.table
      else 0) := rfl

theorem probEvent_livePrivateProbeCutReached_eq_ordinalMass
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    Pr[LivePrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] =
      privateLiveProbeOrdinalMass target computation ordinal context fuel table := by
  induction computation using OracleComp.inductionOn generalizing ordinal context fuel table with
  | pure value =>
      by_cases hcomplete : DeferredCompletable table context <;>
        simp [privatePositionProbeCutAt, runResolvedFromTable, privateLiveProbeOrdinalMass,
          LivePrivateProbeCutReached, retainCompletableResult, hcomplete, PrivateProbeCutReached, privatePositionAccessCandidate]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [privatePositionProbeCutAt_query_bind, privateLiveProbeOrdinalMass_query_bind, if_pos hcomplete]
        by_cases hdisclose : IsPrivatePositionDisclosure target input
        · rw [if_pos hdisclose, if_pos hdisclose]
          cases input <;> simp [IsPrivatePositionDisclosure] at hdisclose <;>
            simp [runResolvedFromTable, LivePrivateProbeCutReached, retainCompletableResult, hcomplete,
              PrivateProbeCutReached, privatePositionAccessCandidate]
        · rw [if_neg hdisclose, if_neg hdisclose]
          have htail (n : Nat) :
              Pr[LivePrivateProbeCutReached target | runResolvedFromTable context fuel table
                ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
                  fun reply => privatePositionProbeCutAt target (next reply) n)] =
              ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
                match result with
                | none => 0
                | some result => privateLiveProbeOrdinalMass target (next result.value) n result.context result.remaining result.table := by
            rw [runResolvedFromTable_bind, probEvent_bind_eq_tsum]
            apply tsum_congr
            intro result
            by_cases hresult : result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
            · cases result with
              | none => simp [LivePrivateProbeCutReached, retainCompletableResult, PrivateProbeCutReached, privatePositionAccessCandidate]
              | some result =>
                  have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input)) context fuel table result hconsistent hstarts hresult
                  dsimp only
                  rw [ih result.value n result.context result.remaining result.table hcore.2.1 (hcore.1 ▸ hcore.2.2)]
            · simp [probOutput_eq_zero_of_not_mem_support hresult]
          by_cases hprobe : IsPrivatePositionProbe target input
          · rw [if_pos hprobe]
            cases ordinal with
            | zero =>
                simp only [hprobe, and_self, if_true]
                cases input <;> simp [IsPrivatePositionProbe] at hprobe
                subst_vars
                simp [runResolvedFromTable, LivePrivateProbeCutReached, retainCompletableResult, hcomplete,
                  PrivateProbeCutReached, privatePositionAccessCandidate]
            | succ ordinal =>
                simp only [hprobe, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, if_true, Nat.add_sub_cancel]
                rw [htail ordinal]
                apply tsum_congr
                intro result
                cases result <;> rfl
          · simp only [hprobe, false_and, if_false]
            rw [htail ordinal]
            apply tsum_congr
            intro result
            cases result <;> rfl
      · rw [probEvent_livePrivateProbeCutReached_eq_zero_of_not_completable target _ context fuel table ordinal hconsistent hstarts hcomplete,
          privateLiveProbeOrdinalMass_query_bind, if_neg hcomplete]

theorem sum_privateLiveProbeOrdinalMass_le_expectedCharge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    (∑ ordinal ∈ Finset.range q, privateLiveProbeOrdinalMass target computation ordinal context fuel table) ≤
      expectedLiveResolvedQueryCharge (privatePositionProbeQueryCharge target) computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing q context fuel table with
  | pure value => simp [privateLiveProbeOrdinalMass, expectedLiveResolvedQueryCharge]
  | query_bind input next ih =>
      rw [expectedLiveResolvedQueryCharge_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete]
        by_cases hdisclose : IsPrivatePositionDisclosure target input
        · simp [privateLiveProbeOrdinalMass_query_bind, hcomplete, hdisclose]
        · have htail (n : Nat) :
              (∑ ordinal ∈ Finset.range n, ∑' result,
                Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
                  match result with
                  | none => 0
                  | some result => privateLiveProbeOrdinalMass target (next result.value) ordinal result.context result.remaining result.table) ≤
              ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
                match result with
                | none => 0
                | some result => expectedLiveResolvedQueryCharge (privatePositionProbeQueryCharge target)
                    (next result.value) result.context result.remaining result.table := by
            rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
            apply ENNReal.tsum_le_tsum
            intro result
            cases result with
            | none => simp
            | some result =>
                simp only [← Finset.mul_sum]
                exact mul_le_mul' le_rfl (ih result.value n result.context result.remaining result.table)
          by_cases hprobe : IsPrivatePositionProbe target input
          · cases q with
            | zero => simp
            | succ q =>
                rw [Finset.sum_range_succ']
                simp only [privateLiveProbeOrdinalMass_query_bind, if_pos hcomplete, if_neg hdisclose, hprobe, Nat.add_eq_zero_iff,
                  Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel, and_self, if_true,
                  privatePositionProbeQueryCharge]
                exact (add_le_add (htail q) (le_refl 1)).trans_eq (add_comm _ _)
          · simp only [privateLiveProbeOrdinalMass_query_bind, if_pos hcomplete, if_neg hdisclose, hprobe, false_and, if_false,
              privatePositionProbeQueryCharge, zero_add]
            exact htail q
      · simp [privateLiveProbeOrdinalMass_query_bind, hcomplete]

theorem expectedLiveResolvedQueryCharge_mono
    (left right : LazyRevealProbe.Query Coordinate → ENNReal) (hle : ∀ input, left input ≤ right input)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveResolvedQueryCharge left computation context fuel table ≤ expectedLiveResolvedQueryCharge right computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedLiveResolvedQueryCharge_query_bind, expectedLiveResolvedQueryCharge_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, if_pos hcomplete]
        apply add_le_add (hle input)
        apply ENNReal.tsum_le_tsum
        intro result
        cases result with
        | none => rfl
        | some result => exact mul_le_mul' le_rfl (ih result.value result.context result.remaining result.table)
      · simp [hcomplete]

theorem expectedLiveResolvedQueryCharge_finset_sum
    (indices : Finset ι) (charge : ι → LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveResolvedQueryCharge (fun input => ∑ index ∈ indices, charge index input) computation context fuel table =
      ∑ index ∈ indices, expectedLiveResolvedQueryCharge (charge index) computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => simp [expectedLiveResolvedQueryCharge]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · simp only [expectedLiveResolvedQueryCharge_query_bind, if_pos hcomplete, Finset.sum_add_distrib]
        congr 1
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        apply tsum_congr
        intro result
        cases result with
        | none => simp
        | some result =>
            simp only [← Finset.mul_sum]
            rw [ih]
      · simp [expectedLiveResolvedQueryCharge_query_bind, hcomplete]

theorem sum_targets_livePrivateProbeCutReached_le_expectedStructuralCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[LivePrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)]) ≤
      expectedLiveResolvedQueryCharge structuralProbeQueryCharge computation context fuel table := by
  simp_rw [probEvent_livePrivateProbeCutReached_eq_ordinalMass _ _ _ _ _ _ hconsistent hstarts]
  calc
    _ ≤ ∑ target ∈ targets, expectedLiveResolvedQueryCharge (privatePositionProbeQueryCharge target) computation context fuel table :=
      Finset.sum_le_sum (fun target _ => sum_privateLiveProbeOrdinalMass_le_expectedCharge target computation q context fuel table)
    _ = expectedLiveResolvedQueryCharge (fun input => ∑ target ∈ targets, privatePositionProbeQueryCharge target input) computation context fuel table :=
      (expectedLiveResolvedQueryCharge_finset_sum targets privatePositionProbeQueryCharge computation context fuel table).symm
    _ ≤ _ := expectedLiveResolvedQueryCharge_mono _ _ (sum_privatePositionProbeQueryCharge_le_structural targets) computation context fuel table

theorem sum_targets_privateResolvedRawCandidate_hit_le_expectedLiveStructuralCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : ∀ target ∈ targets, .position target ∈ context.state.ensured)
    (hstate : ∀ target ∈ targets, context.state.values (.position target) = none)
    (hvalue : ∀ target ∈ targets, context.values target = none)
    (hhidden : ∀ target ∈ targets, .position target ∉ context.state.revealed)
    (hcard : ∀ target ∈ targets, (context.state.pendingAt (.position target)).card + q ≤ 2 ^ 126) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)]) ≤
      expectedLiveResolvedQueryCharge structuralProbeQueryCharge computation context fuel table *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  calc
    _ ≤ ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        Pr[LivePrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] *
          ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
      apply Finset.sum_le_sum
      intro target htarget
      apply Finset.sum_le_sum
      intro ordinal hordinal
      apply probEvent_privateResolvedRawCandidate_hit_le_live_cut target computation context fuel table ordinal hvalid hcomplete
        (hensured target htarget) (hstate target htarget) (hvalue target htarget) (hhidden target htarget)
      exact (Nat.add_le_add_left (Nat.le_of_lt (Finset.mem_range.mp hordinal)) _).trans (hcard target htarget)
    _ = (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        Pr[LivePrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)]) *
          ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by simp only [Finset.sum_mul]
    _ ≤ _ := mul_le_mul' (sum_targets_livePrivateProbeCutReached_le_expectedStructuralCharge targets computation q context fuel table
      hvalid.valuesConsistent (startTableAgrees_of_deferredCompletable hcomplete)) le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
