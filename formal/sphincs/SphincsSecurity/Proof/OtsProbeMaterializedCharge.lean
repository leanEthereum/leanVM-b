import SphincsSecurity.Proof.OtsProbeOrdinaryCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

noncomputable def materializedChargeHandler (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (state : LazyRevealProbe.State Coordinate) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) ((OracleWorld + SigningSpec).Range input) :=
  match input with
  | .inl (.inl n) => splitUniformImpl n
  | .inl (.inr input) =>
      let publicState := canonicalPublicProbeState state
      let plan := purePlanProbingHashQuery parameter input publicState
      probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan
  | .inr message => maskedSign parameter root ftsSecret message

noncomputable def materializedBoundaryCharge {α : Type} (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α) :
    LazyRevealProbe.State Coordinate → Nat → SplitHashCache → ℝ≥0∞ :=
  OracleComp.construct (fun _ _ _ _ => 0)
    (fun input _ next state fuel cache =>
      ordinaryContinuationCharge (fun context remaining value => next value.1 context.state remaining value.2)
        ((materializedChargeHandler parameter root ftsSecret input state).run cache)
        (directDeferredContext state) fuel) computation

theorem materializedBoundaryCharge_query_bind {α : Type} (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (cache : SplitHashCache) :
    materializedBoundaryCharge parameter root ftsSecret (OracleSpec.query input >>= next) state fuel cache =
      ordinaryContinuationCharge (fun context remaining value =>
        materializedBoundaryCharge parameter root ftsSecret (next value.1) context.state remaining value.2)
        ((materializedChargeHandler parameter root ftsSecret input state).run cache)
        (directDeferredContext state) fuel := rfl

theorem probEvent_sampledRunThenFinalizeClean_none_le_unmaterializedCharge
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe fuel) :
    Pr[= none | sampledRunThenFinalizeClean state fuel computation] ≤
      (LazyRevealProbe.expectedProbeCharge computation state fuel + (state.unmaterializedPending.card : ℝ≥0∞)) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[= none | detailedExperimentCleanWithCompletionTable state fuel computation] :=
      probOutput_congr rfl (by
        unfold sampledRunThenFinalizeClean
        exact evalDist_runThenFinalizeCleanFromTable_eq_detailed computation state fuel)
    _ = Pr[= true | LazyRevealProbe.experiment state fuel computation] :=
      probEvent_detailedExperimentClean_none_eq_hit computation state fuel hbound
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      exact LazyRevealProbe.experiment_probability_le_expectedProbeCharge_unmaterialized state fuel computation

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_sampledMaterializedCleanBoundaryFailure_le_charge
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : LazyRevealProbe.State Coordinate) (fuel bound : Nat)
    (cache : SplitHashCache)
    (hbound : ∀ table,
      StartTableAgrees state table →
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        computation).IsQueryBoundP (fun query => query matches Sum.inr _) bound)
    (hbudget : bound ≤ fuel)
    (hpublished : PublishedValues state) :
    Pr[= true |
        sampledMaterializedCleanBoundaryFailure parameter root ftsSecret computation state fuel
          cache] ≤
      (materializedBoundaryCharge parameter root ftsSecret computation state fuel cache +
        (state.unmaterializedPending.card : ENNReal)) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing state fuel bound cache with
  | pure value =>
      have hdist :
          𝒟[Option.isNone <$> sampledRunThenFinalizeClean state fuel
            (pure (value, cache) : OracleComp (LazyRevealProbe.World Coordinate)
              (α × SplitHashCache))] =
            𝒟[sampledMaterializedCleanBoundaryFailure parameter root ftsSecret
              (pure value) state fuel cache] := by
        unfold sampledRunThenFinalizeClean sampledMaterializedCleanBoundaryFailure
          materializedCleanBoundaryFailureFromTable
        rw [map_bind]
        apply evalDist_bind_congr
        intro base _hbase
        rw [runCleanFromTable_pure_oracle]
        simp [materializedCleanBoundary]
      calc
        _ = Pr[= true | Option.isNone <$> sampledRunThenFinalizeClean state fuel
              (pure (value, cache) : OracleComp (LazyRevealProbe.World Coordinate)
                (α × SplitHashCache))] :=
          OracleComp.probOutput_congr rfl hdist.symm
        _ = Pr[= none | sampledRunThenFinalizeClean state fuel
              (pure (value, cache) : OracleComp (LazyRevealProbe.World Coordinate)
                (α × SplitHashCache))] := by
          rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map]
          apply OracleComp.probEvent_congr'
          · intro result _hresult
            cases result <;> simp
          · rfl
        _ ≤ _ := probEvent_sampledRunThenFinalizeClean_none_le_unmaterializedCharge
          (pure (value, cache) : OracleComp (LazyRevealProbe.World Coordinate)
            (α × SplitHashCache)) state fuel (by simp)
  | query_bind query next ih =>
      rw [materializedBoundaryCharge_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              have hinnerBound : ((splitUniformImpl n).run cache).IsQueryBoundP
                  LazyRevealProbe.IsProbe 0 := splitUniformImpl_probeFree n cache
              have hstep := evalDist_sampledCleanStep_eq_safeSupportedGuardedContinuation
                parameter root ftsSecret next (splitUniformImpl n) state fuel cache 0 bound
                (fun _ _ ↦ True) hpublished hinnerBound
                (preservesPublishedValuesImpl_splitUniformImpl n) (by simp) (by omega)
              have hdist :
                  𝒟[sampledMaterializedCleanBoundaryFailure parameter root ftsSecret
                    ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                      (.inl (.inl n)))) >>= next) state fuel cache] =
                    𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
                      (supportedGuardedMaterializedCleanContinuation parameter root ftsSecret next
                        bound state (fun _ _ ↦ True))
                      (directDeferredContext state) fuel ((splitUniformImpl n).run cache)] := by
                calc
                  _ = 𝒟[do
                      let base ← sampleOtsHashTable
                      let table := completedStartTable state base
                      let result ← runCleanFromTable state fuel table
                        ((splitUniformImpl n).run cache)
                      finishCleanFailureObserve
                        (fun nextTable nextState remaining value =>
                          materializedCleanBoundaryFailureFromTable parameter root ftsSecret
                            (next (value : Fin (n + 1) × SplitHashCache).1) nextState remaining
                            nextTable value.2)
                        result] := by
                    unfold sampledMaterializedCleanBoundaryFailure
                    apply evalDist_bind_congr
                    intro base _hbase
                    exact materializedCleanBoundaryFailureFromTable_uniform_query_bind parameter
                      root ftsSecret n next state fuel (completedStartTable state base) cache
                      (startTableAgrees_completedStartTable state base)
                  _ = _ := hstep
              calc
                _ = Pr[= true | runDirectDetailedSafeOrdinaryWithCompletionTable
                      (supportedGuardedMaterializedCleanContinuation parameter root ftsSecret next
                        bound state (fun _ _ ↦ True))
                      (directDeferredContext state) fuel ((splitUniformImpl n).run cache)] :=
                  OracleComp.probOutput_congr rfl hdist
                _ ≤ _ := by
                  rw [← probEvent_eq_eq_probOutput]
                  apply probEvent_safeOrdinary_le_continuationCharge
                  intro nextContext remaining value
                  rw [probEvent_eq_eq_probOutput]
                  by_cases hguard : PublishedValues nextContext.state ∧ bound ≤ remaining ∧
                      LazyRevealProbe.ValuesLE state nextContext.state
                  · rcases hguard with ⟨hnextPublished, hnextBudget, hvalues⟩
                    have hinitial : ∀ base,
                        StartTableAgrees state (completedStartTable nextContext.state base) := by
                      intro base index output hvalue
                      exact startTableAgrees_completedStartTable nextContext.state base index output
                        (hvalues index.coordinate output hvalue)
                    simpa [supportedGuardedMaterializedCleanContinuation, hnextPublished,
                      hnextBudget, hvalues, hinitial,
                      startTableAgrees_completedStartTable,
                      sampledMaterializedCleanBoundaryFailure] using
                      (ih value.1 nextContext.state remaining bound value.2
                      (by
                        intro table hagrees
                        have hinitial' : StartTableAgrees state table := by
                          intro index output hvalue
                          exact hagrees index output (hvalues index.coordinate output hvalue)
                        have hsource := hbound table hinitial'
                        rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                          OracleComp.isQueryBoundP_query_bind_iff] at hsource
                        exact hsource.2 value.1)
                      hnextBudget hnextPublished)
                  · have hcondition : ∀ base,
                        ¬(PublishedValues nextContext.state ∧ bound ≤ remaining ∧
                          LazyRevealProbe.ValuesLE state nextContext.state ∧
                          StartTableAgrees state
                            (completedStartTable nextContext.state base) ∧
                          StartTableAgrees nextContext.state
                            (completedStartTable nextContext.state base) ∧ True) := by
                      intro base hfull
                      exact hguard ⟨hfull.1, hfull.2.1, hfull.2.2.1⟩
                    simp only [supportedGuardedMaterializedCleanContinuation]
                    simp_rw [if_neg (hcondition _)]
                    have hdist : 𝒟[(do
                        let _base ← sampleOtsHashTable
                        pure false : ProbComp Bool)] = 𝒟[(pure false : ProbComp Bool)] :=
                      evalDist_sampleOtsHashTable_bind_const _
                    have hpure : Pr[= true | (pure false : ProbComp Bool)] ≤
                        (materializedBoundaryCharge parameter root ftsSecret (next value.1) nextContext.state remaining value.2 + (nextContext.state.unmaterializedPending.card : ENNReal)) *
                          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
                      simpa only [probOutput_pure, Bool.true_eq_false, ↓reduceIte] using
                        (zero_le : (0 : ENNReal) ≤
                          (materializedBoundaryCharge parameter root ftsSecret (next value.1) nextContext.state remaining value.2 + (nextContext.state.unmaterializedPending.card : ENNReal)) *
                            ((2 ^ digestBits : Nat) : ENNReal)⁻¹)
                    exact (OracleComp.probOutput_congr rfl hdist).le.trans hpure
          | inr input =>
              let publicState := canonicalPublicProbeState state
              let plan := purePlanProbingHashQuery parameter input publicState
              let inner := probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan
              let nextBound := bound - 1
              have hpositive : 0 < bound := by
                let table := completedStartTable state (fun _ ↦ 0)
                have hsource := hbound table (startTableAgrees_completedStartTable state _)
                rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                  OracleComp.isQueryBoundP_query_bind_iff] at hsource
                rcases hsource.1 with hnot | hpositive
                · exact (hnot (by simp)).elim
                · exact hpositive
              have hinnerBound : (inner.run cache).IsQueryBoundP
                  LazyRevealProbe.IsProbe 1 :=
                probingHashQueryAfterRootAwarePublicPlan_isProbeBound_one parameter input
                  publicState plan cache
              have hstep := evalDist_sampledCleanStep_eq_safeSupportedGuardedContinuation
                parameter root ftsSecret next inner state fuel cache 1 nextBound
                (fun _ _ ↦ True) hpublished hinnerBound
                (preservesPublishedValues_probingHashQueryAfterRootAwarePublicPlan parameter input
                  publicState plan)
                (by simp)
                (by dsimp only [nextBound]; omega)
              have hdist :
                  𝒟[sampledMaterializedCleanBoundaryFailure parameter root ftsSecret
                    ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                      (.inl (.inr input)))) >>= next) state fuel cache] =
                    𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
                      (supportedGuardedMaterializedCleanContinuation parameter root ftsSecret next
                        nextBound state (fun _ _ ↦ True))
                      (directDeferredContext state) fuel (inner.run cache)] := by
                calc
                  _ = 𝒟[do
                      let base ← sampleOtsHashTable
                      let table := completedStartTable state base
                      let result ← runCleanFromTable state fuel table (inner.run cache)
                      finishCleanFailureObserve
                        (fun nextTable nextState remaining value =>
                          materializedCleanBoundaryFailureFromTable parameter root ftsSecret
                            (next (value : HashOutput × SplitHashCache).1) nextState remaining
                            nextTable value.2)
                        result] := by
                    unfold sampledMaterializedCleanBoundaryFailure
                    apply evalDist_bind_congr
                    intro base _hbase
                    simpa only [publicState, plan, inner] using
                      (materializedCleanBoundaryFailureFromTable_hash_query_bind parameter root
                        ftsSecret input next state fuel (completedStartTable state base) cache
                        (startTableAgrees_completedStartTable state base) hpublished)
                  _ = _ := hstep
              calc
                _ = Pr[= true | runDirectDetailedSafeOrdinaryWithCompletionTable
                      (supportedGuardedMaterializedCleanContinuation parameter root ftsSecret next
                        nextBound state (fun _ _ ↦ True))
                      (directDeferredContext state) fuel (inner.run cache)] :=
                  OracleComp.probOutput_congr rfl hdist
                _ ≤ _ := by
                  rw [← probEvent_eq_eq_probOutput]
                  apply probEvent_safeOrdinary_le_continuationCharge
                  intro nextContext remaining value
                  rw [probEvent_eq_eq_probOutput]
                  by_cases hguard : PublishedValues nextContext.state ∧
                      nextBound ≤ remaining ∧
                      LazyRevealProbe.ValuesLE state nextContext.state
                  · rcases hguard with ⟨hnextPublished, hnextBudget, hvalues⟩
                    have hinitial : ∀ base,
                        StartTableAgrees state (completedStartTable nextContext.state base) := by
                      intro base index output hvalue
                      exact startTableAgrees_completedStartTable nextContext.state base index output
                        (hvalues index.coordinate output hvalue)
                    simpa [supportedGuardedMaterializedCleanContinuation, hnextPublished,
                      hnextBudget, hvalues, hinitial,
                      startTableAgrees_completedStartTable,
                      sampledMaterializedCleanBoundaryFailure] using
                      (ih value.1 nextContext.state remaining nextBound value.2
                      (by
                        intro table hagrees
                        have hinitial' : StartTableAgrees state table := by
                          intro index output hvalue
                          exact hagrees index output (hvalues index.coordinate output hvalue)
                        have hsource := hbound table hinitial'
                        rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                          OracleComp.isQueryBoundP_query_bind_iff] at hsource
                        dsimp only [nextBound]
                        simpa using hsource.2 value.1)
                      hnextBudget hnextPublished)
                  · have hcondition : ∀ base,
                        ¬(PublishedValues nextContext.state ∧ nextBound ≤ remaining ∧
                          LazyRevealProbe.ValuesLE state nextContext.state ∧
                          StartTableAgrees state
                            (completedStartTable nextContext.state base) ∧
                          StartTableAgrees nextContext.state
                            (completedStartTable nextContext.state base) ∧ True) := by
                      intro base hfull
                      exact hguard ⟨hfull.1, hfull.2.1, hfull.2.2.1⟩
                    simp only [supportedGuardedMaterializedCleanContinuation]
                    simp_rw [if_neg (hcondition _)]
                    have hdist : 𝒟[(do
                        let _base ← sampleOtsHashTable
                        pure false : ProbComp Bool)] = 𝒟[(pure false : ProbComp Bool)] :=
                      evalDist_sampleOtsHashTable_bind_const _
                    have hpure : Pr[= true | (pure false : ProbComp Bool)] ≤
                        (materializedBoundaryCharge parameter root ftsSecret (next value.1) nextContext.state remaining value.2 + (nextContext.state.unmaterializedPending.card : ENNReal)) *
                          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
                      simpa only [probOutput_pure, Bool.true_eq_false, ↓reduceIte] using
                        (zero_le : (0 : ENNReal) ≤
                          (materializedBoundaryCharge parameter root ftsSecret (next value.1) nextContext.state remaining value.2 + (nextContext.state.unmaterializedPending.card : ENNReal)) *
                            ((2 ^ digestBits : Nat) : ENNReal)⁻¹)
                    exact (OracleComp.probOutput_congr rfl hdist).le.trans hpure
      | inr message =>
          have hinnerBound : ((maskedSign parameter root ftsSecret message).run cache).IsQueryBoundP
              LazyRevealProbe.IsProbe 0 :=
            maskedSign_probeFree parameter root ftsSecret message cache
          let admissible := fun (finalState : LazyRevealProbe.State Coordinate)
              (output : (OracleWorld + SigningSpec).Range (.inr message)) ↦ ∀ table,
            StartTableAgrees finalState table →
            output ∈ support
              (scheme.sign
                (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                  SecretKey)
                message)
          have hstep := evalDist_sampledCleanStep_eq_safeSupportedGuardedContinuation
            parameter root ftsSecret next (maskedSign parameter root ftsSecret message)
            state fuel cache 0 bound admissible hpublished hinnerBound
            (preservesPublishedValues_maskedSign parameter root ftsSecret message)
            (by
              intro table result _hstarts hresult nextTable hnextStarts
              have hraw := mem_support_runRaw_done_of_mem_runCleanFromTable_some
                ((maskedSign parameter root ftsSecret message).run cache) state fuel table result
                hresult
              exact maskedSign_done_output_mem_support parameter root nextTable ftsSecret message
                state result.state cache result.value.2 fuel result.remaining result.value.1
                hnextStarts hraw)
            (by omega)
          have hdist :
              𝒟[sampledMaterializedCleanBoundaryFailure parameter root ftsSecret
                ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                  (.inr message))) >>= next) state fuel cache] =
                𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
                  (supportedGuardedMaterializedCleanContinuation parameter root ftsSecret next
                    bound state admissible)
                  (directDeferredContext state) fuel
                  ((maskedSign parameter root ftsSecret message).run cache)] := by
            calc
              _ = 𝒟[do
                  let base ← sampleOtsHashTable
                  let table := completedStartTable state base
                  let result ← runCleanFromTable state fuel table
                    ((maskedSign parameter root ftsSecret message).run cache)
                  finishCleanFailureObserve
                    (fun nextTable nextState remaining value =>
                      materializedCleanBoundaryFailureFromTable parameter root ftsSecret
                        (next (value : Option Signature × SplitHashCache).1) nextState remaining
                        nextTable value.2)
                    result] := by
                unfold sampledMaterializedCleanBoundaryFailure
                apply evalDist_bind_congr
                intro base _hbase
                exact materializedCleanBoundaryFailureFromTable_sign_query_bind parameter root
                  ftsSecret message next state fuel (completedStartTable state base) cache
                  (startTableAgrees_completedStartTable state base)
              _ = _ := hstep
          calc
            _ = Pr[= true | runDirectDetailedSafeOrdinaryWithCompletionTable
                  (supportedGuardedMaterializedCleanContinuation parameter root ftsSecret next
                    bound state admissible)
                  (directDeferredContext state) fuel
                  ((maskedSign parameter root ftsSecret message).run cache)] :=
              OracleComp.probOutput_congr rfl hdist
            _ ≤ _ := by
              rw [← probEvent_eq_eq_probOutput]
              apply probEvent_safeOrdinary_le_continuationCharge
              intro nextContext remaining value
              rw [probEvent_eq_eq_probOutput]
              by_cases hguard : PublishedValues nextContext.state ∧ bound ≤ remaining ∧
                  LazyRevealProbe.ValuesLE state nextContext.state ∧
                  admissible nextContext.state value.1
              · rcases hguard with
                  ⟨hnextPublished, hnextBudget, hvalues, hallowed⟩
                have hinitial : ∀ base,
                    StartTableAgrees state (completedStartTable nextContext.state base) := by
                  intro base index output hvalue
                  exact startTableAgrees_completedStartTable nextContext.state base index output
                    (hvalues index.coordinate output hvalue)
                simpa [supportedGuardedMaterializedCleanContinuation, hnextPublished,
                  hnextBudget, hvalues, hinitial, startTableAgrees_completedStartTable,
                  hallowed, sampledMaterializedCleanBoundaryFailure] using
                  (ih value.1 nextContext.state remaining bound value.2
                    (by
                      intro table hagrees
                      have hinitial' : StartTableAgrees state table := by
                        intro index output hvalue
                        exact hagrees index output (hvalues index.coordinate output hvalue)
                      have hsource := hbound table hinitial'
                      rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hsource
                      exact isQueryBoundP_of_bind hsource value.1 (hallowed table hagrees))
                    hnextBudget hnextPublished)
              · have hcondition : ∀ base,
                    ¬(PublishedValues nextContext.state ∧ bound ≤ remaining ∧
                      LazyRevealProbe.ValuesLE state nextContext.state ∧
                      StartTableAgrees state (completedStartTable nextContext.state base) ∧
                      StartTableAgrees nextContext.state
                        (completedStartTable nextContext.state base) ∧
                      admissible nextContext.state value.1) := by
                  intro base hfull
                  exact hguard
                    ⟨hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2.2.2⟩
                simp only [supportedGuardedMaterializedCleanContinuation]
                simp_rw [if_neg (hcondition _)]
                have hdist : 𝒟[(do
                    let _base ← sampleOtsHashTable
                    pure false : ProbComp Bool)] = 𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_sampleOtsHashTable_bind_const _
                have hpure : Pr[= true | (pure false : ProbComp Bool)] ≤
                    (materializedBoundaryCharge parameter root ftsSecret (next value.1) nextContext.state remaining value.2 + (nextContext.state.unmaterializedPending.card : ENNReal)) *
                      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
                  simpa only [probOutput_pure, Bool.true_eq_false, ↓reduceIte] using
                    (zero_le : (0 : ENNReal) ≤
                      (materializedBoundaryCharge parameter root ftsSecret (next value.1) nextContext.state remaining value.2 + (nextContext.state.unmaterializedPending.card : ENNReal)) *
                        ((2 ^ digestBits : Nat) : ENNReal)⁻¹)
                exact (OracleComp.probOutput_congr rfl hdist).le.trans hpure


end SphincsSecurity.Concrete.OtsProbeSimulation
