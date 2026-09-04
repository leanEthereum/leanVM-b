import SphincsSecurity.Proof.OtsProbeJointStep

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_directJointSnapshotBoundary_diagnostic
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache) (q bound : Nat)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey)) computation).IsQueryBoundP
        (fun query => query matches Sum.inr _) bound)
    (hcontext : FinalizationContextLE table left right)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hcanonical : CanonicalMaterializedValues table left)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hleftLower : bound ≤ leftFuel) (hleftUpper : leftFuel ≤ q)
    (hrightLower : q + bound ≤ rightFuel) :
    RelTriple
      (directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve parameter root ftsSecret
        computation (retainedResolvedFinalizationBoundaryWitnessSnapshotObserve table root)
        snapshots left leftFuel table leftCache)
      (observedMaterializedBoundary parameter root ftsSecret computation observations right.state
        rightFuel table rightCache >>= finishObservedMaterializedDiagnostic table)
      (BoundarySnapshotDiagnosticRel table) := by
  induction computation using OracleComp.inductionOn generalizing
      snapshots observations left right leftFuel rightFuel leftCache rightCache bound with
  | pure value =>
      rw [directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve,
        OracleComp.construct_pure, observedMaterializedBoundary, OracleComp.construct_pure]
      simp only [pure_bind]
      apply relTriple_retainedFinalization_jointDiagnostic table root left leftFuel
        (value, leftCache) ⟨right.state, rightFuel, (value, rightCache), table, observations⟩ snapshots
        haligned rfl
      simpa only [← hrightMaterialized] using hcontext
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve,
        OracleComp.construct_query_bind, observedMaterializedBoundary,
        OracleComp.construct_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              simp only [bind_assoc]
              let leftObserve : DeferredContext → Nat →
                  (Fin (n + 1) × SplitHashCache) → List PlannedProbeSnapshot →
                    ProbComp BoundaryWitnessSnapshotOutput :=
                fun nextContext remaining value laterSnapshots =>
                  directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve parameter root
                    ftsSecret (next value.1)
                    (retainedResolvedFinalizationBoundaryWitnessSnapshotObserve table root)
                    laterSnapshots nextContext remaining table value.2
              have hbase := (witnessMaterializedStableCouples_splitUniformImpl table n)
                left right leftFuel rightFuel leftCache rightCache hcontext (by omega) hcache
                hrevealed hvalues hpublished hrightMaterialized
              have hlocal := relTriple_runDirectResolvedWitness_observed_of_probeFree table
                ((splitUniformImpl n).run leftCache) ((splitUniformImpl n).run rightCache)
                observations left right leftFuel rightFuel
                hbase (splitUniformImpl_probeFree n rightCache) hrightMaterialized
              have hleftSupported :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hlocal
                  (fun result => result ∈ support
                    (runDirectResolvedWitnessFromTable left leftFuel table
                      ((splitUniformImpl n).run leftCache)))
                  (fun result hresult => hresult)
              have hbothSupported :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
                  hleftSupported
              unfold runDirectBoundaryWitnessSnapshotObserve
              apply relTriple_bind hbothSupported
              intro leftResult rightResult hstep
              rcases hstep with ⟨⟨hstep, hleftSupport⟩, hrightSupport⟩
              change RelTriple
                (finishDirectBoundaryWitnessSnapshotObserve
                  (canonicalizeDirectBoundaryWitnessSnapshotObserve table leftObserve) snapshots
                  leftResult)
                ((match rightResult with
                  | none => pure none
                  | some result =>
                      observedMaterializedBoundary parameter root ftsSecret
                        (next result.value.1) result.observations result.state result.remaining
                        table result.value.2) >>= finishObservedMaterializedDiagnostic table)
                (BoundarySnapshotDiagnosticRel table)
              have hfinish := relTriple_finishJointWitnessObservedStep (α := Fin (n + 1))
                (β := RetainedRestResult) parameter (fun _ => root) ftsSecret next leftObserve
                snapshots observations table leftResult rightResult hstep haligned (by
                intro nextLeft nextRight hleftEq hrightEq hclean
                rw [hleftEq] at hleftSupport
                rw [hrightEq] at hrightSupport
                have hcanonicalRun := hclean.canonicalize_left
                let canonical := canonicalizeMaterializedValues table nextLeft.context
                have hleftCompletable : DeferredCompletable table canonical :=
                  hcanonicalRun.context_le.leftCompletable
                have hnotPrivate : ¬PrivateStructuralHit canonical :=
                  not_privateStructuralHit_of_deferredCompletable hleftCompletable
                have hleftFuelPreserved : leftFuel ≤ nextLeft.remaining := by
                  have := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                    ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft 0
                    (splitUniformImpl_probeFree n leftCache) hleftSupport
                  omega
                have hrightFuelPreserved : rightFuel ≤ nextRight.remaining := by
                  have := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run rightCache) observations right.state rightFuel table
                    (observedResolvedResult observations nextRight) 0
                    (splitUniformImpl_probeFree n rightCache) hrightSupport
                  simpa [observedResolvedResult] using this
                have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
                  remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                    ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft
                    (by
                      rw [← map_erase_runDirectResolvedWitnessFromTable
                        ((splitUniformImpl n).run leftCache) left leftFuel table, support_map]
                      exact ⟨.done nextLeft, hleftSupport, rfl⟩)
                unfold canonicalizeDirectBoundaryWitnessSnapshotObserve
                  classifyDirectBoundaryWitnessSnapshotObserve
                simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published,
                  ↓reduceIte, hleftCompletable]
                rw [← hclean.value_eq]
                simpa [leftObserve] using
                  (ih nextLeft.value.1 snapshots observations canonical nextRight.context
                    nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2 bound
                    (hbound.2 nextLeft.value.1) hcanonicalRun.context_le hcanonicalRun.cache_eq
                    hcanonicalRun.revealed_eq hcanonicalRun.values_le
                    hcanonicalRun.left_published hcanonicalRun.right_materialized
                    (canonicalizeMaterializedValues_canonical table nextLeft.context
                      hclean.context_le.view.leftConsistent)
                    haligned (by omega) (by omega) (by omega)))
              convert hfinish using 1
              cases rightResult <;> simp only [pure_bind]
          | inr input =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              simp only [bind_assoc]
              have hrightValues :
                  (materializedCanonicalContext table right.state).state.values =
                    left.state.values := by
                unfold materializedCanonicalContext
                rw [← hrightMaterialized]
                exact canonicalized_right_values_eq_of_finalizationContextLE hcontext
                  hrevealed hcanonical
              have hplanEq :
                  purePlanProbingHashQuery parameter input
                      (materializedCanonicalContext table right.state).state =
                    purePlanProbingHashQuery parameter input left.state :=
                purePlanProbingHashQuery_eq_of_values_eq hrightValues parameter input
              rw [hplanEq]
              rw [← rootAwareCandidateForPlan?_purePlan parameter input left.state]
              let plan := purePlanProbingHashQuery parameter input left.state
              have hpublicExecutor :
                  probingHashQueryAfterRootAwarePublicPlan parameter input
                      (materializedCanonicalContext table right.state).state plan =
                    probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan :=
                probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input
                  hrightValues plan
              rw [hpublicExecutor]
              let candidate? := rootAwareCandidateForPlan? parameter input plan
              let nextSnapshots := appendPlannedSnapshot snapshots candidate? left
              let nextObservations := observationsAfterCandidate observations right.state candidate?
              have hcontextDirect :
                  FinalizationContextLE table left (directDeferredContext right.state) := by
                rwa [← hrightMaterialized]
              have hnextAligned : SnapshotsObservedAt table nextSnapshots nextObservations := by
                exact haligned.appendCandidate candidate? hcontextDirect hrevealed hpublished
                  hcanonical
              have houter : IsOuterHash (.inl (.inr input)) := by simp [IsOuterHash]
              have hboundPositive : 0 < bound := by
                rcases hbound.1 with hnot | hpositive
                · exact (hnot (by simp)).elim
                · exact hpositive
              have hleftPositive : 0 < leftFuel := by omega
              have hstrictFuel : leftFuel < rightFuel := by omega
              have hlocal :=
                relTriple_runDirectResolvedWitness_afterPlan_observedMaterialized table parameter
                  input left.state plan observations left right leftFuel rightFuel leftCache
                  rightCache rfl hleftPositive hstrictFuel hcontext hcache hrevealed hvalues
                  hpublished hrightMaterialized
              have hleftSupported :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hlocal
                  (fun result => result ∈ support
                    (runDirectResolvedWitnessFromTable left leftFuel table
                      ((probingHashQueryAfterPlan parameter input plan).run leftCache)))
                  (fun result hresult => hresult)
              have hbothSupported :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
                  hleftSupported
              let leftObserve : DeferredContext → Nat →
                  (HashOutput × SplitHashCache) → List PlannedProbeSnapshot →
                    ProbComp BoundaryWitnessSnapshotOutput :=
                fun nextContext remaining value laterSnapshots =>
                  directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve parameter root
                    ftsSecret (next value.1)
                    (retainedResolvedFinalizationBoundaryWitnessSnapshotObserve table root)
                    laterSnapshots nextContext remaining table value.2
              unfold runDirectBoundaryWitnessSnapshotObserve
              apply relTriple_bind hbothSupported
              intro leftResult rightResult hstep
              rcases hstep with ⟨⟨hstep, hleftSupport⟩, hrightSupport⟩
              have hfinish := relTriple_finishJointWitnessObservedStep (α := HashOutput)
                (β := RetainedRestResult) parameter (fun _ => root) ftsSecret next leftObserve
                nextSnapshots nextObservations table leftResult rightResult hstep hnextAligned (by
                intro nextLeft nextRight hleftEq hrightEq hclean
                rw [hleftEq] at hleftSupport
                rw [hrightEq] at hrightSupport
                have hcanonicalRun := hclean.canonicalize_left
                let canonical := canonicalizeMaterializedValues table nextLeft.context
                have hleftCompletable : DeferredCompletable table canonical :=
                  hcanonicalRun.context_le.leftCompletable
                have hnotPrivate : ¬PrivateStructuralHit canonical :=
                  not_privateStructuralHit_of_deferredCompletable hleftCompletable
                have hleftFuelSpent : leftFuel ≤ nextLeft.remaining + 1 :=
                  fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run leftCache) left leftFuel
                    table nextLeft 1
                    (probingHashQueryAfterPlan_isProbeBound_one parameter input plan leftCache)
                    hleftSupport
                have hrightFuelSpent : rightFuel ≤ nextRight.remaining + 1 := by
                  have := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan).run
                      rightCache) observations right.state rightFuel table
                    (observedResolvedResult nextObservations nextRight) 1
                    (probingHashQueryAfterRootAwarePublicPlan_isProbeBound_one parameter input
                      left.state plan rightCache) hrightSupport
                  simpa [observedResolvedResult] using this
                have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
                  remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run leftCache) left leftFuel
                    table nextLeft (by
                      rw [← map_erase_runDirectResolvedWitnessFromTable
                        ((probingHashQueryAfterPlan parameter input plan).run leftCache) left
                        leftFuel table, support_map]
                      exact ⟨.done nextLeft, hleftSupport, rfl⟩)
                unfold canonicalizeDirectBoundaryWitnessSnapshotObserve
                  classifyDirectBoundaryWitnessSnapshotObserve
                simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published,
                  ↓reduceIte, hleftCompletable]
                rw [← hclean.value_eq]
                simpa [leftObserve, IsOuterHash] using
                  (ih nextLeft.value.1 nextSnapshots nextObservations canonical
                    nextRight.context nextLeft.remaining nextRight.remaining nextLeft.value.2
                    nextRight.value.2 (bound - 1)
                    (by simpa [IsOuterHash] using hbound.2 nextLeft.value.1)
                    hcanonicalRun.context_le hcanonicalRun.cache_eq hcanonicalRun.revealed_eq
                    hcanonicalRun.values_le hcanonicalRun.left_published
                    hcanonicalRun.right_materialized
                    (canonicalizeMaterializedValues_canonical table nextLeft.context
                      hclean.context_le.view.leftConsistent)
                    hnextAligned (by omega) (by omega) (by omega)))
              convert hfinish using 1
              · rfl
              · cases rightResult <;> rfl
      | inr message =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
          simp only [bind_assoc]
          let leftObserve : DeferredContext → Nat →
              (Option Signature × SplitHashCache) → List PlannedProbeSnapshot →
                ProbComp BoundaryWitnessSnapshotOutput :=
            fun nextContext remaining value laterSnapshots =>
              directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve parameter root
                ftsSecret (next value.1)
                (retainedResolvedFinalizationBoundaryWitnessSnapshotObserve table root)
                laterSnapshots nextContext remaining table value.2
          have hbase := (witnessMaterializedStableCouples_maskedSign table parameter root
            ftsSecret message) left right leftFuel rightFuel leftCache rightCache hcontext
              (by omega) hcache hrevealed hvalues hpublished hrightMaterialized
          have hlocal := relTriple_runDirectResolvedWitness_observed_of_probeFree table
            ((maskedSign parameter root ftsSecret message).run leftCache)
            ((maskedSign parameter root ftsSecret message).run rightCache)
            observations left right leftFuel rightFuel hbase
            (maskedSign_probeFree parameter root ftsSecret message rightCache) hrightMaterialized
          have hleftSupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hlocal
              (fun result => result ∈ support
                (runDirectResolvedWitnessFromTable left leftFuel table
                  ((maskedSign parameter root ftsSecret message).run leftCache)))
              (fun result hresult => hresult)
          have hbothSupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
              hleftSupported
          unfold runDirectBoundaryWitnessSnapshotObserve
          apply relTriple_bind hbothSupported
          intro leftResult rightResult hstep
          rcases hstep with ⟨⟨hstep, hleftSupport⟩, hrightSupport⟩
          have hfinish := relTriple_finishJointWitnessObservedStep (α := Option Signature)
            (β := RetainedRestResult) parameter (fun _ => root) ftsSecret next leftObserve
            snapshots observations table leftResult rightResult hstep haligned (by
            intro nextLeft nextRight hleftEq hrightEq hclean
            rw [hleftEq] at hleftSupport
            rw [hrightEq] at hrightSupport
            have hcanonicalRun := hclean.canonicalize_left
            let canonical := canonicalizeMaterializedValues table nextLeft.context
            have hleftCompletable : DeferredCompletable table canonical :=
              hcanonicalRun.context_le.leftCompletable
            have hnotPrivate : ¬PrivateStructuralHit canonical :=
              not_privateStructuralHit_of_deferredCompletable hleftCompletable
            have hleftFuelPreserved : leftFuel ≤ nextLeft.remaining := by
              have := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                ((maskedSign parameter root ftsSecret message).run leftCache) left leftFuel table
                nextLeft 0 (maskedSign_probeFree parameter root ftsSecret message leftCache)
                hleftSupport
              omega
            have hrightFuelPreserved : rightFuel ≤ nextRight.remaining := by
              have := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                ((maskedSign parameter root ftsSecret message).run rightCache) observations
                right.state rightFuel table (observedResolvedResult observations nextRight) 0
                (maskedSign_probeFree parameter root ftsSecret message rightCache) hrightSupport
              simpa [observedResolvedResult] using this
            have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
              remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                ((maskedSign parameter root ftsSecret message).run leftCache) left leftFuel table
                nextLeft (by
                  rw [← map_erase_runDirectResolvedWitnessFromTable
                    ((maskedSign parameter root ftsSecret message).run leftCache) left leftFuel
                    table, support_map]
                  exact ⟨.done nextLeft, hleftSupport, rfl⟩)
            unfold canonicalizeDirectBoundaryWitnessSnapshotObserve
              classifyDirectBoundaryWitnessSnapshotObserve
            simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published,
              ↓reduceIte, hleftCompletable]
            rw [← hclean.value_eq]
            have hdetailed : DirectDetailedResult.done nextLeft ∈ support
                (runDirectResolvedDetailedFromTable left leftFuel table
                  ((maskedSign parameter root ftsSecret message).run leftCache)) := by
              rw [← map_erase_runDirectResolvedWitnessFromTable
                ((maskedSign parameter root ftsSecret message).run leftCache)
                left leftFuel table, support_map]
              exact ⟨.done nextLeft, hleftSupport, rfl⟩
            have hdirect : some nextLeft ∈ support
                (runDirectResolvedFromTable left leftFuel table
                  ((maskedSign parameter root ftsSecret message).run leftCache)) :=
              mem_support_runDirectResolvedFromTable_of_done_detailed
                ((maskedSign parameter root ftsSecret message).run leftCache)
                left leftFuel table nextLeft hdetailed
            have hraw := raw_done_of_mem_runDirectResolvedFromTable
              ((maskedSign parameter root ftsSecret message).run leftCache)
              left leftFuel table nextLeft hdirect
            have houtput : nextLeft.value.1 ∈ support
                (scheme.sign
                  (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                    SecretKey) message) := by
              exact maskedSign_done_output_mem_support parameter root table ftsSecret
                message left.state nextLeft.context.state leftCache nextLeft.value.2
                leftFuel nextLeft.remaining nextLeft.value.1
                  hclean.context_le.view.leftStarts (by
                    simpa only [SigningSpec, maskedExpandedAdversaryImpl,
                      maskedSigningImpl] using hraw)
            have htailBound := isQueryBoundP_of_bind hbound nextLeft.value.1 houtput
            simpa [leftObserve, IsOuterHash] using
              (ih nextLeft.value.1 snapshots observations canonical nextRight.context
                nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2 bound
                (htailBound.mono (by omega))
                hcanonicalRun.context_le hcanonicalRun.cache_eq hcanonicalRun.revealed_eq
                hcanonicalRun.values_le hcanonicalRun.left_published
                hcanonicalRun.right_materialized
                (canonicalizeMaterializedValues_canonical table nextLeft.context
                  hclean.context_le.view.leftConsistent)
                haligned (by omega) (by omega) (by omega)))
          convert hfinish using 1
          · rfl
          · cases rightResult <;> rfl


end SphincsSecurity.Concrete.OtsProbeSimulation
