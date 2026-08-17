import XmssSecurity.CappedGlobalChainHighPublicExperiment
import XmssSecurity.CappedGlobalChainHighBoundedCoupling
import XmssSecurity.CappedVerifierQueryFloor

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

noncomputable def globalHighBoundedPublicProgram
    (q : Nat) (adversary : Adversary Concrete.scheme) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex) Unit :=
  RevealProbeOracleSimulation.enforceProbeBound (q + numChains)
    (globalHighDirectPublicProgram adversary)

theorem globalHighBoundedPublicProgram_isProbeQueryBoundP
    (q : Nat) (adversary : Adversary Concrete.scheme) :
    (globalHighBoundedPublicProgram q adversary).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery (q + numChains) := by
  exact RevealProbeOracleSimulation.enforceProbeBound_isProbeQueryBoundP
    (q + numChains) (globalHighDirectPublicProgram adversary)

def HasGlobalHighBoundedPublicReduction
    (q : Nat) (adversary : Adversary Concrete.scheme) : Prop :=
  Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
    detailedGameWithKeygenCache adversary] ≤
  Pr[RevealProbeOracleSimulation.ObservedHit |
    RevealProbeOracleSimulation.eagerExperiment
      (globalHighBoundedPublicProgram q adversary)]

theorem globalWinningChainOrigin_probability_le_unboundedPublicExperiment
    (adversary : Adversary Concrete.scheme) :
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
    Pr[RevealProbeOracleSimulation.ObservedHit |
      RevealProbeOracleSimulation.eagerExperiment
        (globalHighDirectPublicProgram adversary)] := by
  apply (globalWinningChainOrigin_probability_le_publicObservedHit
    adversary).trans
  rw [show Pr[fun right : GlobalHighMonitoredProgramResult =>
      RevealProbeOracleSimulation.ObservedHit
        (globalHighMonitoredPublicProjection right) |
      globalHighMonitoredProgram adversary] =
    Pr[RevealProbeOracleSimulation.ObservedHit |
      globalHighMonitoredPublicProjection <$>
        globalHighMonitoredProgram adversary] by
      rw [probEvent_map]
      rfl]
  exact le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_globalHighMonitoredPublicProjection_eq_publicExperiment
      adversary))

def HasGlobalHighPublicEnforcement
    (q : Nat) (adversary : Adversary Concrete.scheme) : Prop :=
  Pr[RevealProbeOracleSimulation.ObservedHit |
      RevealProbeOracleSimulation.eagerExperiment
        (globalHighDirectPublicProgram adversary)] ≤
    Pr[RevealProbeOracleSimulation.ObservedHit |
      RevealProbeOracleSimulation.eagerExperiment
        (globalHighBoundedPublicProgram q adversary)]

theorem hasGlobalHighBoundedPublicReduction_of_enforcement
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (henforcement : HasGlobalHighPublicEnforcement q adversary) :
    HasGlobalHighBoundedPublicReduction q adversary :=
  (globalWinningChainOrigin_probability_le_unboundedPublicExperiment
    adversary).trans henforcement

def GlobalHighBoundedPublicObservedHit
    (q : Nat) (result : GlobalHighMonitoredProgramResult) : Prop :=
  RevealProbeOracleSimulation.ObservedHit
    (RevealProbeOracleSimulation.enforceEagerResult (q + numChains)
      (globalHighMonitoredPublicProjection result))

theorem evalDist_globalHighBoundedPublicProjection_eq_boundedExperiment
    (q : Nat) (adversary : Adversary Concrete.scheme) :
    evalDist ((RevealProbeOracleSimulation.enforceEagerResult
        (q + numChains) ∘ globalHighMonitoredPublicProjection) <$>
      globalHighMonitoredProgram adversary) =
    evalDist (RevealProbeOracleSimulation.eagerExperiment
      (globalHighBoundedPublicProgram q adversary)) := by
  unfold globalHighBoundedPublicProgram
  rw [RevealProbeOracleSimulation.eagerExperiment_enforceProbeBound_eq_map]
  have hmapped := evalDist_map_congr_of_evalDist_eq
    (RevealProbeOracleSimulation.enforceEagerResult (q + numChains))
    (globalHighMonitoredPublicProjection <$>
      globalHighMonitoredProgram adversary)
    (RevealProbeOracleSimulation.eagerExperiment
      (globalHighDirectPublicProgram adversary))
    (evalDist_globalHighMonitoredPublicProjection_eq_publicExperiment
      adversary)
  simpa [Functor.map_map, Function.comp_def] using hmapped

theorem observedProbeCount_globalForgeryPrimaryProbeTrace
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) :
    RevealProbeOracleSimulation.observedProbeCount
      (globalForgeryPrimaryProbeTrace result) = numChains := by
  have hcount : ∀ trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex,
      (∀ action ∈ trace, ∃ index target, action = .probe index target) →
      RevealProbeOracleSimulation.observedProbeCount trace = trace.length := by
    intro trace hprobes
    induction trace with
    | nil => rfl
    | cons action rest ih =>
        obtain ⟨index, target, rfl⟩ := hprobes action (by simp)
        simp only [RevealProbeOracleSimulation.observedProbeCount,
          List.length_cons, Nat.succ.injEq]
        apply ih
        intro candidate hcandidate
        exact hprobes candidate (by simp [hcandidate])
  rw [hcount]
  · unfold globalForgeryPrimaryProbeTrace
    simp [numChains]
  · intro action haction
    unfold globalForgeryPrimaryProbeTrace at haction
    simp only [List.mem_ofFn] at haction
    obtain ⟨chain, rfl⟩ := haction
    exact ⟨_, _, rfl⟩

theorem sourceGlobalHighBoundedProgramRelation_origin_implies_boundedPublicHit
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (left : SourceGlobalTracedProgramResult)
    (right : GlobalHighMonitoredProgramResult)
    (hleftSupport : left ∈ support (sourceGlobalTracedProgram adversary))
    (hrightSupport : right ∈ support (globalHighMonitoredProgram adversary))
    (hrel : SourceGlobalHighBoundedProgramRelation q (q + numChains)
      left right)
    (horigin : GlobalWinningOutcomeChainValueHasKeygenOrigin
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.1.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.1.1.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.1) :
    GlobalHighBoundedPublicObservedHit q right := by
  rcases hrel with ⟨hkey, hgoodOrHit, hconsistent⟩
  rcases hgoodOrHit with hgood | hboundedHit
  · have hunbounded := sourceGlobal_origin_implies_right_publicObservedHit
      adversary left right hleftSupport hrightSupport
        ⟨hkey, Or.inl hgood.1, hconsistent⟩ horigin
    have hcount : RevealProbeOracleSimulation.observedProbeCount
        (globalHighMonitoredPublicProjection right).2.2 ≤ q + numChains := by
      dsimp only [globalHighMonitoredPublicProjection]
      rw [RevealProbeOracleSimulation.observedProbeCount_append,
        observedProbeCount_globalForgeryPrimaryProbeTrace]
      exact Nat.add_le_add_right hgood.2 numChains
    unfold GlobalHighBoundedPublicObservedHit
    exact
      (RevealProbeOracleSimulation.observedHit_enforceEagerResult_iff_of_count_le
        (q + numChains) (globalHighMonitoredPublicProjection right) hcount).2
          hunbounded
  · unfold GlobalHighBoundedPublicObservedHit
    unfold RevealProbeOracleSimulation.ObservedHit
    dsimp only [globalHighMonitoredPublicProjection,
      RevealProbeOracleSimulation.enforceEagerResult]
    exact
      RevealProbeOracleSimulation.runObserved_enforceProbeTrace_append_eq_true_of_prefix
        right.1.1.2 AdaptiveRevealMonitor.State.empty right.2.2.1.trace
          (globalForgeryPrimaryProbeTrace
            (globalHighMonitoredErasedResult right)) (q + numChains)
              hboundedHit

theorem sourceGlobal_origin_probability_le_boundedPublicObservedHit_of_hashQueryBound
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun left : SourceGlobalTracedProgramResult =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.1.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.2.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.1.1.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.2.1 |
      sourceGlobalTracedProgram adversary] ≤
    Pr[GlobalHighBoundedPublicObservedHit q |
      globalHighMonitoredProgram adversary] := by
  apply probEvent_le_of_relTriple
    (relTriple_with_support
      (relTriple_sourceGlobal_globalHighMonitored_program_boundedHit q
        (q + numChains) adversary hbound (by omega)))
  intro left right hrel horigin
  exact
    sourceGlobalHighBoundedProgramRelation_origin_implies_boundedPublicHit q
      adversary left right hrel.2.1 hrel.2.2 hrel.1 horigin

theorem sourceGlobal_origin_probability_le_boundedPublicObservedHit_sub_keygen
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun left : SourceGlobalTracedProgramResult =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.1.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.2.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.1.1.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.2.1 |
      sourceGlobalTracedProgram adversary] ≤
    Pr[GlobalHighBoundedPublicObservedHit
        (q - treeHashQueryCount treeHeight) |
      globalHighMonitoredProgram adversary] := by
  apply probEvent_le_of_relTriple
    (relTriple_with_support
      (relTriple_sourceGlobal_globalHighMonitored_program_boundedHit_sub_keygen
        q (q - treeHashQueryCount treeHeight + numChains) adversary hbound
          (by omega)))
  intro left right hrel horigin
  exact sourceGlobalHighBoundedProgramRelation_origin_implies_boundedPublicHit
    (q - treeHashQueryCount treeHeight) adversary left right hrel.2.1
      hrel.2.2 hrel.1 horigin

theorem hasGlobalHighBoundedPublicReduction_of_monitored
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hmonitored :
      Pr[fun result =>
          GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
            result.1.1.2 result.2.1 |
        detailedGameWithKeygenCache adversary] ≤
      Pr[GlobalHighBoundedPublicObservedHit q |
        globalHighMonitoredProgram adversary]) :
    HasGlobalHighBoundedPublicReduction q adversary := by
  apply hmonitored.trans
  rw [show Pr[GlobalHighBoundedPublicObservedHit q |
      globalHighMonitoredProgram adversary] =
    Pr[RevealProbeOracleSimulation.ObservedHit |
      (RevealProbeOracleSimulation.enforceEagerResult
        (q + numChains) ∘ globalHighMonitoredPublicProjection) <$>
          globalHighMonitoredProgram adversary] by
      rw [probEvent_map]
      rfl]
  exact le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_globalHighBoundedPublicProjection_eq_boundedExperiment
      q adversary))

def HasGlobalHighBoundedHitTransfer
    (q : Nat) (adversary : Adversary Concrete.scheme) : Prop :=
  ∀ left right,
    left ∈ support (sourceGlobalTracedProgram adversary) →
    right ∈ support (globalHighMonitoredProgram adversary) →
    SourceGlobalHighMonitoredProgramRelation left right →
    GlobalWinningOutcomeChainValueHasKeygenOrigin
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.1.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.1.1.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.1 →
    GlobalHighBoundedPublicObservedHit q right

theorem sourceGlobal_origin_probability_le_boundedPublicObservedHit
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (htransfer : HasGlobalHighBoundedHitTransfer q adversary) :
    Pr[fun left : SourceGlobalTracedProgramResult =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.1.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.2.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.1.1.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.2.1 |
      sourceGlobalTracedProgram adversary] ≤
    Pr[GlobalHighBoundedPublicObservedHit q |
      globalHighMonitoredProgram adversary] := by
  apply probEvent_le_of_relTriple
    (relTriple_with_support
      (relTriple_sourceGlobal_globalHighMonitored_program adversary))
  intro left right hrel horigin
  exact htransfer left right hrel.2.1 hrel.2.2 hrel.1 horigin

theorem globalWinningChainOrigin_probability_le_boundedPublicObservedHit
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (htransfer : HasGlobalHighBoundedHitTransfer q adversary) :
    Pr[fun result =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
          result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
    Pr[GlobalHighBoundedPublicObservedHit q |
      globalHighMonitoredProgram adversary] := by
  calc
    _ = Pr[fun result =>
          GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.1.2
            result.1.2.2 result.1.1.1.2 result.1.2.1 |
        detailedGameWithKeygenCacheAndActionTrace adversary] := by
      rw [← detailedGameWithKeygenCacheAndActionTrace_projection,
        probEvent_map]
      rfl
    _ = Pr[fun left : SourceGlobalTracedProgramResult =>
          GlobalWinningOutcomeChainValueHasKeygenOrigin
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.1.2
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.2.2
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.1.1.2
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.2.1 |
        sourceGlobalTracedProgram adversary] := by
      let event := fun result :
          ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
            (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.1.2
          result.1.2.2 result.1.1.1.2 result.1.2.1
      let project := fun left : SourceGlobalTracedProgramResult =>
        eraseGlobalChainKeygenView (sourceGlobalProgramResult left)
      change Pr[event | detailedGameWithKeygenCacheAndActionTrace adversary] =
        Pr[event ∘ project | sourceGlobalTracedProgram adversary]
      rw [← probEvent_map]
      exact probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_sourceGlobalErased_eq_originalActionTraced adversary).symm
    _ ≤ _ := sourceGlobal_origin_probability_le_boundedPublicObservedHit
      q adversary htransfer

theorem hasGlobalHighBoundedPublicReduction_of_hitTransfer
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (htransfer : HasGlobalHighBoundedHitTransfer q adversary) :
    HasGlobalHighBoundedPublicReduction q adversary :=
  hasGlobalHighBoundedPublicReduction_of_monitored q adversary
    (globalWinningChainOrigin_probability_le_boundedPublicObservedHit
      q adversary htransfer)

theorem globalWinningChainOrigin_probability_le_boundedPublicObservedHit_of_hashQueryBound
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun result =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
          result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
    Pr[GlobalHighBoundedPublicObservedHit q |
      globalHighMonitoredProgram adversary] := by
  calc
    _ = Pr[fun result =>
          GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.1.2
            result.1.2.2 result.1.1.1.2 result.1.2.1 |
        detailedGameWithKeygenCacheAndActionTrace adversary] := by
      rw [← detailedGameWithKeygenCacheAndActionTrace_projection,
        probEvent_map]
      rfl
    _ = Pr[fun left : SourceGlobalTracedProgramResult =>
          GlobalWinningOutcomeChainValueHasKeygenOrigin
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.1.2
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.2.2
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.1.1.2
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.2.1 |
        sourceGlobalTracedProgram adversary] := by
      let event := fun result :
          ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
            (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.1.2
          result.1.2.2 result.1.1.1.2 result.1.2.1
      let project := fun left : SourceGlobalTracedProgramResult =>
        eraseGlobalChainKeygenView (sourceGlobalProgramResult left)
      change Pr[event | detailedGameWithKeygenCacheAndActionTrace adversary] =
        Pr[event ∘ project | sourceGlobalTracedProgram adversary]
      rw [← probEvent_map]
      exact probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_sourceGlobalErased_eq_originalActionTraced adversary).symm
    _ ≤ _ :=
      sourceGlobal_origin_probability_le_boundedPublicObservedHit_of_hashQueryBound
        q adversary hbound

theorem globalWinningChainOrigin_probability_le_boundedPublicObservedHit_sub_keygen
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun result =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
          result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
    Pr[GlobalHighBoundedPublicObservedHit
        (q - treeHashQueryCount treeHeight) |
      globalHighMonitoredProgram adversary] := by
  calc
    _ = Pr[fun result =>
          GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.1.2
            result.1.2.2 result.1.1.1.2 result.1.2.1 |
        detailedGameWithKeygenCacheAndActionTrace adversary] := by
      rw [← detailedGameWithKeygenCacheAndActionTrace_projection,
        probEvent_map]
      rfl
    _ = Pr[fun left : SourceGlobalTracedProgramResult =>
          GlobalWinningOutcomeChainValueHasKeygenOrigin
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.1.2
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.2.2
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.1.1.2
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.2.1 |
        sourceGlobalTracedProgram adversary] := by
      let event := fun result :
          ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
            (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.1.2
          result.1.2.2 result.1.1.1.2 result.1.2.1
      let project := fun left : SourceGlobalTracedProgramResult =>
        eraseGlobalChainKeygenView (sourceGlobalProgramResult left)
      change Pr[event | detailedGameWithKeygenCacheAndActionTrace adversary] =
        Pr[event ∘ project | sourceGlobalTracedProgram adversary]
      rw [← probEvent_map]
      exact probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_sourceGlobalErased_eq_originalActionTraced adversary).symm
    _ ≤ _ := sourceGlobal_origin_probability_le_boundedPublicObservedHit_sub_keygen
      q adversary hbound

theorem hasGlobalHighBoundedPublicReduction_of_hashQueryBound
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    HasGlobalHighBoundedPublicReduction q adversary :=
  hasGlobalHighBoundedPublicReduction_of_monitored q adversary
    (globalWinningChainOrigin_probability_le_boundedPublicObservedHit_of_hashQueryBound
      q adversary hbound)

theorem hasGlobalHighBoundedPublicReduction_of_hashQueryBound_sub_keygen
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    HasGlobalHighBoundedPublicReduction
      (q - treeHashQueryCount treeHeight) adversary :=
  hasGlobalHighBoundedPublicReduction_of_monitored
    (q - treeHashQueryCount treeHeight) adversary
      (globalWinningChainOrigin_probability_le_boundedPublicObservedHit_sub_keygen
        q adversary hbound)

theorem globalWinningChainOrigin_probability_le_q_add_numChains
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hreduction : HasGlobalHighBoundedPublicReduction q adversary) :
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
      ((q + numChains : Nat) : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  exact hreduction.trans
    (RevealProbeOracleSimulation.eagerExperiment_observedHit_probability_le
      (q + numChains) (globalHighBoundedPublicProgram q adversary)
      (globalHighBoundedPublicProgram_isProbeQueryBoundP q adversary))

theorem globalWinningChainOrigin_probability_le_sub_keygen_add_numChains
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
      ((q - treeHashQueryCount treeHeight + numChains : Nat) : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal) :=
  globalWinningChainOrigin_probability_le_q_add_numChains
    (q - treeHashQueryCount treeHeight) adversary
      (hasGlobalHighBoundedPublicReduction_of_hashQueryBound_sub_keygen
        q adversary hbound)

theorem globalWinningChainOrigin_probability_le_two_queries
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (hreduction : HasGlobalHighBoundedPublicReduction q adversary) :
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
      2 * ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
  apply (globalWinningChainOrigin_probability_le_q_add_numChains q adversary
    hreduction).trans
  have hfloor := hashQueryBound_at_least_numChains adversary q hbound
  have hcast : ((q + numChains : Nat) : ENNReal) ≤ 2 * (q : ENNReal) := by
    exact_mod_cast (show q + numChains ≤ 2 * q by omega)
  rw [div_eq_mul_inv]
  calc
    ((q + numChains : Nat) : ENNReal) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
      (2 * (q : ENNReal)) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by gcongr
    _ = 2 * ((q : ENNReal) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by ring

end XmssSecurity.CappedChain
