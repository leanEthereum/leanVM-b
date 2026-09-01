import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRoot

/-!
# Comparison-root exception for stopped layer roots

The successful diagnostic prefix avoids the actual selected root. The independent comparison root
used by the exchangeable root experiment can still equal an earlier candidate. This file isolates
that exception and keeps its probability proportional to the production mass of the selected root
fiber.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def snapshotPrefixCandidateDigests
    (ordinal : Nat) (source : PrivateWitnessSnapshotOutput) : List Digest :=
  (source.2.take ordinal).map fun snapshot => snapshot.probe.candidate

def SelectedPrivateSnapshotCleanRootComparisonExceptionAt
    (table : OtsSecretIndex → HashOutput)
    (source : PrivateWitnessSnapshotOutput) (ordinal : Nat)
    (target : Position) (rightRoot : Digest) : Prop :=
  ∃ selected : Fin source.2.length, ∃ output,
    selected.val = ordinal ∧
    selectedPrivateSnapshotOrdinal? ordinal source.2 =
      some (privateOrdinalSelectionOfSnapshot selected) ∧
    (privateOrdinalSelectionOfSnapshot selected).GoodForActualRoot target output ordinal ∧
    IsLayerRoot target ∧
    SnapshotsAvoidExistingHiddenPositionHits table (source.2.take ordinal) ∧
    ¬CandidatesAvoidRoot target rightRoot
      ((privateOrdinalSelectionOfSnapshot selected).candidates.take ordinal)

def SelectedPrivateSnapshotCleanRootGoodForComparisonAt
    (table : OtsSecretIndex → HashOutput)
    (source : PrivateWitnessSnapshotOutput) (ordinal : Nat)
    (target : Position) (rightRoot : Digest) : Prop :=
  ∃ selected : Fin source.2.length, ∃ output,
    selected.val = ordinal ∧
    selectedPrivateSnapshotOrdinal? ordinal source.2 =
      some (privateOrdinalSelectionOfSnapshot selected) ∧
    (privateOrdinalSelectionOfSnapshot selected).GoodForActualRoot target output ordinal ∧
    IsLayerRoot target ∧
    SnapshotsAvoidExistingHiddenPositionHits table (source.2.take ordinal) ∧
    CandidatesAvoidRoot target rightRoot
      ((privateOrdinalSelectionOfSnapshot selected).candidates.take ordinal)

theorem SelectedPrivateSnapshotCleanRootGoodForComparisonAt.goodForRoots
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    {target : Position} {rightRoot : Digest}
    (hgood : SelectedPrivateSnapshotCleanRootGoodForComparisonAt
      table source ordinal target rightRoot) :
    ∃ selected : Fin source.2.length, ∃ output,
      selected.val = ordinal ∧
      selectedPrivateSnapshotOrdinal? ordinal source.2 =
        some (privateOrdinalSelectionOfSnapshot selected) ∧
      (privateOrdinalSelectionOfSnapshot selected).GoodForRoots
        target output rightRoot ordinal := by
  obtain ⟨selected, output, hordinal, hselection, hactual, _hroot, _hclean, hright⟩ := hgood
  exact ⟨selected, output, hordinal, hselection, hactual.goodForRoots hright⟩

theorem SelectedPrivateSnapshotCleanRootComparisonExceptionAt.cleanRootHit
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    {target : Position} {rightRoot : Digest}
    (hexception : SelectedPrivateSnapshotCleanRootComparisonExceptionAt
      table source ordinal target rightRoot) :
    SelectedPrivateSnapshotCleanRootHitAt table source ordinal := by
  obtain ⟨selected, output, hordinal, hselection, hgood, hroot, hclean, _hcomparison⟩ :=
    hexception
  exact ⟨selected, target, output, hordinal, hselection, hgood, hroot, hclean⟩

theorem SelectedPrivateSnapshotCleanRootComparisonExceptionAt.position
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    {target : Position} {rightRoot : Digest}
    (hexception : SelectedPrivateSnapshotCleanRootComparisonExceptionAt
      table source ordinal target rightRoot) :
    selectedPrivateSnapshotLayerRootPosition? ordinal source = some target := by
  obtain ⟨selected, output, hordinal, _hselection, hgood, hroot, _hclean, _hcomparison⟩ :=
    hexception
  unfold selectedPrivateSnapshotLayerRootPosition?
  have hlt : ordinal < source.2.length := by rw [← hordinal]; exact selected.isLt
  rw [dif_pos hlt, candidateLayerRootPosition?_eq_some_iff]
  have hindex : (⟨ordinal, hlt⟩ : Fin source.2.length) = selected := Fin.ext hordinal.symm
  rw [hindex]
  have hcandidate := hgood.1
  rw [privateOrdinalSelectionOfSnapshot_candidate] at hcandidate
  have hcandidate' : (source.2.get selected).probe =
      ⟨.position target, truncateHash output⟩ := by
    simpa [snapshotProbeOrdinal] using hcandidate
  exact ⟨congrArg Probe.coordinate hcandidate', hroot⟩

theorem not_candidatesAvoidRoot_mem_candidate_map
    {target : Position} {root : Digest} {candidates : List Probe}
    (havoid : ¬CandidatesAvoidRoot target root candidates) :
    root ∈ candidates.map Probe.candidate := by
  classical
  by_contra hmem
  apply havoid
  intro candidate hcandidate heq
  apply hmem
  rw [List.mem_map]
  exact ⟨candidate, hcandidate, by rw [heq]⟩

theorem SelectedPrivateSnapshotCleanRootComparisonExceptionAt.comparison_mem
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    {target : Position} {rightRoot : Digest}
    (hexception : SelectedPrivateSnapshotCleanRootComparisonExceptionAt
      table source ordinal target rightRoot) :
    rightRoot ∈ snapshotPrefixCandidateDigests ordinal source := by
  obtain ⟨selected, _output, hordinal, _hselection, _hgood, _hroot, _hclean,
    hcomparison⟩ := hexception
  have hmem := not_candidatesAvoidRoot_mem_candidate_map hcomparison
  unfold snapshotPrefixCandidateDigests
  rw [← hordinal] at hmem ⊢
  rw [privateOrdinalSelectionOfSnapshot_candidates_take] at hmem
  simpa [List.map_take, Function.comp_def] using hmem

theorem probEvent_cleanRootFiber_comparisonException_le
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp PrivateWitnessSnapshotOutput) (ordinal : Nat) (target : Position) :
    Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
        SelectedPrivateSnapshotCleanRootComparisonExceptionAt
          table result.1 ordinal target result.2 | do
      let source ← run
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (source, rightRoot)] ≤
      Pr[fun source => SelectedPrivateSnapshotCleanRootHitAt table source ordinal ∧
          selectedPrivateSnapshotLayerRootPosition? ordinal source = some target | run] *
        ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  let gate := fun source : PrivateWitnessSnapshotOutput =>
    SelectedPrivateSnapshotCleanRootHitAt table source ordinal ∧
      selectedPrivateSnapshotLayerRootPosition? ordinal source = some target
  let values := snapshotPrefixCandidateDigests ordinal
  calc
    _ ≤ Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
          gate result.1 ∧ result.2 ∈ values result.1 | do
        let source ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)] := by
      apply probEvent_mono
      intro result _hresult hexception
      exact ⟨⟨hexception.cleanRootHit, hexception.position⟩, hexception.comparison_mem⟩
    _ ≤ Pr[gate | run] *
          ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
      apply probEvent_gate_and_uniformDigest_mem_list_le run gate values ordinal
      intro source _hsource _hgate
      unfold values snapshotPrefixCandidateDigests
      simp
    _ = _ := rfl

theorem relTriple_pair_uniform_right
    (run : ProbComp α) [SampleableType β] :
    RelTriple run (do
      let value ← run
      let sampled ← ($ᵗ β : ProbComp β)
      pure (value, sampled)) (fun value result => value = result.1) := by
  apply relTriple_of_evalDist_eq_left
    (show evalDist run = evalDist (run >>= pure) by simp)
  apply relTriple_bind (relTriple_refl run)
  intro left right heq
  subst right
  have hbase := relTriple_true (pure left : ProbComp α) (do
    let sampled ← ($ᵗ β : ProbComp β)
    pure (left, sampled))
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value => value = left) (by intro value hvalue; simpa using hvalue)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro value result hrelation
  rw [hrelation.1.2]
  rw [mem_support_bind_iff] at hrelation
  obtain ⟨sampled, _hsampled, hresult⟩ := hrelation.2
  symm
  simpa using congrArg Prod.fst (show result = (left, sampled) by simpa using hresult)

theorem cleanRootFiber_split_comparison
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    {target : Position} {rightRoot : Digest}
    (hhit : SelectedPrivateSnapshotCleanRootHitAt table source ordinal)
    (hposition : selectedPrivateSnapshotLayerRootPosition? ordinal source = some target) :
    SelectedPrivateSnapshotCleanRootGoodForComparisonAt
        table source ordinal target rightRoot ∨
      SelectedPrivateSnapshotCleanRootComparisonExceptionAt
        table source ordinal target rightRoot := by
  obtain ⟨selected, sourceTarget, output, hordinal, hselection, hactual, hroot, hclean⟩ := hhit
  have htarget : sourceTarget = target := by
    have hsourcePosition :
        selectedPrivateSnapshotLayerRootPosition? ordinal source = some sourceTarget := by
      unfold selectedPrivateSnapshotLayerRootPosition?
      have hlt : ordinal < source.2.length := by rw [← hordinal]; exact selected.isLt
      rw [dif_pos hlt, candidateLayerRootPosition?_eq_some_iff]
      have hindex : (⟨ordinal, hlt⟩ : Fin source.2.length) = selected :=
        Fin.ext hordinal.symm
      rw [hindex]
      have hcandidate := hactual.1
      rw [privateOrdinalSelectionOfSnapshot_candidate] at hcandidate
      have hcandidate' : (source.2.get selected).probe =
          ⟨.position sourceTarget, truncateHash output⟩ := by
        simpa [snapshotProbeOrdinal] using hcandidate
      exact ⟨congrArg Probe.coordinate hcandidate', hroot⟩
    rw [hposition] at hsourcePosition
    exact (Option.some.inj hsourcePosition).symm
  subst sourceTarget
  by_cases hright : CandidatesAvoidRoot target rightRoot
      ((privateOrdinalSelectionOfSnapshot selected).candidates.take ordinal)
  · exact Or.inl ⟨selected, output, hordinal, hselection, hactual, hroot, hclean, hright⟩
  · exact Or.inr ⟨selected, output, hordinal, hselection, hactual, hroot, hclean, hright⟩

theorem probEvent_cleanRootFiber_le_goodComparison_add_exception
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp PrivateWitnessSnapshotOutput) (ordinal : Nat) (target : Position) :
    Pr[fun source => SelectedPrivateSnapshotCleanRootHitAt table source ordinal ∧
        selectedPrivateSnapshotLayerRootPosition? ordinal source = some target | run] ≤
      Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
          SelectedPrivateSnapshotCleanRootGoodForComparisonAt
            table result.1 ordinal target result.2 | do
        let source ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)] +
      Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
          SelectedPrivateSnapshotCleanRootComparisonExceptionAt
            table result.1 ordinal target result.2 | do
        let source ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)] := by
  let paired : ProbComp (PrivateWitnessSnapshotOutput × Digest) := do
    let source ← run
    let rightRoot ← ($ᵗ Digest : ProbComp Digest)
    pure (source, rightRoot)
  calc
    _ ≤ Pr[fun result => SelectedPrivateSnapshotCleanRootHitAt table result.1 ordinal ∧
          selectedPrivateSnapshotLayerRootPosition? ordinal result.1 = some target | paired] := by
      apply probEvent_le_of_relTriple (relTriple_pair_uniform_right run)
      intro source result hrelation hevent
      rwa [← hrelation]
    _ ≤ Pr[fun result =>
          SelectedPrivateSnapshotCleanRootGoodForComparisonAt
              table result.1 ordinal target result.2 ∨
            SelectedPrivateSnapshotCleanRootComparisonExceptionAt
              table result.1 ordinal target result.2 | paired] := by
      apply probEvent_mono
      intro result _hresult hevent
      exact cleanRootFiber_split_comparison hevent.1 hevent.2
    _ ≤ _ := probEvent_or_le _ _ _

theorem probEvent_cleanRootFiber_le_goodComparison_add_weighted_exception
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp PrivateWitnessSnapshotOutput) (ordinal : Nat) (target : Position) :
    Pr[fun source => SelectedPrivateSnapshotCleanRootHitAt table source ordinal ∧
        selectedPrivateSnapshotLayerRootPosition? ordinal source = some target | run] ≤
      Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
          SelectedPrivateSnapshotCleanRootGoodForComparisonAt
            table result.1 ordinal target result.2 | do
        let source ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)] +
      Pr[fun source => SelectedPrivateSnapshotCleanRootHitAt table source ordinal ∧
          selectedPrivateSnapshotLayerRootPosition? ordinal source = some target | run] *
        ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  exact (probEvent_cleanRootFiber_le_goodComparison_add_exception table run ordinal target).trans
    (add_le_add_right
      (probEvent_cleanRootFiber_comparisonException_le table run ordinal target) _)

def privateOrdinalSelectionGoodForSomeOutput
    (target : Position) (rightRoot : Digest) (ordinal : Nat) :
    Option PrivateOrdinalSelection → Prop
  | none => False
  | some selection => ∃ output,
      selection.GoodForRoots target output rightRoot ordinal

theorem relTriple_snapshotComparison_privateOrdinalSelectionComparison
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple
      (do
        let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
          ftsSecret fuel
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot))
      (do
        let selection ← granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter
          table ftsSecret fuel
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (selection, rightRoot))
      (fun left right =>
        SnapshotOrdinalSelectionRel ordinal left.1 right.1 ∧ left.2 = right.2) := by
  apply relTriple_bind
    (relTriple_granularAllCanonicalSnapshot_privateOrdinalSelection ordinal adversary parameter
      table ftsSecret fuel)
  intro source selection hselection
  apply relTriple_bind (relTriple_refl ($ᵗ Digest : ProbComp Digest))
  intro leftRoot rightRoot hroot
  subst rightRoot
  exact relTriple_pure_pure ⟨hselection, rfl⟩

theorem probEvent_goodComparison_le_privateOrdinalSelection
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) :
    Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
        SelectedPrivateSnapshotCleanRootGoodForComparisonAt
          table result.1 ordinal target result.2 | do
      let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
        ftsSecret fuel
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (source, rightRoot)] ≤
      Pr[fun result : Option PrivateOrdinalSelection × Digest =>
          privateOrdinalSelectionGoodForSomeOutput target result.2 ordinal result.1 | do
        let selection ← granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter
          table ftsSecret fuel
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (selection, rightRoot)] := by
  apply probEvent_le_of_relTriple
    (relTriple_snapshotComparison_privateOrdinalSelectionComparison ordinal adversary parameter
      table ftsSecret fuel)
  intro source selection hrelation hgood
  obtain ⟨selected, output, _hordinal, hselected, hactual⟩ := hgood.goodForRoots
  have hselection : selection.1 =
      some (privateOrdinalSelectionOfSnapshot selected) := by
    exact hrelation.1.symm.trans hselected
  rw [hselection]
  exact ⟨output, by simpa [hrelation.2] using hactual⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
