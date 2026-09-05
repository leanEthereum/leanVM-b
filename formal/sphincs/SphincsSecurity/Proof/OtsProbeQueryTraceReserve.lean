import SphincsSecurity.Proof.OtsProbeQueryTraceCoupling
import SphincsSecurity.Proof.OtsProbePrehitTraceTerminal

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

namespace CanonicalQueryTraceRel

variable {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
  {left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection}
  {right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
  (hrelation : CanonicalQueryTraceRel parameter table left right)

include hrelation

theorem length_le : left.2.length ≤ right.2.length := by
  have hlength := hrelation.2.length_eq
  rw [List.length_take] at hlength
  omega

theorem selection_at (i : Fin left.2.length) :
    CanonicalQuerySelectionRel parameter table (some (left.2.get i))
      (some (right.2.get ⟨i.val, i.isLt.trans_le hrelation.length_le⟩).actual) := by
  have hbound : i.val < (right.2.take left.2.length).length := by
    rw [← hrelation.2.length_eq]
    exact i.isLt
  have hget := hrelation.2.get i.isLt hbound
  simpa only [List.get_eq_getElem, List.getElem_take] using hget

end CanonicalQueryTraceRel

set_option maxRecDepth 100000 in
theorem CanonicalQueryTraceRel.reserve_of_matching_history_roots
    {accountingKey : SecretKey} (secretKey : SecretKey) {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection}
    {right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (hrelation : CanonicalQueryTraceRel accountingKey.parameter table left right)
    (hsecrets : accountingKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (hrun : right ∈ support (runPrehitQueryTrace accountingKey secretKey computation state))
    (hfinal : right.1.2.2 = false)
    (i j : Fin left.2.length) (hij : i.val < j.val)
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hinput : (left.2.get i).input = .inl (.inr input))
    (hcandidate : EncodingLayerRootCandidateAt accountingKey.parameter input candidate)
    (hposition : candidate.coordinate = .position (layerRootPosition lay tree))
    (hvalue : (left.2.get j).context.positionValue (layerRootPosition lay tree) = some output)
    (hmatch : candidate.candidate = truncateHash output) :
    (4 / 3 : ℝ≥0∞) ≤ otsOpeningRefinedQueryReserve accountingKey
      (right.2.get ⟨i.val, i.isLt.trans_le hrelation.length_le⟩).state.1.cache input := by
  let actualI : Fin right.2.length := ⟨i.val, i.isLt.trans_le hrelation.length_le⟩
  let actualJ : Fin right.2.length := ⟨j.val, j.isLt.trans_le hrelation.length_le⟩
  have hsource := hrelation.selection_at i
  have htarget := hrelation.selection_at j
  obtain ⟨_htargetInput, _htable, hinvariant, _hvisible, _hpublished, hcomputed⟩ := htarget
  have hroot := hcomputed.root_settled_value hinvariant accountingKey.ftsSecret lay tree output hvalue
  have hsettled : Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret
      (right.2.get actualJ).state.1.cache (layerRootPosition lay tree) := by
    rw [hsecrets]
    exact hroot.1
  have hrootValue : honestValue (fromCache (right.2.get actualJ).state.1.cache)
      accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret (layerRootPosition lay tree) =
        truncateHash output := by
    rw [hsecrets]
    exact hroot.2
  have hfalse := prehitQueryTrace_entry_false_of_final_false accountingKey secretKey computation state right hrun hfinal
    (right.2.get actualJ) (List.get_mem _ _)
  have hpairs := prehitQueryTrace_pairwise_encodingReserve accountingKey secretKey computation state right hrun
  have hpair := hpairs.rel_get_of_lt (show actualI < actualJ from hij)
  exact hpair input candidate (layerRootPosition lay tree) (hsource.1.symm.trans hinput)
    hcandidate hposition hfalse hsettled (hmatch.trans hrootValue.symm)

set_option maxRecDepth 100000 in
theorem CanonicalQueryTraceRel.reserve_of_matching_final_root
    {accountingKey : SecretKey} (secretKey : SecretKey) {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection}
    {right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (hrelation : CanonicalQueryTraceRel accountingKey.parameter table left right)
    (hsecrets : accountingKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (hrun : right ∈ support (runPrehitQueryTrace accountingKey secretKey computation state))
    (hfinal : right.1.2.2 = false)
    (terminal : ResolvedRunResult (α × SplitHashCache)) (hterminal : left.1 = some terminal)
    (i : Fin left.2.length)
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hinput : (left.2.get i).input = .inl (.inr input))
    (hcandidate : EncodingLayerRootCandidateAt accountingKey.parameter input candidate)
    (hposition : candidate.coordinate = .position (layerRootPosition lay tree))
    (hvalue : terminal.context.positionValue (layerRootPosition lay tree) = some output)
    (hmatch : candidate.candidate = truncateHash output) :
    (4 / 3 : ℝ≥0∞) ≤ otsOpeningRefinedQueryReserve accountingKey
      (right.2.get ⟨i.val, i.isLt.trans_le hrelation.length_le⟩).state.1.cache input := by
  have hterminalRelation := hrelation.1
  rw [hterminal] at hterminalRelation
  obtain ⟨_htable, _hvalue, hinvariant, _hvisible, _hpublished, hcomputed⟩ := hterminalRelation
  have hroot := hcomputed.root_settled_value hinvariant accountingKey.ftsSecret lay tree output hvalue
  have hsettled : Settled accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret
      right.1.2.1.cache (layerRootPosition lay tree) := by
    rw [hsecrets]
    exact hroot.1
  have hrootValue : honestValue (fromCache right.1.2.1.cache)
      accountingKey.parameter accountingKey.otsSecret accountingKey.ftsSecret (layerRootPosition lay tree) =
        truncateHash output := by
    rw [hsecrets]
    exact hroot.2
  exact prehitQueryTrace_encodingReserve_at_final accountingKey secretKey computation state right hrun _ (List.get_mem _ _)
    input candidate (layerRootPosition lay tree) ((hrelation.selection_at i).1.symm.trans hinput)
    hcandidate hposition hfinal hsettled (hmatch.trans hrootValue.symm)

end SphincsSecurity.Concrete.OtsProbeSimulation
