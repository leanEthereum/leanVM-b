import SphincsSecurity.Proof.OtsProbeEarlyParentQuery
import SphincsSecurity.Proof.OtsProbeNativeRetainedProjection
import SphincsSecurity.Proof.OtsProbeNativeRateBound

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

private theorem relTriple_empty_trace_earlyParent
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (right : ProbComp ((β × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)) :
    RelTriple (pure (none, []) : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection))
      right (fun left right => EarlyOtsParentAtQuery parameter
        (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret right →
        left.1 = none) := by
  have h := relTriple_true
    (pure (none, []) : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)) right
  have hs := FtsProbeSimulation.relTriple_and_left_support h (fun left => left.1 = none) (by
    intro left hleft
    have heq : left = (none, []) := by simpa using hleft
    exact congrArg Prod.fst heq)
  exact relTriple_post_mono hs (fun _ _ hrel _ => hrel.2)

theorem relTriple_nativeAfterRoot_prehit_earlyParent
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple (nativeChainTraceAfterRoot targets parameter table ftsSecret fuel
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩))
      (prehitRetainedQueryTrace adversary parameter table ftsSecret)
      (fun left right => EarlyOtsParentAtQuery parameter
        (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret right →
        left.1 = none) := by
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table (ensuredInitialContext targets)
    fuel emptySplitHashCache ∅ (ensuredInitialContext_resolvedInvariant targets parameter table)
    (ensuredInitialContext_visible targets parameter table) (ensuredInitialContext_published targets)
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hroot
    (fun left => ∀ result, left = some result → DeferredComputationsClosed result.context) (by
      intro left hleft result heq
      subst left
      exact (ensuredInitialContext_computed targets).of_mem_runResolved _ _ fuel table result hleft)
  have hprojection := TightEncoding.runEncodingPrehitMonitor_project accountingKey
    (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest) :
      OracleComp OracleWorld Digest) ∅ false
  rw [simulateQ_romImpl_liftM] at hprojection
  have hmonitor := relTriple_of_evalDist_map_eq_general
    ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅)
    (TightEncoding.runEncodingPrehitMonitor accountingKey
      (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest) :
        OracleComp OracleWorld Digest) ∅ false)
    id Prod.fst (by simpa only [id_map] using congrArg evalDist hprojection.symm)
  unfold nativeChainTraceAfterRoot prehitRetainedQueryTrace
  apply relTriple_bind (relTriple_trans_exists hsupported hmonitor)
  rintro leftRoot rightRoot ⟨actualRoot, hrelation, heq⟩
  have hbase : ReachableResolvedRunRel parameter table leftRoot rightRoot.1 := heq ▸ hrelation.1
  cases leftRoot with
  | none => exact relTriple_empty_trace_earlyParent parameter table ftsSecret _
  | some result =>
      have hcomputed := hrelation.2 result rfl
      dsimp only
      rcases hbase with hclean | hdoomed
      · rw [hclean.1, ← hclean.2.1]
        have htrace := relTriple_nativeQueryTrace_prehit_earlyParent parameter result.value.1 table ftsSecret accountingKey
          (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) result.context result.remaining result.value.2
          (⟨rightRoot.1.2, ⟨[], [], []⟩, [], none⟩, rightRoot.2)
          hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 hcomputed
        have hmap := relTriple_map
          (R := fun (left : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache)) × List CanonicalQuerySelection)
            (right : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) =>
            EarlyOtsParentAtQuery parameter otsSecret ftsSecret right → left.1 = none)
          (f := id)
          (g := fun rest : (RetainedRestResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot =>
            (((result.value.1, rest.1.1), rest.1.2), rest.2)) htrace
        simpa only [id_map, map_eq_bind_pure_comp, Function.comp_def, id_eq, bind_pure, EarlyOtsParentAtQuery] using hmap
      · rw [runNativeQueryTrace_of_not_completable parameter result.value.1 ftsSecret _
          result.context result.remaining result.table result.value.2 (by rw [hdoomed.1]; exact hdoomed.2.2.2)]
        exact relTriple_empty_trace_earlyParent parameter table ftsSecret _

theorem probEvent_earlyOtsParentAtQuery_le_nativeTerminalFailure
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[EarlyOtsParentAtQuery parameter
      (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret |
      prehitRetainedQueryTrace adversary parameter table ftsSecret] ≤
      Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot targets adversary parameter table ftsSecret fuel] := by
  apply (probEvent_le_of_relTriple
    (relTriple_symm (relTriple_nativeAfterRoot_prehit_earlyParent targets adversary parameter table ftsSecret fuel))
    (fun _ _ hrel hearly => hrel hearly)).trans
  rw [nativeTerminalFailureAfterRoot, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro trace
  by_cases hnone : trace.1 = none
  · rw [if_pos hnone, hnone]
    simp [finishResolvedRunIsNone, finishResolvedRun]
  · simp [hnone]

noncomputable def sampledEarlyOtsParentQueryRisk (adversary : Adversary) : ℝ≥0∞ :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | sampleOtsHashTable] *
        Pr[EarlyOtsParentAtQuery parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret |
          prehitRetainedQueryTrace adversary parameter table ftsSecret]

theorem sampledEarlyOtsParentQueryRisk_le_nativeTerminalFailure
    (adversary : Adversary) (fuel : Nat) :
    sampledEarlyOtsParentQueryRisk adversary ≤
      Pr[fun verdict => verdict = true | sampledNativeTerminalFailure adversary fuel] := by
  simp only [sampledEarlyOtsParentQueryRisk, sampledNativeTerminalFailure, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  exact mul_le_mul' le_rfl
    (probEvent_earlyOtsParentAtQuery_le_nativeTerminalFailure Finset.univ adversary parameter table ftsSecret fuel)

theorem sampledEarlyOtsParentQueryRisk_le_actualOtsCount_rate_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqSpace : q + 1 < Fintype.card Digest) :
    sampledEarlyOtsParentQueryRisk adversary ≤
      sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        privateHistoryGuessRate q + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (sampledEarlyOtsParentQueryRisk_le_nativeTerminalFailure adversary (q + 1)).trans
  rw [probEvent_sampledNativeTerminalFailure_eq_risk]
  exact sampledNativeTerminalRisk_le_actualOtsCount_rate_add_erasure_of_querySpace adversary q hq hqSpace

theorem sampledEarlyOtsParentQueryRisk_le_actualOtsCount127_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    sampledEarlyOtsParentQueryRisk adversary ≤
      sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        (2 * (Fintype.card Digest : ENNReal)⁻¹) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (sampledEarlyOtsParentQueryRisk_le_actualOtsCount_rate_add_erasure adversary q hq (by
    have hspace : 2 ^ 127 + 1 < Fintype.card Digest := by norm_num [digestBits]
    omega)).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul' le_rfl
  simpa only [show Fintype.card Digest = 2 ^ digestBits by simp] using privateHistoryGuessRate_le_two hqMax

end SphincsSecurity.Concrete.OtsProbeSimulation
