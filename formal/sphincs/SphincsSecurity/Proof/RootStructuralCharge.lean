import SphincsSecurity.Proof.HonestStructuralCharge
import SphincsSecurity.Proof.HashQueryCutCharge
import SphincsSecurity.Proof.StoppedParentGame

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation
set_option backward.isDefEq.respectTransparency false

theorem expectedQueryCharge_treeRoot_eq_zero
    (secretKey : SecretKey) (lay : Layer) (tree : TreeIndex) (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun cache input => parentStoppedEncodingQueryCharge secretKey cache input +
      ftsParentQueryCharge secretKey cache input)
      (liftM (treeRoot secretKey.parameter lay tree (secretKey.otsSecret lay tree) : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) cache = 0 := by
  apply expectedQueryCharge_lift_eq_zero_of_supported_cuts
  intro ordinal middleCache input next hcut
  exact structuralCharge_eq_zero_at_supported_honest_query secretKey _
    (fun f => settlingRun_treeRoot secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f lay tree)
    (fun f => honestStructuralQueries_treeRoot secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f lay tree)
    ordinal cache middleCache input next hcut

theorem expectedPreExceptionCharge_treeRoot_eq_zero
    (secretKey : SecretKey) (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (lay : Layer) (tree : TreeIndex) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (fun cache input => parentStoppedEncodingQueryCharge secretKey cache input +
      ftsParentQueryCharge secretKey cache input)
      (liftM (treeRoot secretKey.parameter lay tree (secretKey.otsSecret lay tree) : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) cache hit = 0 := by
  apply le_antisymm _ bot_le
  exact (expectedPreExceptionCharge_le_queryCharge exception _ _ cache hit).trans_eq
    (expectedQueryCharge_treeRoot_eq_zero secretKey lay tree cache)

theorem runExceptionMonitor_treeRoot_empty
    (secretKey : SecretKey) (lay : Layer) (tree : TreeIndex) :
    runExceptionMonitor (CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
      (liftM (treeRoot secretKey.parameter lay tree (secretKey.otsSecret lay tree) : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) ∅ false =
      (fun result => (result, false)) <$>
        (simulateQ romImpl (liftM (treeRoot secretKey.parameter lay tree (secretKey.otsSecret lay tree) : OracleComp HashSpec Digest) :
          OracleComp OracleWorld Digest)).run ∅ := by
  let exception := CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
  let computation : OracleComp OracleWorld Digest := liftM (treeRoot secretKey.parameter lay tree (secretKey.otsSecret lay tree) : OracleComp HashSpec Digest)
  change runExceptionMonitor exception computation ∅ false = _
  have hflag := runFirstException_flag_projection exception computation ∅ none
  simp only [Option.isSome_none] at hflag
  rw [← hflag, ← runFirstException_project exception computation ∅ none, Functor.map_map]
  simp only [map_eq_bind_pure_comp]
  apply _root_.OracleComp.bind_congr_of_forall_mem_support
  intro result hresult
  have hnone := runFirstException_treeRoot_no_record secretKey exception (fun _ _ _ h => h.2) lay tree hresult
  simp only [Function.comp_apply, hnone, Option.isSome_none]

theorem preParentStructuralCharge_retained_eq_afterRoot
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
    expectedPreExceptionCharge (CleanParentSettlement parameter otsSecret ftsSecret)
      (fun cache input => parentStoppedEncodingQueryCharge accountingKey cache input + ftsParentQueryCharge accountingKey cache input)
      (OtsProbeSimulation.retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ false =
      ∑' result, Pr[= result | (simulateQ romImpl
        (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest)).run ∅] *
        expectedPreExceptionCharge (CleanParentSettlement parameter otsSecret ftsSecret)
          (fun cache input => parentStoppedEncodingQueryCharge accountingKey cache input + ftsParentQueryCharge accountingKey cache input)
          (simulateQ (expandedAdversaryImpl ⟨parameter, result.1, otsSecret, ftsSecret⟩)
            (retainedGameRestComputation adversary ⟨result.1, parameter⟩)) result.2 false := by
  dsimp only
  have hzero := expectedPreExceptionCharge_treeRoot_eq_zero (primitiveAccountingKey parameter otsSecret ftsSecret)
    (CleanParentSettlement parameter otsSecret ftsSecret) topLayer rootTree ∅ false
  have hroot := runExceptionMonitor_treeRoot_empty (primitiveAccountingKey parameter otsSecret ftsSecret) topLayer rootTree
  simp only [primitiveAccountingKey] at hzero hroot
  simp only [primitiveAccountingKey]
  rw [OtsProbeSimulation.retainedAfterSecretsComputation, expectedPreExceptionCharge_bind, hzero, zero_add,
    hroot, tsum_probOutput_map_mul]
  apply tsum_congr
  intro result
  rw [bind_pure_comp, expectedPreExceptionCharge_map]

theorem sampledPreParentStructuralCharge_eq_afterRoot (adversary : Adversary) :
    sampledPreParentQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
      ftsParentQueryCharge secretKey cache input) adversary =
      ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        ∑' result, Pr[= result | (simulateQ romImpl
          (liftM (treeRoot secrets.parameter topLayer rootTree (secrets.otsSecret topLayer rootTree) : OracleComp HashSpec Digest) :
            OracleComp OracleWorld Digest)).run ∅] *
          expectedPreExceptionCharge (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
            (fun cache input => parentStoppedEncodingQueryCharge
                (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret) cache input +
              ftsParentQueryCharge (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret) cache input)
            (simulateQ (expandedAdversaryImpl ⟨secrets.parameter, result.1, secrets.otsSecret, secrets.ftsSecret⟩)
              (retainedGameRestComputation adversary ⟨result.1, secrets.parameter⟩)) result.2 false := by
  rw [sampledPreParentQueryCharge_eq_retained]
  apply tsum_congr
  intro secrets
  rw [preParentStructuralCharge_retained_eq_afterRoot]

end SphincsSecurity.Concrete
