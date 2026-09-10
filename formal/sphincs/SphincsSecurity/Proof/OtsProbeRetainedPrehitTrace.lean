import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrehitQueryTrace
import SphincsSecurity.Proof.OtsProbeQueryCutPrehit

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem runPrehitQueryTrace_cache_projection
    (accountingKey secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : ViewedFullTraceState × Bool) :
    (fun result => (result.1.1, result.1.2.1.cache)) <$> runPrehitQueryTrace accountingKey secretKey computation state =
      (simulateQ (unloggedMappedAdversaryImpl secretKey) computation).run state.1.cache := by
  rw [← encodingPrehitViewedAdversaryImpl_cache_projection accountingKey secretKey computation state,
    ← runPrehitQueryTrace_projection, Functor.map_map]

noncomputable def prehitRetainedQueryTrace
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ProbComp ((RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) := do
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  let root ← TightEncoding.runEncodingPrehitMonitor accountingKey
    (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest) :
      OracleComp OracleWorld Digest) ∅ false
  let rest ← runPrehitQueryTrace accountingKey ⟨parameter, root.1.1, otsSecret, ftsSecret⟩
    (retainedGameRestComputation adversary ⟨root.1.1, parameter⟩)
    (⟨root.1.2, ⟨[], [], []⟩, [], none⟩, root.2)
  pure (((root.1.1, rest.1.1), rest.1.2), rest.2)

theorem prehitRetainedQueryTrace_cache_projection
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (fun result => (result.1.1, result.1.2.1.cache)) <$> prehitRetainedQueryTrace adversary parameter table ftsSecret =
      actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table) := by
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  have hroot := TightEncoding.runEncodingPrehitMonitor_project accountingKey
    (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest) :
      OracleComp OracleWorld Digest) ∅ false
  rw [simulateQ_romImpl_liftM] at hroot
  unfold prehitRetainedQueryTrace actualRetainedGameAfterTable
  change _ = ((simulateQ (randomOracle : QueryImpl HashSpec _)
    (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅ >>= fun root => do
      let result ← (simulateQ (unloggedMappedAdversaryImpl ⟨parameter, root.1, otsSecret, ftsSecret⟩)
        (retainedGameRestComputation adversary ⟨root.1, parameter⟩)).run root.2
      pure ((root.1, result.1), result.2))
  rw [← hroot, bind_map_left, map_bind]
  apply bind_congr
  intro root
  simp only [map_bind, map_pure]
  have hrest := runPrehitQueryTrace_cache_projection accountingKey ⟨parameter, root.1.1, otsSecret, ftsSecret⟩
    (retainedGameRestComputation adversary ⟨root.1.1, parameter⟩) (⟨root.1.2, ⟨[], [], []⟩, [], none⟩, root.2)
  rw [← hrest, bind_map_left]

end SphincsSecurity.Concrete.OtsProbeSimulation
