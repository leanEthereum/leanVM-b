import SphincsSecurity.Proof.JointProbeResolvedExecution
import SphincsSecurity.Proof.OtsProbeStartErasureBound
import SphincsSecurity.Proof.PreExceptionChargeComparison

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (OtsSecretIndex ResolvedRunResult)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def JointOriginalRunRel (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput)
    (ftsTable : Coordinate → Digest)
    (left : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache))))
    (right : α × QueryCache HashSpec) : Prop :=
  left.hit = true ∨ OtsProbeSimulation.ReachableResolvedRunRel parameter otsTable
    (projectJointResolvedCache parameter ftsTable left) right

theorem relTriple_jointResolvedComputation_original
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (cache : JointSourceCache) (actualCache : QueryCache HashSpec)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash ftsFuel)
    (hclean : AdaptiveRevealProbe.tableHits state ftsTable = false)
    (hsynced : RevealedSynced parameter ftsTable state cache.2)
    (hinvariant : OtsProbeSimulation.ResolvedContextInvariant parameter otsTable context
      (mergedCache parameter ftsTable cache.2) actualCache)
    (hvisible : OtsProbeSimulation.VisibleResolvedComputationsCached parameter otsTable context actualCache)
    (hpublished : OtsProbeSimulation.PublishedValues context.state) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (otsTable ⟨lay, tree, leafIdx, chainIdx⟩),
      fun index tree leaf => ftsTable (index, tree, leaf)⟩
    RelTriple (AdaptiveRevealProbe.runDetailed ftsTable state ftsFuel
      (runJointResolved ((jointSourceComputation parameter root computation).run cache) context fuel otsTable))
      ((simulateQ romImpl (simulateQ (expandedAdversaryImpl secretKey) computation)).run actualCache)
      (JointOriginalRunRel parameter otsTable ftsTable) := by
  dsimp only
  have hjoint := jointResolvedCoupledAt_computation parameter root ftsTable computation state ftsFuel
    context fuel otsTable cache hbound hclean hsynced
  have hnative := OtsProbeSimulation.reachableResolvedCouples_simulateQ _ _
    (OtsProbeSimulation.reachableResolvedCouples_maskedChronologicalExpandedAdversaryImpl parameter root otsTable
      (fun index tree leaf => ftsTable (index, tree, leaf))) computation context fuel
    (OtsProbeSimulation.replaceOrdinaryCache cache.1 (mergedCache parameter ftsTable cache.2)) actualCache
    hinvariant hvisible hpublished
  rw [OtsProbeSimulation.simulateQ_unloggedMapped_eq_expanded] at hnative
  apply relTriple_post_mono (relTriple_trans_exists hjoint hnative)
  rintro left right ⟨native, hleft, hright⟩
  rcases hleft with hhit | heq
  · exact Or.inl hhit
  · exact Or.inr (heq ▸ hright)

theorem relTriple_jointResolvedComputation_originalMonitor
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (cache : JointSourceCache)
    (actualCache : QueryCache HashSpec) (hit : Bool)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash ftsFuel)
    (hclean : AdaptiveRevealProbe.tableHits state ftsTable = false)
    (hsynced : RevealedSynced parameter ftsTable state cache.2)
    (hinvariant : OtsProbeSimulation.ResolvedContextInvariant parameter otsTable context
      (mergedCache parameter ftsTable cache.2) actualCache)
    (hvisible : OtsProbeSimulation.VisibleResolvedComputationsCached parameter otsTable context actualCache)
    (hpublished : OtsProbeSimulation.PublishedValues context.state) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (otsTable ⟨lay, tree, leafIdx, chainIdx⟩),
      fun index tree leaf => ftsTable (index, tree, leaf)⟩
    RelTriple (AdaptiveRevealProbe.runDetailed ftsTable state ftsFuel
      (runJointResolved ((jointSourceComputation parameter root computation).run cache) context fuel otsTable))
      (runExceptionMonitor exception (simulateQ (expandedAdversaryImpl secretKey) computation) actualCache hit)
      (fun left right => JointOriginalRunRel parameter otsTable ftsTable left right.1 ∧
        right ∈ support (runExceptionMonitor exception (simulateQ (expandedAdversaryImpl secretKey) computation) actualCache hit)) := by
  dsimp only
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (otsTable ⟨lay, tree, leafIdx, chainIdx⟩),
    fun index tree leaf => ftsTable (index, tree, leaf)⟩
  have hbase := relTriple_jointResolvedComputation_original parameter root otsTable ftsTable computation state ftsFuel
    context fuel cache actualCache hbound hclean hsynced hinvariant hvisible hpublished
  have hprojection := runExceptionMonitor_project exception (simulateQ (expandedAdversaryImpl secretKey) computation) actualCache hit
  have hmonitor := relTriple_of_evalDist_map_eq_general
    ((simulateQ romImpl (simulateQ (expandedAdversaryImpl secretKey) computation)).run actualCache)
    (runExceptionMonitor exception (simulateQ (expandedAdversaryImpl secretKey) computation) actualCache hit)
    id Prod.fst (by simpa only [id_map] using congrArg evalDist hprojection.symm)
  apply relTriple_and_right_support
  apply relTriple_post_mono (relTriple_trans_exists hbase hmonitor)
  rintro left right ⟨actual, hrelation, heq⟩
  exact heq ▸ hrelation

theorem JointOriginalRunRel.of_completable
    {parameter : PublicParameter} {otsTable : OtsSecretIndex → HashOutput} {ftsTable : Coordinate → Digest}
    {left : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache)))}
    {right : α × QueryCache HashSpec}
    (hrel : JointOriginalRunRel parameter otsTable ftsTable left right)
    (hclean : left.hit = false)
    {entry : ResolvedRunResult (α × OtsProbeSimulation.SplitHashCache)}
    (hentry : projectJointResolvedCache parameter ftsTable left = some entry)
    (hcomplete : OtsProbeSimulation.DeferredCompletable otsTable entry.context) :
    entry.table = otsTable ∧ entry.value.1 = right.1 ∧
      OtsProbeSimulation.ResolvedContextInvariant parameter otsTable entry.context
        (OtsProbeSimulation.ordinaryQueryCache entry.value.2) right.2 ∧
      OtsProbeSimulation.VisibleResolvedComputationsCached parameter otsTable entry.context right.2 ∧
      OtsProbeSimulation.PublishedValues entry.context.state := by
  rcases hrel with hhit | hrel
  · simp [hclean] at hhit
  · rw [hentry] at hrel
    exact hrel.elim id (fun hdoomed => False.elim (hdoomed.2.2.2 hcomplete))

end SphincsSecurity.Concrete.FtsProbeSimulation
