import SphincsSecurity.Proof.JointProbeResolvedBlocks

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def JointResolvedCleanRel (parameter : PublicParameter) (table : Coordinate → Digest)
    (left : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache))))
    (right : Option (ResolvedRunResult (α × OtsProbeSimulation.SplitHashCache))) : Prop :=
  left.hit = true ∨ projectJointResolvedCache parameter table left = right

def JointResolvedCoupledAt (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (source : JointSource α)
    (native : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (cache : JointSourceCache) : Prop :=
  RelTriple (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved (source.run cache) context fuel otsTable))
    (OtsProbeSimulation.runResolvedFromTable context fuel otsTable
      (native.run (OtsProbeSimulation.replaceOrdinaryCache cache.1 (mergedCache parameter table cache.2))))
    (JointResolvedCleanRel parameter table)

theorem jointResolvedCoupledAt_of_project_eq
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (source : JointSource α)
    (native : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (cache : JointSourceCache)
    (h : projectJointResolvedCache parameter table <$>
        AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved (source.run cache) context fuel otsTable) =
      OtsProbeSimulation.runResolvedFromTable context fuel otsTable
        (native.run (OtsProbeSimulation.replaceOrdinaryCache cache.1 (mergedCache parameter table cache.2)))) :
    JointResolvedCoupledAt parameter table state ftsFuel source native context fuel otsTable cache := by
  unfold JointResolvedCoupledAt
  rw [← h]
  have hself := relTriple_post_mono
    (relTriple_refl (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved (source.run cache) context fuel otsTable)))
    (R' := fun left right => JointResolvedCleanRel parameter table left (projectJointResolvedCache parameter table right))
    (fun left right heq => Or.inr (congrArg (projectJointResolvedCache parameter table) heq))
  simpa only [id_map] using relTriple_map (f := id) (g := projectJointResolvedCache parameter table) hself

theorem jointResolvedCoupledAt_nativeBlock
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (hcommutes : ∀ cache, OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table cache) computation)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (cache : JointSourceCache) (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    JointResolvedCoupledAt parameter table state ftsFuel (jointSourceNativeBlock computation) computation context fuel otsTable cache :=
  jointResolvedCoupledAt_of_project_eq parameter table state ftsFuel _ _ context fuel otsTable cache
    (jointSourceNativeBlock_resolved parameter table state ftsFuel computation hcommutes context fuel otsTable cache hclean)

theorem jointResolvedCoupledAt_ftsBlock
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (masked : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (ordinary : OracleComp HashSpec α) (h : NativeResolvedCoupled parameter table state ftsFuel masked ordinary)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (cache : JointSourceCache) :
    JointResolvedCoupledAt parameter table state ftsFuel (jointSourceFtsBlock masked)
      (simulateQ OtsProbeSimulation.ordinaryHashImpl ordinary) context fuel otsTable cache :=
  jointResolvedCoupledAt_of_project_eq parameter table state ftsFuel _ _ context fuel otsTable cache
    (jointSourceFtsBlock_resolved parameter table state ftsFuel masked ordinary h context fuel otsTable cache)

theorem relTriple_jointResolved_of_hit
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (left : ProbComp (AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache)))))
    (right : ProbComp (Option (ResolvedRunResult (α × OtsProbeSimulation.SplitHashCache))))
    (hhit : ∀ result ∈ support left, result.hit = true) :
    RelTriple left right (JointResolvedCleanRel parameter table) :=
  relTriple_post_mono
    (relTriple_and_left_support (relTriple_true left right) (fun result => result.hit = true) hhit)
    (fun _ _ h => Or.inl h.2)

end SphincsSecurity.Concrete.FtsProbeSimulation
