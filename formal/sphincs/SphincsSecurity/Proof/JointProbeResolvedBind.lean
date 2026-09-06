import SphincsSecurity.Proof.JointProbeResolvedRelation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def resumeJointResolved (table : Coordinate → Digest) (ftsFuel : Nat) (next : α → JointSource β) :
    AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache))) →
      ProbComp (AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (β × JointSourceCache))))
  | .stopped hit => pure (.stopped hit)
  | .done _ state none => AdaptiveRevealProbe.runDetailed table state ftsFuel (pure none)
  | .done _ state (some entry) => AdaptiveRevealProbe.runDetailed table state ftsFuel
      (runJointResolved ((next entry.value.1).run entry.value.2) entry.context entry.remaining entry.table)

theorem jointResolvedCoupledAt_bind_of_resume
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel afterFuel : Nat)
    (left : JointSource α) (next : α → JointSource β)
    (nativeLeft : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (nativeNext : α → StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hbind : AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointResolved ((left >>= next).run cache) context fuel otsTable) =
      (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved (left.run cache) context fuel otsTable) >>=
        resumeJointResolved table afterFuel next))
    (hleft : JointResolvedCoupledAt parameter table state ftsFuel left nativeLeft context fuel otsTable cache)
    (hnext : ∀ finalState entry,
      .done false finalState (some entry) ∈ support
        (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved (left.run cache) context fuel otsTable)) →
      JointResolvedCoupledAt parameter table finalState afterFuel (next entry.value.1) (nativeNext entry.value.1)
        entry.context entry.remaining entry.table entry.value.2) :
    JointResolvedCoupledAt parameter table state ftsFuel (left >>= next) (nativeLeft >>= nativeNext) context fuel otsTable cache := by
  unfold JointResolvedCoupledAt at hleft ⊢
  rw [hbind, StateT.run_bind, OtsProbeSimulation.runResolvedFromTable_bind]
  apply relTriple_bind (relTriple_and_left_support hleft
    (fun result => result ∈ support (AdaptiveRevealProbe.runDetailed table state ftsFuel
      (runJointResolved (left.run cache) context fuel otsTable))) (fun _ h => h))
  intro detailed native hrelation
  obtain ⟨hrelation, hsupport⟩ := hrelation
  cases detailed with
  | stopped hit =>
      cases hit with
      | false =>
          have heq : none = native := hrelation.resolve_left (by simp [AdaptiveRevealProbe.DetailedResult.hit])
          subst native
          exact relTriple_pure_pure (Or.inr rfl)
      | true =>
          apply relTriple_jointResolved_of_hit
          intro result hresult
          simp only [resumeJointResolved, mem_support_pure_iff] at hresult
          subst result
          rfl
  | done hit finalState entry =>
      have hhit := AdaptiveRevealProbe.tableHits_of_mem_runDetailed_done table state finalState ftsFuel
        (runJointResolved (left.run cache) context fuel otsTable) hit entry hsupport
      cases hit with
      | true =>
          apply relTriple_jointResolved_of_hit
          cases entry with
          | none => exact runDetailed_hit_eq_true_of_tableHits_eq_true table finalState afterFuel _ hhit
          | some entry => exact runDetailed_hit_eq_true_of_tableHits_eq_true table finalState afterFuel _ hhit
      | false =>
          have heq := hrelation.resolve_left (by simp [AdaptiveRevealProbe.DetailedResult.hit])
          subst native
          cases entry with
          | none =>
              simp only [resumeJointResolved, AdaptiveRevealProbe.runDetailed, construct_pure, hhit,
                projectJointResolvedCache, cleanJointResolved, Option.map_none]
              exact relTriple_pure_pure (Or.inr rfl)
          | some entry => exact hnext finalState entry hsupport

theorem jointResolvedCoupledAt_bind_probeFree
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (left : JointSource α) (next : α → JointSource β)
    (nativeLeft : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (nativeNext : α → StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hfree : (runJointResolved (left.run cache) context fuel otsTable).IsQueryBoundP AdaptiveRevealProbe.IsProbe 0)
    (hleft : JointResolvedCoupledAt parameter table state ftsFuel left nativeLeft context fuel otsTable cache)
    (hnext : ∀ finalState entry,
      .done false finalState (some entry) ∈ support
        (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved (left.run cache) context fuel otsTable)) →
      JointResolvedCoupledAt parameter table finalState ftsFuel (next entry.value.1) (nativeNext entry.value.1)
        entry.context entry.remaining entry.table entry.value.2) :
    JointResolvedCoupledAt parameter table state ftsFuel (left >>= next) (nativeLeft >>= nativeNext) context fuel otsTable cache := by
  apply jointResolvedCoupledAt_bind_of_resume parameter table state ftsFuel ftsFuel left next nativeLeft nativeNext
    context fuel otsTable cache ?_ hleft hnext
  rw [StateT.run_bind, runJointResolved_bind, AdaptiveRevealProbe.runDetailed_bind_probeFree table state ftsFuel _ _ hfree]
  apply bind_congr
  intro result
  cases result with
  | stopped hit => rfl
  | done hit finalState entry => cases entry <;> rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
