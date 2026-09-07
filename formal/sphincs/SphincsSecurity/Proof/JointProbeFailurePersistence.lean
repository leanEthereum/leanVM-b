import SphincsSecurity.Proof.JointProbeOriginalSharedSupport

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def JointCompletionFailure
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult α))) : Prop :=
  ∀ entry, cleanJointResolved result = some entry → ¬ OtsProbeSimulation.DeferredCompletable entry.table entry.context

theorem jointCompletionFailure_of_hit
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult α)))
    (hhit : result.hit = true) : JointCompletionFailure result := by
  cases result <;> simp_all [JointCompletionFailure, cleanJointResolved, AdaptiveRevealProbe.DetailedResult.hit]

theorem resolvedFacts_of_mem_jointDetailed
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (entry : ResolvedRunResult α) (hconsistent : context.ValuesConsistent)
    (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable)
    (hresult : .done false finalState (some entry) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved computation context fuel otsTable))) :
    entry.table = otsTable ∧ entry.context.ValuesConsistent ∧
      OtsProbeSimulation.StartTableAgrees entry.context.state otsTable ∧
      (OtsProbeSimulation.DeferredCompletable otsTable entry.context → OtsProbeSimulation.DeferredCompletable otsTable context) := by
  have hmap : some entry ∈ support
      (cleanJointResolved <$> AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved computation context fuel otsTable)) := by
    rw [support_map]
    exact ⟨_, hresult, rfl⟩
  rw [runJointFts_resolved_commute, support_map] at hmap
  obtain ⟨nativeOption, hnative, heq⟩ := hmap
  cases nativeOption with
  | none => simp [flattenOptionalResolved] at heq
  | some native =>
      have hcore := OtsProbeSimulation.resolvedCore_of_mem_runResolvedFromTable _ context fuel otsTable native hconsistent hstarts hnative
      cases hvalue : native.value with
      | none => simp [flattenOptionalResolved, hvalue] at heq
      | some value =>
          simp only [flattenOptionalResolved, hvalue, Option.map_some, Option.some.injEq] at heq
          subst entry
          exact ⟨hcore.1, hcore.2.1, hcore.2.2, fun hc =>
            OtsProbeSimulation.deferredCompletable_of_mem_runResolvedFromTable _ context fuel otsTable native
              hconsistent hstarts hnative hc⟩

theorem jointCompletionFailure_of_not_completable
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable)
    (hdoomed : ¬ OtsProbeSimulation.DeferredCompletable otsTable context)
    (result) (hresult : result ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved computation context fuel otsTable))) :
    JointCompletionFailure result := by
  intro entry heq hc
  cases result with
  | stopped hit => simp [cleanJointResolved] at heq
  | done hit finalState native =>
      cases hit with
      | true => simp [cleanJointResolved] at heq
      | false =>
          simp only [cleanJointResolved] at heq
          subst native
          have hf := resolvedFacts_of_mem_jointDetailed table computation state finalState ftsFuel context fuel otsTable entry
            hconsistent hstarts hresult
          rw [hf.1] at hc
          exact hdoomed (hf.2.2.2 hc)

theorem jointCompletionFailure_resume
    (table : Coordinate → Digest) (left : JointSource α) (next : α → JointSource β)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel afterFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (cache : JointSourceCache) (hconsistent : context.ValuesConsistent)
    (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable)
    (head) (hhead : head ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved (left.run cache) context fuel otsTable)))
    (hfailed : JointCompletionFailure head)
    (result) (hresult : result ∈ support (resumeJointResolved table afterFuel next head)) :
    JointCompletionFailure result := by
  cases head with
  | stopped hit =>
      simp only [resumeJointResolved, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simp [JointCompletionFailure, cleanJointResolved]
  | done hit finalState entry =>
      cases hit with
      | true =>
          have hh := AdaptiveRevealProbe.tableHits_of_mem_runDetailed_done table state finalState ftsFuel _ true entry hhead
          apply jointCompletionFailure_of_hit
          cases entry with
          | none => exact runDetailed_hit_eq_true_of_tableHits_eq_true table finalState afterFuel _ hh result hresult
          | some entry => exact runDetailed_hit_eq_true_of_tableHits_eq_true table finalState afterFuel _ hh result hresult
      | false =>
          cases entry with
          | none =>
              simp only [resumeJointResolved, AdaptiveRevealProbe.runDetailed, construct_pure, support_pure, Set.mem_singleton_iff] at hresult
              subst result
              cases AdaptiveRevealProbe.tableHits finalState table <;> simp [JointCompletionFailure, cleanJointResolved]
          | some entry =>
              have hf := resolvedFacts_of_mem_jointDetailed table _ state finalState ftsFuel context fuel otsTable entry hconsistent hstarts hhead
              apply jointCompletionFailure_of_not_completable table _ finalState afterFuel entry.context entry.remaining entry.table
                hf.2.1 (hf.1.symm ▸ hf.2.2.1) (hfailed entry rfl) result hresult

theorem probEvent_jointCompletionFailure_resume_eq_one
    (table : Coordinate → Digest) (left : JointSource α) (next : α → JointSource β)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel afterFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (cache : JointSourceCache) (hconsistent : context.ValuesConsistent)
    (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable)
    (head) (hhead : head ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved (left.run cache) context fuel otsTable)))
    (hfailed : JointCompletionFailure head) :
    Pr[JointCompletionFailure | resumeJointResolved table afterFuel next head] = 1 := by
  apply probEvent_eq_one_iff.mpr
  exact ⟨by simp, jointCompletionFailure_resume table left next state ftsFuel afterFuel context fuel otsTable cache hconsistent hstarts head hhead hfailed⟩

end SphincsSecurity.Concrete.FtsProbeSimulation
