import SphincsSecurity.Proof.Logged
import VCVio.OracleComp.QueryTracking.ProgrammingOracle
import VCVio.ProgramLogic.Relational.ProgrammingOracle

/-!
# The programmed game

The hybrid step: answer chosen hash inputs with values decided in advance, carrying a flag that
records whether the programming was ever observable. The game's distribution changes only when that
flag fires, which is the identical-until-bad pattern; VCVio proves the bound for a computation over
one spec, and this module lifts it to the game's spec, `unifSpec + HashSpec`, where the sampling
summand is passive and the programming acts on the hash summand alone.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

/-- The sampling summand, carrying the flag untouched. -/
noncomputable def unifFwdFlag :
    QueryImpl unifSpec (StateT (QueryCache HashSpec × Bool) ProbComp) :=
  QueryImpl.extendState (unifFwdImpl HashSpec) fun _ _ _ _ flag => flag

/-- The random-oracle semantics with a policy programmed into the hash oracle. -/
noncomputable def romImplProg (policy : OracleSpec.ProgrammingPolicy HashSpec) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec × Bool) ProbComp) :=
  unifFwdFlag + QueryImpl.withProgramming uniformSampleImpl policy

/-- The identical-until-bad partner: the same flag, but every answer honest. -/
noncomputable def romImplTrack (policy : OracleSpec.ProgrammingPolicy HashSpec) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec × Bool) ProbComp) :=
  unifFwdFlag + QueryImpl.withCachingTrackingPolicy uniformSampleImpl policy

theorem romImplProg_inl (policy : OracleSpec.ProgrammingPolicy HashSpec) (i : ℕ) :
    romImplProg policy (Sum.inl i) = romImplTrack policy (Sum.inl i) := rfl

/-- The two implementations agree on every outcome that leaves the flag unset. On a sampling query
they are the same implementation; on a hash query they differ only where the policy fires, and there
both produce only flagged outcomes. -/
theorem romImplProg_agree (policy : OracleSpec.ProgrammingPolicy HashSpec)
    (t : OracleWorld.Domain) (cache : QueryCache HashSpec) (u : OracleWorld.Range t)
    (cache' : QueryCache HashSpec) :
    Pr[= (u, (cache', false)) | (romImplProg policy t).run (cache, false)]
      = Pr[= (u, (cache', false)) | (romImplTrack policy t).run (cache, false)] := by
  cases t with
  | inl i => rw [romImplProg_inl]
  | inr input =>
      simp only [romImplProg, romImplTrack, QueryImpl.add_apply_inr,
        QueryImpl.withProgramming_apply, QueryImpl.withCachingTrackingPolicy_apply]
      rcases hcache : cache input with _ | v
      · rcases hpolicy : policy input with _ | w
        · simp [hcache]
        · -- the policy fires: both sides flag the outcome, so neither yields an unflagged one
          rw [probOutput_eq_zero_of_not_mem_support (by
              intro hmem
              simp [hcache] at hmem
              exact Bool.noConfusion (congrArg
                (fun z : OracleWorld.Range (Sum.inr input) × QueryCache HashSpec × Bool => z.2.2)
                (Set.mem_singleton_iff.mp hmem))),
            probOutput_eq_zero_of_not_mem_support (by
              intro hmem
              simp [hcache] at hmem
              obtain ⟨answer, _, hanswer⟩ := hmem
              exact Bool.noConfusion (congrArg
                (fun z : OracleWorld.Range (Sum.inr input) × QueryCache HashSpec × Bool => z.2.2)
                hanswer))]
      · simp [hcache]

/-- The flag only ever goes up, in either implementation: a sampling query carries it, and the two
hash implementations are monotone by construction. -/
theorem romImplProg_mono (policy : OracleSpec.ProgrammingPolicy HashSpec)
    (t : OracleWorld.Domain) (p : QueryCache HashSpec × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((romImplProg policy t).run p), z.2.2 = true := by
  cases t with
  | inl i =>
      intro z hz
      rw [show (romImplProg policy (Sum.inl i)).run p
          = ((unifFwdImpl HashSpec i).run p.1 >>= fun q => pure (q.1, (q.2, p.2))) from rfl] at hz
      obtain ⟨q, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hp
  | inr input =>
      intro z hz
      obtain ⟨cache, flag⟩ := p
      simp only at hp
      subst hp
      exact QueryImpl.withProgramming_bad_monotone uniformSampleImpl policy input cache z hz

theorem romImplTrack_mono (policy : OracleSpec.ProgrammingPolicy HashSpec)
    (t : OracleWorld.Domain) (p : QueryCache HashSpec × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((romImplTrack policy t).run p), z.2.2 = true := by
  cases t with
  | inl i =>
      intro z hz
      rw [show (romImplTrack policy (Sum.inl i)).run p
          = ((unifFwdImpl HashSpec i).run p.1 >>= fun q => pure (q.1, (q.2, p.2))) from rfl] at hz
      obtain ⟨q, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hp
  | inr input =>
      intro z hz
      obtain ⟨cache, flag⟩ := p
      simp only at hp
      subst hp
      exact QueryImpl.withCachingTrackingPolicy_bad_monotone uniformSampleImpl policy input cache z
        hz

/-- **The hybrid step.** Programming the hash oracle moves the game's distribution by at most the
probability that the programming is ever observed. -/
theorem tvDist_romImplProg_le (policy : OracleSpec.ProgrammingPolicy HashSpec) {α : Type}
    (oa : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    tvDist ((simulateQ (romImplProg policy) oa).run (cache, false))
        ((simulateQ (romImplTrack policy) oa).run (cache, false))
      ≤ Pr[fun z : α × QueryCache HashSpec × Bool => z.2.2 = true
          | (simulateQ (romImplProg policy) oa).run (cache, false)].toReal :=
  ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad _ _ oa cache
    (romImplProg_agree policy) (romImplProg_mono policy) (romImplTrack_mono policy)

end SphincsSecurity
