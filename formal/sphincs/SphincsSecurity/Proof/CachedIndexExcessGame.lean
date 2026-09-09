import SphincsSecurity.Proof.CachedIndexExcessConcentration
import SphincsSecurity.Proof.TerminalSampling

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def sampledCachedIndexExcessGame (adversary : Adversary) : ProbComp (Bool × Bool) := do
  let secrets ← sampleSecrets
  let result ← runExceptionMonitor (cacheEntryException (CachedIndexExcessExceptional secrets.parameter))
    (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false
  pure (result.1.1, result.2)

theorem sampledCachedIndexExcessGame_projection (adversary : Adversary) :
    Prod.fst <$> sampledCachedIndexExcessGame adversary = sampledGame adversary := by
  rw [sampledCachedIndexExcessGame, map_bind, sampledGame]
  apply bind_congr
  intro secrets
  rw [bind_pure_comp, Functor.map_map, StateT.run'_eq,
    ← runExceptionMonitor_project
      (cacheEntryException (CachedIndexExcessExceptional secrets.parameter))
      (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false,
    Functor.map_map]

theorem probEvent_sampledCachedIndexExcessGame_le (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) :
    Pr[fun result => result.2 = true | sampledCachedIndexExcessGame adversary] ≤ (q : ENNReal) / 2 ^ 170 := by
  rw [sampledCachedIndexExcessGame]
  apply probEvent_bind_le_of_forall_le
  intro secrets hsecrets
  rw [bind_pure_comp, probEvent_map]
  have hs := SampledSecrets.support_components hsecrets
  exact probEvent_cachedIndexExcessExceptional_le secrets.parameter _ q
    (isQueryBoundP_gameAfterSecrets adversary q hbound hs.1 hs.2.1 hs.2.2) ∅ finite_empty
    (fun _ _ => rfl)

theorem forgeAdvantage_le_without_cachedIndexExcess_add_exception (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) :
    forgeAdvantage scheme adversary ≤
      Pr[fun result => result.1 = true ∧ result.2 = false | sampledCachedIndexExcessGame adversary] +
        (q : ENNReal) / 2 ^ 170 := by
  rw [forgeAdvantage_eq_sampledGame, ← sampledCachedIndexExcessGame_projection, probOutput_map]
  apply le_trans _ (add_le_add le_rfl (probEvent_sampledCachedIndexExcessGame_le adversary q hbound))
  apply le_trans _ (probEvent_or_le _ _ _)
  apply probEvent_mono
  intro result _ hwin
  cases result.2
  · exact Or.inl ⟨hwin, rfl⟩
  · exact Or.inr rfl

end SphincsSecurity.Concrete
