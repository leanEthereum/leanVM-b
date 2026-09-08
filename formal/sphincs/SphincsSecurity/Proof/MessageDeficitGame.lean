import SphincsSecurity.Proof.MessageDeficitReuse
import SphincsSecurity.Proof.TerminalSampling

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def messageDeficitGameAfterSecrets (adversary : Adversary) (secrets : SampledSecrets) :
    ProbComp ((Bool × QueryCache HashSpec) × Bool) := do
  let rootResult ← (simulateQ romImpl
    (liftM (treeRoot secrets.parameter topLayer rootTree (secrets.otsSecret topLayer rootTree) :
      OracleComp HashSpec Digest) : OracleComp OracleWorld Digest)).run ∅
  let key : SecretKey := ⟨secrets.parameter, rootResult.1, secrets.otsSecret, secrets.ftsSecret⟩
  runExceptionMonitor (cacheEntryException (MessageDeficitExceptional key))
    (gameRest scheme adversary ⟨rootResult.1, secrets.parameter⟩ key) rootResult.2 false

theorem messageDeficitGameAfterSecrets_projection (adversary : Adversary) (secrets : SampledSecrets) :
    Prod.fst <$> messageDeficitGameAfterSecrets adversary secrets =
      (simulateQ romImpl (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret)).run ∅ := by
  rw [messageDeficitGameAfterSecrets, map_bind, gameAfterSecrets, simulateQ_bind, StateT.run_bind]
  exact bind_congr fun rootResult => runExceptionMonitor_project _ _ rootResult.2 false

theorem probEvent_messageDeficitGameAfterSecrets_le (adversary : Adversary) (secrets : SampledSecrets)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hbound : (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret).IsQueryBoundP
      (· matches Sum.inr _) q) :
    Pr[fun result => result.2 = true | messageDeficitGameAfterSecrets adversary secrets] ≤ (q : ENNReal) / 2 ^ 223 := by
  unfold messageDeficitGameAfterSecrets
  apply probEvent_bind_le_of_forall_le
  intro rootResult hroot
  let key : SecretKey := ⟨secrets.parameter, rootResult.1, secrets.otsSecret, secrets.ftsSecret⟩
  have hrootSupport : rootResult.1 ∈ support
      (liftM (treeRoot secrets.parameter topLayer rootTree (secrets.otsSecret topLayer rootTree) :
        OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) := by
    apply support_simulateQ_run'_subset romImpl _ ∅
    rw [StateT.run'_eq, support_map]
    exact ⟨rootResult, hroot, rfl⟩
  rw [gameAfterSecrets] at hbound
  have hrest := isQueryBoundP_of_bind hbound rootResult.1 hrootSupport
  have hfinite := finite_cache_of_mem_support _ ∅ rootResult.1 rootResult.2 hroot finite_empty
  apply probEvent_messageDeficitExceptional_le key _ q hrest hq rootResult.2 hfinite
  intro payload
  have hrootHash := hroot
  rw [simulateQ_romImpl_liftM] at hrootHash
  exact treeRoot_cache_message_none secrets.parameter topLayer rootTree (secrets.otsSecret topLayer rootTree)
    rootResult.1 rootResult.2 hrootHash payload

noncomputable def sampledMessageDeficitGame (adversary : Adversary) : ProbComp (Bool × Bool) := do
  let secrets ← sampleSecrets
  let result ← messageDeficitGameAfterSecrets adversary secrets
  pure (result.1.1, result.2)

theorem sampledMessageDeficitGame_projection (adversary : Adversary) :
    Prod.fst <$> sampledMessageDeficitGame adversary = sampledGame adversary := by
  rw [sampledMessageDeficitGame, map_bind, sampledGame]
  apply bind_congr
  intro secrets
  rw [bind_pure_comp, Functor.map_map, StateT.run'_eq, ← messageDeficitGameAfterSecrets_projection, Functor.map_map]

theorem probEvent_sampledMessageDeficitGame_le (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hq : q ≤ 2 ^ 127) :
    Pr[fun result => result.2 = true | sampledMessageDeficitGame adversary] ≤ (q : ENNReal) / 2 ^ 223 := by
  rw [sampledMessageDeficitGame]
  apply probEvent_bind_le_of_forall_le
  intro secrets hsecrets
  rw [bind_pure_comp, probEvent_map]
  have hs := SampledSecrets.support_components hsecrets
  exact probEvent_messageDeficitGameAfterSecrets_le adversary secrets q hq
    (isQueryBoundP_gameAfterSecrets adversary q hbound hs.1 hs.2.1 hs.2.2)

theorem forgeAdvantage_le_without_messageDeficit_add_exception (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hq : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      Pr[fun result => result.1 = true ∧ result.2 = false | sampledMessageDeficitGame adversary] +
        (q : ENNReal) / 2 ^ 223 := by
  rw [forgeAdvantage_eq_sampledGame, ← sampledMessageDeficitGame_projection, probOutput_map]
  apply le_trans _ (add_le_add le_rfl (probEvent_sampledMessageDeficitGame_le adversary q hbound hq))
  apply le_trans _ (probEvent_or_le _ _ _)
  apply probEvent_mono
  intro result _ hwin
  cases result.2
  · exact Or.inl ⟨hwin, rfl⟩
  · exact Or.inr rfl

end SphincsSecurity.Concrete
