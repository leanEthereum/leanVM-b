import SphincsSecurity.Proof.Game

/-!
# Splitting the game at the secrets

The honest structure is a function of the sampled secrets and of the oracle's answers, so a bound
that mentions it has to be stated after the secrets are fixed and before any hash query is made.
Key generation samples them and then builds layer `0`'s tree, so the split is inside key generation
rather than after it: what follows the split makes every hash query the experiment makes, and the
accounting therefore starts from the empty cache, at potential `0`, and with nothing to prove about
what key generation leaves behind.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

/-- The game from the sampled secrets on: build the root, then run the adversary against the signer
and verify what it returns. -/
noncomputable def gameAfterSecrets (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) : OracleComp OracleWorld Bool := do
  let root ← liftM
    (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)
  gameRest scheme adversary ⟨root, parameter⟩ ⟨parameter, root, otsSecret, ftsSecret⟩

attribute [local semireducible] keygen

theorem gameCore_eq_secrets (adversary : Adversary) :
    gameCore scheme adversary = (do
      let parameter ← liftM sampleParameter
      let otsSecret ← liftM sampleOtsSecrets
      let ftsSecret ← liftM sampleFtsSecrets
      gameAfterSecrets adversary parameter otsSecret ftsSecret) := by
  rw [gameCore_eq]
  simp only [scheme, keygen, gameAfterSecrets, bind_assoc, pure_bind]

/-- Lifting a sampling into the game's oracles changes nothing about where it lands. -/
theorem mem_support_liftM_of_mem_support {α : Type} {oa : ProbComp α} {x : α}
    (hmem : x ∈ support oa) : x ∈ support (liftM oa : OracleComp OracleWorld α) := by
  rwa [← liftComp_eq_liftM, support_liftComp]

/-- A lifted sampling passes through the semantics untouched: it samples, and the cache it hands on
is the one it was given. -/
theorem simulateQ_romImpl_liftM_bind_run' {α β : Type} (oa : ProbComp α)
    (k : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM oa : OracleComp OracleWorld α) >>= k)).run' cache
      = oa >>= fun x => (simulateQ romImpl (k x)).run' cache := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    show simulateQ romImpl (liftM oa : OracleComp OracleWorld α)
      = simulateQ (unifFwdImpl HashSpec) oa from QueryImpl.simulateQ_add_liftM_left _ _ oa,
    unifFwdImpl.simulateQ_run]
  simp [map_eq_bind_pure_comp, bind_assoc, StateT.run'_eq]

/-- **The reduction's frame.** A bound on the game after the secrets are sampled, uniform in them,
is a bound on the advantage. -/
theorem forgeAdvantage_le_secrets (adversary : Adversary) (c : ℝ≥0∞)
    (h : ∀ parameter ∈ support sampleParameter, ∀ otsSecret ∈ support sampleOtsSecrets,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
      Pr[= true | (simulateQ romImpl
          (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤ c) :
    forgeAdvantage scheme adversary ≤ c := by
  rw [forgeAdvantage, gameCore_eq_secrets, simulateQ_romImpl_liftM_bind_run',
    ← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_of_forall_le fun parameter hparameter => ?_
  rw [probEvent_eq_eq_probOutput, simulateQ_romImpl_liftM_bind_run', ← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_of_forall_le fun otsSecret hots => ?_
  rw [probEvent_eq_eq_probOutput, simulateQ_romImpl_liftM_bind_run', ← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_of_forall_le fun ftsSecret hfts => ?_
  rw [probEvent_eq_eq_probOutput]
  exact h parameter hparameter otsSecret hots ftsSecret hfts

/-- The query bound survives the split: what bounds the whole experiment bounds what follows the
secrets. -/
theorem isQueryBoundP_gameAfterSecrets (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) {parameter : PublicParameter}
    (hparameter : parameter ∈ support sampleParameter)
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    (hots : otsSecret ∈ support sampleOtsSecrets)
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    (gameAfterSecrets adversary parameter otsSecret ftsSecret).IsQueryBoundP
      (· matches Sum.inr _) q := by
  rw [HasHashQueryBound, gameCore_eq_secrets] at hq
  exact isQueryBoundP_of_bind
    (isQueryBoundP_of_bind
      (isQueryBoundP_of_bind hq parameter (mem_support_liftM_of_mem_support hparameter))
      otsSecret (mem_support_liftM_of_mem_support hots))
    ftsSecret (mem_support_liftM_of_mem_support hfts)

end Concrete

end SphincsSecurity
