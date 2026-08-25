import SphincsSecurity.Proof.Descent
import SphincsSecurity.Proof.Secrets

/-!
# Winning execution frame

A winning support point is split into the honest root computation, the adversary and signing run,
and final verification. The final hash-only run supplies one answer function and its cached query
trace for deterministic extraction.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

theorem simulateQ_romImpl_cache_le {alpha : Type} (oa : OracleComp OracleWorld alpha)
    (cache : QueryCache HashSpec) (z : alpha × QueryCache HashSpec)
    (hmem : z ∈ support ((simulateQ romImpl oa).run cache)) : cache ≤ z.2 := by
  apply OracleComp.simulateQ_run_preservesInv romImpl (cache ≤ ·) _ oa cache le_rfl z hmem
  intro input current hle result hresult
  cases input with
  | inl sample =>
      change result ∈ support (((unifFwdImpl HashSpec) sample).run current) at hresult
      have hrun := unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec) (liftM (unifSpec.query sample) : ProbComp _) current
      simp only [simulateQ_spec_query] at hrun
      rw [hrun, support_map] at hresult
      obtain ⟨value, _, heq⟩ := hresult
      rw [← (Prod.mk.inj heq).2]
      exact hle
  | inr hashInput =>
      change result ∈ support
        (((randomOracle : QueryImpl HashSpec _) hashInput).run current) at hresult
      exact hle.trans (QueryImpl.withCaching_cache_le uniformSampleImpl hashInput current
        result hresult)

namespace Concrete

theorem winning_support_extract (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (finalCache : QueryCache HashSpec)
    (hwin : (true, finalCache) ∈ support ((simulateQ romImpl
      (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅)) :
    ∃ root rootCache forgery signingLog adversaryCache,
      (root, rootCache) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅)
      ∧ ((forgery, signingLog), adversaryCache) ∈ support
        ((simulateQ romImpl
          ((simulateQ (forwardOracles + signingOracle scheme
            ⟨parameter, root, otsSecret, ftsSecret⟩)
              (adversary.main ⟨root, parameter⟩)).run)).run rootCache)
      ∧ (true, finalCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (verify ⟨root, parameter⟩ forgery.message forgery.signature)).run adversaryCache)
      ∧ SigningTranscript.Valid signingLog
      ∧ ¬SigningTranscript.Contains signingLog forgery
      ∧ ∃ f : QueryImpl HashSpec Id, finalCache.AgreesWithFn f
        ∧ evalWithAnswerFn f (verify ⟨root, parameter⟩ forgery.message forgery.signature) = true
        ∧ CachedRun finalCache f
          (verify ⟨root, parameter⟩ forgery.message forgery.signature)
        ∧ evalWithAnswerFn f
          (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)) = root
        ∧ CachedRun finalCache f
          (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
        ∧ Settled parameter otsSecret ftsSecret finalCache
          (.node topLayer rootTree ⟨layerHeight topLayer - 1, by decide⟩ ⟨0, by positivity⟩)
        ∧ ∃ digest : MessageDigest,
          evalWithAnswerFn f
              (messageDigest parameter root forgery.message forgery.signature.randomness) = digest
            ∧ CachedRun finalCache f
              (messageDigest parameter root forgery.message forgery.signature.randomness)
            ∧ Admissible digest
            ∧ let index := digestIndex digest
              let leaves := digestLeaves digest
              let ftsPublicKey := evalWithAnswerFn f
                (ftsRecover parameter index leaves forgery.signature.ftsSecret
                  forgery.signature.ftsPath)
              CachedRun finalCache f
                  (ftsRecover parameter index leaves forgery.signature.ftsSecret
                    forgery.signature.ftsPath)
                ∧ (Bad parameter otsSecret ftsSecret finalCache ∨
                  HypertreeTopOpening f finalCache parameter otsSecret index forgery.signature
                    ftsPublicKey root) := by
  rw [gameAfterSecrets, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hwin
  obtain ⟨⟨root, rootCache⟩, hroot, hrest⟩ := hwin
  have hroot' : (root, rootCache) ∈ support ((simulateQ
      (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅) := by
    simpa only [simulateQ_romImpl_liftM] using hroot
  rw [gameRest, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, hadversary, hfinish⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hfinish
  obtain ⟨⟨verified, verifyCache⟩, hverify, hreturn⟩ := hfinish
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hreturn
  obtain ⟨hresult, rfl⟩ := hreturn
  have hverified : verified = true := by
    cases verified <;> simp_all
  subst verified
  have htranscript : SigningTranscript.Valid signingLog
      ∧ ¬SigningTranscript.Contains signingLog forgery := by
    have h := (show (SigningTranscript.Valid signingLog
        ∧ ¬SigningTranscript.Contains signingLog forgery) ∧ True by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hresult.symm)
    exact h.1
  have hverify' : (true, finalCache) ∈ support ((simulateQ
      (randomOracle : QueryImpl HashSpec _)
      (verify ⟨root, parameter⟩ forgery.message forgery.signature)).run adversaryCache) := by
    simpa only [scheme, simulateQ_romImpl_liftM] using hverify
  obtain ⟨hverifyLe, f, hf, heval, hqueries⟩ := exists_answerFn_replay_of_mem_support
    (verify ⟨root, parameter⟩ forgery.message forgery.signature) adversaryCache true finalCache hverify'
  have hadversaryLe : rootCache ≤ adversaryCache := simulateQ_romImpl_cache_le
    ((simulateQ (forwardOracles + signingOracle scheme
      ⟨parameter, root, otsSecret, ftsSecret⟩)
        (adversary.main ⟨root, parameter⟩)).run) rootCache _ hadversary
  have hrootLe : rootCache ≤ finalCache := hadversaryLe.trans hverifyLe
  obtain ⟨hrootEval, hrootQueries⟩ := replay_of_mem_support_of_le
    (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)) ∅ root rootCache finalCache
    hroot' hrootLe f hf
  have hrootRun : CachedRun finalCache f
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)) := hrootQueries
  have hrootSettled := settled_treeRoot_of_cachedRun
    (otsSecret := otsSecret) (ftsSecret := ftsSecret) hf topLayer rootTree hrootRun
  obtain ⟨digest, hdigest, hdigestRun, hadmissible, hlayers, hftsRun, hlayersRun⟩ :=
    verify_extract ⟨root, parameter⟩ forgery.message forgery.signature heval hqueries
  let index := digestIndex digest
  let leaves := digestLeaves digest
  let ftsPublicKey := evalWithAnswerFn f
    (ftsRecover parameter index leaves forgery.signature.ftsSecret forgery.signature.ftsPath)
  have hhypertree : HypertreeRun f finalCache parameter index forgery.signature
      ftsPublicKey root :=
    hypertreeRun_of_verify index forgery.signature ftsPublicKey root hlayers hlayersRun
  have htarget : root = honestNode f parameter topLayer rootTree
      (otsSecret topLayer rootTree) (layerHeight topLayer) 0 := by
    rw [← hrootEval]
    rfl
  have htop := hypertree_top_extract_or_bad hf index forgery.signature ftsPublicKey root
    hhypertree htarget (by simpa using hrootSettled)
  exact ⟨root, rootCache, forgery, signingLog, adversaryCache, hroot', hadversary, hverify',
    htranscript.1, htranscript.2, f, hf, heval, hqueries, hrootEval, hrootRun,
    by simpa using hrootSettled, digest, hdigest, hdigestRun, hadmissible, hftsRun, htop⟩

end Concrete

end SphincsSecurity
