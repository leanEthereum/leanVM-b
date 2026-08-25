import SphincsSecurity.Proof.FullTrace
import SphincsSecurity.Proof.Secrets

/-!
# Direct adversary queries within the complete query budget

The global game bound controls the direct hash intervals on every supported adversary path. The
proof follows only signer replies that the concrete signer can actually return, rather than asking
for a structural bound on continuations after impossible replies.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

noncomputable def expandedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (OracleComp OracleWorld) := by
  intro input
  cases input with
  | inl worldInput => exact liftM (OracleWorld.query worldInput)
  | inr request => exact Concrete.scheme.sign secretKey request

theorem forwardOracles_add_signingOracle_eq_withTraceAppend
    (secretKey : SecretKey) :
    forwardOracles + signingOracle Concrete.scheme secretKey =
      QueryImpl.withTraceAppend (expandedAdversaryImpl secretKey) signingLogFragment := by
  funext input
  cases input with
  | inl worldInput => rfl
  | inr request => rfl

theorem simulateQ_expandedAdversaryImpl_query_bind_inl
    (secretKey : SecretKey) (worldInput : OracleWorld.Domain)
    (continuation : OracleWorld.Range worldInput →
      OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (expandedAdversaryImpl secretKey)
        (liftM ((OracleWorld + SigningSpec).query (.inl worldInput)) >>= continuation) =
      (liftM (OracleWorld.query worldInput) >>= fun output =>
        simulateQ (expandedAdversaryImpl secretKey) (continuation output)) := by
  simp [expandedAdversaryImpl]

theorem simulateQ_expandedAdversaryImpl_query_bind_inr
    (secretKey : SecretKey) (request : SignRequest)
    (continuation : SigningSpec.Range request →
      OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (expandedAdversaryImpl secretKey)
        (liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= continuation) =
      (Concrete.scheme.sign secretKey request >>= fun output =>
        simulateQ (expandedAdversaryImpl secretKey) (continuation output)) := by
  simp [expandedAdversaryImpl]

theorem isQueryBoundP_expandedAdversaryImpl
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : ((simulateQ (forwardOracles + signingOracle Concrete.scheme secretKey)
      computation).run).IsQueryBoundP (· matches Sum.inr _) q) :
    (simulateQ (expandedAdversaryImpl secretKey) computation).IsQueryBoundP
      (· matches Sum.inr _) q := by
  rw [forwardOracles_add_signingOracle_eq_withTraceAppend] at hbound
  exact (isQueryBoundP_iff_of_map_eq (p := (· matches Sum.inr _))
    (QueryImpl.fst_map_run_withTraceAppend (expandedAdversaryImpl secretKey)
      signingLogFragment computation)).mp hbound

theorem unloggedMappedAdversaryImpl_eq_simulateQ_expanded
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain) :
    unloggedMappedAdversaryImpl secretKey input =
      simulateQ romImpl (expandedAdversaryImpl secretKey input) := by
  cases input with
  | inl worldInput =>
      exact (simulateQ_spec_query
        (impl := romImpl) worldInput).symm
  | inr request => rfl

theorem unloggedMappedAdversaryImpl_output_mem_support_expanded
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (initialCache finalCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (hmem : (output, finalCache) ∈ support
      ((unloggedMappedAdversaryImpl secretKey input).run initialCache)) :
    output ∈ support (expandedAdversaryImpl secretKey input) := by
  apply support_simulateQ_run'_subset romImpl
    (expandedAdversaryImpl secretKey input) initialCache
  rw [StateT.run'_eq, support_map,
    ← unloggedMappedAdversaryImpl_eq_simulateQ_expanded]
  exact ⟨(output, finalCache), hmem, rfl⟩

theorem fullTracedMappedAdversaryImpl_direct_countQ_le_of_expanded
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (q : Nat),
      (simulateQ (expandedAdversaryImpl secretKey) computation).IsQueryBoundP
        (· matches Sum.inr _) q →
      ∀ (initialCache : QueryCache HashSpec) (initialTrace : FullAdversaryTrace)
        (result : α × (QueryCache HashSpec × FullAdversaryTrace)),
        result ∈ support
          ((simulateQ (fullTracedMappedAdversaryImpl secretKey)
            computation).run (initialCache, initialTrace)) →
        result.2.2.direct.countQ isDirectHashQuery ≤
          initialTrace.direct.countQ isDirectHashQuery + q := by
  induction computation using OracleComp.inductionOn with
  | pure x =>
      intro q _ initialCache initialTrace result hmem
      simp only [simulateQ_pure] at hmem
      subst result
      simp
  | query_bind input continuation ih =>
      intro q hbound initialCache initialTrace result hmem
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨queryResult, hquery, hrest⟩ := hmem
      have hquery' := hquery
      rw [simulateQ_spec_query, fullTracedMappedAdversaryImpl,
        QueryImpl.extendState_apply, mem_support_bind_iff] at hquery'
      obtain ⟨underlyingResult, hunderlying, hpure⟩ := hquery'
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst queryResult
      have houtput := unloggedMappedAdversaryImpl_output_mem_support_expanded secretKey input
        initialCache underlyingResult.2 underlyingResult.1 hunderlying
      cases input with
      | inl worldInput =>
          cases worldInput with
          | inl uniformInput =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                isQueryBoundP_query_bind_iff] at hbound
              have htail := ih underlyingResult.1 q (hbound.2 underlyingResult.1)
                underlyingResult.2
                (fullAdversaryTraceUpdate (.inl (.inl uniformInput)) initialCache
                  underlyingResult.1 underlyingResult.2 initialTrace)
                result hrest
              simp [fullAdversaryTraceUpdate, QueryLog.countQ, QueryLog.getQ_cons,
                isDirectHashQuery] at htail ⊢
              exact htail
          | inr hashInput =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                isQueryBoundP_query_bind_iff] at hbound
              have hpositive : 0 < q := hbound.1.resolve_left (by simp)
              have htail := ih underlyingResult.1 (q - 1) (hbound.2 underlyingResult.1)
                underlyingResult.2
                (fullAdversaryTraceUpdate (.inl (.inr hashInput)) initialCache
                  underlyingResult.1 underlyingResult.2 initialTrace)
                result hrest
              simp [fullAdversaryTraceUpdate, QueryLog.countQ, QueryLog.getQ_cons,
                isDirectHashQuery] at htail ⊢
              omega
      | inr request =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
          have hcontinuation := isQueryBoundP_of_bind hbound underlyingResult.1 houtput
          have htail := ih underlyingResult.1 q hcontinuation underlyingResult.2
            (fullAdversaryTraceUpdate (.inr request) initialCache underlyingResult.1
              underlyingResult.2 initialTrace)
            result hrest
          simp [fullAdversaryTraceUpdate, QueryLog.countQ, QueryLog.getQ_cons,
            isDirectHashQuery] at htail ⊢
          exact htail

theorem gameRestWithFullTrace_hashQueries_length_le_of_bound
    (adversary : Adversary) (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) (q : Nat)
    (hbound : ((simulateQ (forwardOracles + signingOracle Concrete.scheme secretKey)
      (adversary.main publicKey)).run).IsQueryBoundP (· matches Sum.inr _) q)
    (result : (Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hresult : result ∈ support
      (gameRestWithFullTrace adversary publicKey secretKey initialCache)) :
    result.2.2.hashQueries.length ≤ q := by
  rw [gameRestWithFullTrace, mem_support_bind_iff] at hresult
  obtain ⟨⟨forgery, adversaryCache, trace⟩, hadversary, hfinish⟩ := hresult
  rw [mem_support_bind_iff] at hfinish
  obtain ⟨⟨verified, finalCache⟩, hverify, hpure⟩ := hfinish
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rw [FullAdversaryTrace.hashQueries, directHashQueries_length_eq_countQ]
  have hdirect := fullTracedMappedAdversaryImpl_direct_countQ_le_of_expanded secretKey
    (adversary.main publicKey) q
    (isQueryBoundP_expandedAdversaryImpl secretKey (adversary.main publicKey) q hbound)
    initialCache ⟨[], [], []⟩ (forgery, adversaryCache, trace) hadversary
  simpa [QueryLog.countQ] using hdirect

namespace Concrete

theorem gameAfterSecretsWithFullTrace_hashQueries_length_le
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hresult : result ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret)) :
    result.2.2.hashQueries.length ≤ q := by
  have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts
  rw [gameAfterSecrets] at hgame
  rw [gameAfterSecretsWithFullTrace, mem_support_bind_iff] at hresult
  obtain ⟨⟨root, rootCache⟩, hroot, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨restResult, hrest, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hrootSupport : root ∈ support
      (liftM ((treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
        OracleComp HashSpec Digest)) : OracleComp OracleWorld Digest) := by
    apply support_simulateQ_run'_subset romImpl _ ∅
    rw [StateT.run'_eq, support_map]
    exact ⟨(root, rootCache), hroot, rfl⟩
  have hrestBound := isQueryBoundP_of_bind hgame root hrootSupport
  rw [gameRest] at hrestBound
  have hadversaryBound := IsQueryBoundP.of_bind_left hrestBound
  exact gameRestWithFullTrace_hashQueries_length_le_of_bound adversary
    (⟨root, parameter⟩ : PublicKey)
    (⟨parameter, root, otsSecret, ftsSecret⟩ : SecretKey)
    rootCache q hadversaryBound restResult hrest

end Concrete

end SphincsSecurity
