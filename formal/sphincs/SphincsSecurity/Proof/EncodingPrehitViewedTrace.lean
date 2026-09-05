import SphincsSecurity.Proof.EncodingPrehitComposition
import SphincsSecurity.Proof.EncodingPrehitGame

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec TightEncoding

noncomputable def encodingPrehitViewedAdversaryImpl (accountingKey secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (ViewedFullTraceState × Bool) ProbComp) := by
  intro input
  cases input with
  | inl query =>
      exact fun state => do
        let result ← runEncodingPrehitMonitor accountingKey (OracleWorld.query query) state.1.cache state.2
        let trace := fullAdversaryTraceUpdate (.inl query) state.1.cache result.1.1 result.1.2 state.1.trace
        pure (result.1.1, (⟨result.1.2, trace, state.1.views, state.1.targetView⟩, result.2))
  | inr request =>
      exact fun state => do
        let result ← runEncodingPrehitMonitor accountingKey (signWithView secretKey request) state.1.cache state.2
        let trace := fullAdversaryTraceUpdate (.inr request) state.1.cache result.1.1.1 result.1.2 state.1.trace
        pure (result.1.1.1, (⟨result.1.2, trace, state.1.views ++ [result.1.1.2], state.1.targetView⟩, result.2))

theorem encodingPrehitViewedAdversaryImpl_query_projection
    (accountingKey secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : ViewedFullTraceState × Bool) :
    (fun result => (result.1, result.2.1)) <$>
      (encodingPrehitViewedAdversaryImpl accountingKey secretKey input).run state =
      (viewedFullTracedMappedAdversaryImpl secretKey input).run state.1 := by
  cases input with
  | inl query =>
      have hp := runEncodingPrehitMonitor_project accountingKey
        (liftM (OracleWorld.query query) : OracleComp OracleWorld _) state.1.cache state.2
      rw [simulateQ_spec_query] at hp
      change Prod.fst <$> runEncodingPrehitMonitor accountingKey
        (liftM (OracleWorld.query query) : OracleComp OracleWorld _) state.1.cache state.2 =
          romImpl query state.1.cache at hp
      have h := congrArg (fun run =>
            (fun result => (result.1, (⟨result.2,
              fullAdversaryTraceUpdate (.inl query) state.1.cache result.1 result.2 state.1.trace,
              state.1.views, state.1.targetView⟩ : ViewedFullTraceState))) <$> run) hp
      cases query <;>
        simpa [encodingPrehitViewedAdversaryImpl, viewedFullTracedMappedAdversaryImpl, StateT.run] using h
  | inr request =>
      have hp := runEncodingPrehitMonitor_project accountingKey
        (signWithView secretKey request) state.1.cache state.2
      change Prod.fst <$> runEncodingPrehitMonitor accountingKey
        (signWithView secretKey request) state.1.cache state.2 =
          simulateQ romImpl (signWithView secretKey request) state.1.cache at hp
      simpa [encodingPrehitViewedAdversaryImpl, viewedFullTracedMappedAdversaryImpl,
        StateT.run] using congrArg (fun run =>
          (fun result => (result.1.1, (⟨result.2,
            fullAdversaryTraceUpdate (.inr request) state.1.cache result.1.1 result.2 state.1.trace,
            state.1.views ++ [result.1.2], state.1.targetView⟩ : ViewedFullTraceState))) <$> run) hp

theorem encodingPrehitViewedAdversaryImpl_projection
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool) :
    Prod.map id Prod.fst <$>
      (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state =
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey) computation).run state.1 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
    (viewedFullTracedMappedAdversaryImpl secretKey) Prod.fst
  exact encodingPrehitViewedAdversaryImpl_query_projection accountingKey secretKey

noncomputable def gameRestWithEncodingPrehitView (adversary : Adversary)
    (accountingKey : SecretKey) (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) (hit : Bool) :
    ProbComp ((Forgery × Bool) × (ViewedFullTraceState × Bool)) := do
  let (forgery, state) ←
    (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
      (adversary.main publicKey)).run (⟨initialCache, ⟨[], [], []⟩, [], none⟩, hit)
  let result ← runEncodingPrehitMonitor accountingKey
    (liftM (verifyWithView publicKey forgery.message forgery.signature) :
      OracleComp OracleWorld (Bool × FewTimeView)) state.1.cache state.2
  let log := state.1.trace.signing.toSigningLog
  let verdict := decide (SigningTranscript.Valid log ∧ ¬ SigningTranscript.Contains log forgery) && result.1.1.1
  pure ((forgery, verdict), (⟨result.1.2, state.1.trace, state.1.views, some result.1.1.2⟩, result.2))

theorem gameRestWithEncodingPrehitView_projection (adversary : Adversary)
    (accountingKey : SecretKey) (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) (hit : Bool) :
    (fun result => (result.1, result.2.1)) <$>
      gameRestWithEncodingPrehitView adversary accountingKey publicKey secretKey initialCache hit =
      gameRestWithViewTrace adversary publicKey secretKey initialCache := by
  rw [gameRestWithEncodingPrehitView, gameRestWithViewTrace,
    ← encodingPrehitViewedAdversaryImpl_projection accountingKey secretKey
      (adversary.main publicKey) (⟨initialCache, ⟨[], [], []⟩, [], none⟩, hit)]
  simp only [map_bind, bind_map_left, Prod.map, id_eq]
  apply bind_congr
  intro result
  rw [← runEncodingPrehitMonitor_project accountingKey
    (liftM (verifyWithView publicKey result.1.message result.1.signature) :
      OracleComp OracleWorld (Bool × FewTimeView)) result.2.1.cache result.2.2]
  simp

noncomputable def gameAfterSecretsWithEncodingPrehitView (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ProbComp ((Digest × Forgery × Bool) × (ViewedFullTraceState × Bool)) := do
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  let rootResult ← runEncodingPrehitMonitor accountingKey
    (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
      OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) ∅ false
  let result ← gameRestWithEncodingPrehitView adversary accountingKey ⟨rootResult.1.1, parameter⟩
    ⟨parameter, rootResult.1.1, otsSecret, ftsSecret⟩ rootResult.1.2 rootResult.2
  pure ((rootResult.1.1, result.1.1, result.1.2), result.2)

theorem gameAfterSecretsWithEncodingPrehitView_projection (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (fun result => (result.1, result.2.1)) <$>
      gameAfterSecretsWithEncodingPrehitView adversary parameter otsSecret ftsSecret =
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret := by
  rw [gameAfterSecretsWithEncodingPrehitView, gameAfterSecretsWithViewTrace,
    ← runEncodingPrehitMonitor_project (primitiveAccountingKey parameter otsSecret ftsSecret)
      (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
        OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) ∅ false]
  simp only [map_bind, bind_map_left]
  apply bind_congr
  intro result
  rw [← gameRestWithEncodingPrehitView_projection adversary
    (primitiveAccountingKey parameter otsSecret ftsSecret) ⟨result.1.1, parameter⟩
    ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ result.1.2 result.2]
  simp

end SphincsSecurity.Concrete
