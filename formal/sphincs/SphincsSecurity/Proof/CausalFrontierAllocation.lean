import SphincsSecurity.Proof.CausalFrontierProgram
import SphincsSecurity.Proof.QueryAllocation
import SphincsSecurity.Proof.BoundaryHashCost

namespace SphincsSecurity.Concrete.CausalFrontierProgram

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierSigningRun boundaryEval frontierRoot

def IsHash : OracleWorld.Domain → Prop := (· matches .inr _)

instance : DecidablePred IsHash := fun input => by unfold IsHash; infer_instance

theorem lift_prob_queryBound {Result : Type} (computation : ProbComp Result) :
    (liftM computation : OracleComp OracleWorld Result).IsQueryBoundP IsHash 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, isQueryBoundP_pure]
  | query_bind input next ih =>
      rw [liftM_bind]
      change ((liftM (OracleWorld.query (.inl input)) >>= fun answer => liftM (next answer)) :
        OracleComp OracleWorld Result).IsQueryBoundP IsHash 0
      simp only [isQueryBoundP_query_bind_iff, IsHash, Bool.false_eq_true, not_false_eq_true, true_or, ↓reduceIte, true_and]
      exact ih

private theorem withTrace_run {Input Trace : Type} {spec : OracleSpec Input} [Monoid Trace]
    (trace : (input : spec.Domain) → spec.Range input → Trace) (input : spec.Domain) :
    ((QueryImpl.id' spec).withTrace trace input).run =
      (fun answer => (answer, trace input answer)) <$> (liftM (spec.query input) : OracleComp spec _) := by
  simp [QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_tell]

theorem worldTrace_counted_le (parameter : PublicParameter) (input : OracleWorld.Domain)
    (result : (OracleWorld.Range input × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted IsHash
      ((QueryImpl.id' OracleWorld).withTrace (signingBoundaryTrace parameter) input).run)) :
    result.2 ≤ result.1.2.hashCalls := by
  rw [withTrace_run, QueryCap.counted_map, support_map] at hresult
  obtain ⟨original, horiginal, rfl⟩ := hresult
  rw [signingBoundaryTrace_hashCalls_eq]
  apply QueryCap.counted_le_of_queryBound IsHash _ _ _ original horiginal
  cases input <;> simp [isQueryBoundP_query_iff, IsHash]

theorem boundary_counted_le {Result : Type} (parameter : PublicParameter) (computation : OracleComp OracleWorld Result)
    (result : (Result × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted IsHash (boundaryComputation parameter computation))) :
    result.2 ≤ result.1.2.hashCalls :=
  QueryCap.counted_writer_simulate_le _ SigningBoundaryTrace.hashCalls SigningBoundaryTrace.hashCalls_mul _
    (worldTrace_counted_le parameter) computation result hresult

theorem adversaryImpl_counted_le (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (input : (OracleWorld + SigningSpec).Domain)
    (result : ((OracleWorld + SigningSpec).Range input × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted IsHash
      (adversaryImpl parameter root external ftsSecret words frontier input).run)) : result.2 ≤ result.1.2.hashCalls := by
  cases input with
  | inl input => exact worldTrace_counted_le parameter input result hresult
  | inr message =>
      rw [adversaryImpl_signing, WriterT.run_mk] at hresult
      have hzero := QueryCap.counted_le_of_queryBound _ _ 0 (lift_prob_queryBound _) result hresult
      exact hzero.trans (Nat.zero_le _)

theorem adversaryRun_counted_le {Result : Type} (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (result : ((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted IsHash
      (adversaryRun parameter root external ftsSecret words frontier computation))) : result.2 ≤ result.1.2.hashCalls :=
  QueryCap.counted_writer_simulate_le _ SigningBoundaryTrace.hashCalls SigningBoundaryTrace.hashCalls_mul _
    (adversaryImpl_counted_le parameter root external ftsSecret words frontier) (OtsPrefix.logged computation) result hresult

theorem gameRest_counted_le (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary)
    (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted IsHash
      (gameRest parameter root external ftsSecret words frontier adversary))) : result.2 ≤ result.1.2.hashCalls := by
  simp only [gameRest, QueryCap.counted_bind, QueryCap.counted_pure, bind_assoc, pure_bind, Nat.add_zero] at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨first, hfirst, hresult⟩ := hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨second, hsecond, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  rw [SigningBoundaryTrace.hashCalls_mul]
  exact Nat.add_le_add (adversaryRun_counted_le parameter root external ftsSecret words frontier _ first hfirst)
    (boundary_counted_le parameter _ second hsecond)

theorem game_counted_le (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted IsHash
      (game parameter external ftsSecret words frontier adversary))) : result.2 ≤ result.1.2.hashCalls := by
  rw [game, QueryCap.counted_map, support_map] at hresult
  obtain ⟨original, horiginal, rfl⟩ := hresult
  have h := gameRest_counted_le parameter _ external ftsSecret words frontier adversary original horiginal
  simp only [SigningBoundaryTrace.hashCalls_mul]
  omega

theorem game_recorded_le (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × List OracleWorld.Domain)
    (hresult : result ∈ support (QueryCap.recorded (game parameter external ftsSecret words frontier adversary))) :
    QueryCap.calls IsHash result.2 ≤ result.1.2.hashCalls :=
  QueryCap.recorded_calls_le IsHash _ (fun result => result.2.hashCalls)
    (game_counted_le parameter external ftsSecret words frontier adversary) result hresult

end SphincsSecurity.Concrete.CausalFrontierProgram
