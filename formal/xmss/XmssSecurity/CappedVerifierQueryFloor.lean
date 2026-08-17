import XmssSecurity.CappedEncodingRejection
import XmssSecurity.CappedChain.ChainInputTrace

open OracleComp OracleSpec
open scoped BigOperators

namespace XmssSecurity

set_option maxHeartbeats 2000000

inductive ExactQueryCount {index : Type} {spec : OracleSpec index} :
    OracleComp spec α → Nat → Prop where
  | pure (value : α) : ExactQueryCount (pure value) 0
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (count : Nat) (hnext : ∀ output, ExactQueryCount (next output) count) :
      ExactQueryCount (liftM (spec.query input) >>= next) (count + 1)

inductive ExactPredicateQueryCount {index : Type} {spec : OracleSpec index}
    (predicate : spec.Domain → Prop) : OracleComp spec α → Nat → Prop where
  | pure (value : α) : ExactPredicateQueryCount predicate (pure value) 0
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (count : Nat) (hinput : predicate input)
      (hnext : ∀ output, ExactPredicateQueryCount predicate (next output) count) :
      ExactPredicateQueryCount predicate
        (liftM (spec.query input) >>= next) (count + 1)

namespace ExactQueryCount

theorem exists_queryBoundP_continuation
    {index : Type} {spec : OracleSpec index} [OracleSpec.Inhabited spec]
    {predicate : spec.Domain → Prop} [DecidablePred predicate]
    {head : OracleComp spec α} {next : α → OracleComp spec β} {bound : Nat}
    (hbound : (head >>= next).IsQueryBoundP predicate bound) :
    ∃ value, (next value).IsQueryBoundP predicate bound := by
  induction head using OracleComp.inductionOn generalizing bound with
  | pure value => exact ⟨value, by simpa using hbound⟩
  | query_bind input rest ih =>
      rw [bind_assoc, OracleComp.isQueryBoundP_query_bind_iff] at hbound
      obtain ⟨value, hvalue⟩ := ih default (hbound.2 default)
      exact ⟨value, hvalue.mono (by split <;> omega)⟩

theorem source_isQueryBoundP_of_liftComp
    {index : Type} {spec : OracleSpec index}
    {superIndex : Type} {superSpec : OracleSpec superIndex}
    [inclusion : spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]
    {computation : OracleComp spec α}
    {sourcePredicate : spec.Domain → Prop} [DecidablePred sourcePredicate]
    {targetPredicate : superSpec.Domain → Prop} [DecidablePred targetPredicate]
    {bound : Nat}
    (hpredicate : ∀ input,
      sourcePredicate input ↔ targetPredicate (inclusion.onQuery input))
    (hbound : (OracleComp.liftComp computation superSpec).IsQueryBoundP
      targetPredicate bound) :
    computation.IsQueryBoundP sourcePredicate bound := by
  induction computation using OracleComp.inductionOn generalizing bound with
  | pure value => trivial
  | query_bind input next ih =>
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query] at hbound
      change (((liftM (spec.query input) :
        OracleComp superSpec (spec.Range input)) >>= fun output =>
          OracleComp.liftComp (next output) superSpec).IsQueryBoundP
            targetPredicate bound) at hbound
      rw [show
          (liftM (spec.query input) : OracleComp superSpec (spec.Range input)) =
            liftM (superSpec.query (inclusion.onQuery input)) >>= fun output =>
              Pure.pure (inclusion.onResponse input output) by
        change ((liftM (spec.query input) :
          OracleQuery superSpec (spec.Range input)) :
            OracleComp superSpec (spec.Range input)) = _
        rw [show
            (liftM (spec.query input) : OracleQuery superSpec (spec.Range input)) =
              ⟨inclusion.onQuery input, inclusion.onResponse input⟩ from
          inclusion.liftM_eq_lift _]
        rfl, bind_assoc, OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      constructor
      · simpa [hpredicate input] using hbound.1
      · intro sourceOutput
        obtain ⟨targetOutput, htargetOutput⟩ :=
          (OracleSpec.LawfulSubSpec.onResponse_bijective
            (spec := spec) (superSpec := superSpec) input).2 sourceOutput
        have hcontinuation := hbound.2 targetOutput
        simp only [pure_bind, htargetOutput] at hcontinuation
        have hrec := ih sourceOutput hcontinuation
        simpa [hpredicate input] using hrec

theorem bind {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactQueryCount computation count)
    (next : α → OracleComp spec β) (nextCount : Nat)
    (hnext : ∀ value, ExactQueryCount (next value) nextCount) :
    ExactQueryCount (computation >>= next) (count + nextCount) := by
  induction hcomputation with
  | pure value => simpa using hnext value
  | query input rest restCount hrest ih =>
      rw [bind_assoc]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ExactQueryCount.query input (fun output => rest output >>= next)
          (restCount + nextCount) ih

theorem map {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactQueryCount computation count) (f : α → β) :
    ExactQueryCount (f <$> computation) count := by
  convert hcomputation.bind
    (fun value => (Pure.pure (f value) : OracleComp spec β)) 0
    (fun value => ExactQueryCount.pure (f value)) using 1 <;>
    simp [map_eq_bind_pure_comp]

theorem le_of_isTotalQueryBound [OracleSpec.Inhabited spec]
    {computation : OracleComp spec α} {count bound : Nat}
    (hexact : ExactQueryCount computation count)
    (hbound : computation.IsTotalQueryBound bound) :
    count ≤ bound := by
  induction hexact generalizing bound with
  | pure value => exact Nat.zero_le bound
  | query input next count hnext ih =>
      rw [OracleComp.isTotalQueryBound_query_bind_iff] at hbound
      have hrec := ih default (bound := bound - 1) (hbound.2 default)
      omega

theorem liftComp_predicate
    {superIndex : Type} {superSpec : OracleSpec superIndex}
    [inclusion : spec ⊂ₒ superSpec]
    {computation : OracleComp spec α} {count : Nat}
    (hexact : ExactQueryCount computation count)
    (predicate : superSpec.Domain → Prop)
    (hpredicate : ∀ input, predicate (inclusion.onQuery input)) :
    ExactPredicateQueryCount predicate
      (OracleComp.liftComp computation superSpec) count := by
  induction hexact with
  | pure value => exact .pure value
  | query input next count hnext ih =>
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change ExactPredicateQueryCount predicate
        (((liftM (spec.query input) : OracleComp superSpec (spec.Range input)) >>=
          fun output => OracleComp.liftComp (next output) superSpec)) (count + 1)
      rw [show
          (liftM (spec.query input) : OracleComp superSpec (spec.Range input)) =
            liftM (superSpec.query (inclusion.onQuery input)) >>= fun output =>
              Pure.pure (inclusion.onResponse input output) by
        change ((liftM (spec.query input) :
          OracleQuery superSpec (spec.Range input)) :
            OracleComp superSpec (spec.Range input)) = _
        rw [show
            (liftM (spec.query input) : OracleQuery superSpec (spec.Range input)) =
              ⟨inclusion.onQuery input, inclusion.onResponse input⟩ from
          inclusion.liftM_eq_lift _]
        rfl, bind_assoc]
      exact .query (inclusion.onQuery input)
        (fun output => OracleComp.liftComp
          (next (inclusion.onResponse input output)) superSpec)
        count (hpredicate input) (fun output => by
          simpa only [pure_bind] using ih (inclusion.onResponse input output))

namespace ExactPredicateQueryCount

theorem le_of_isQueryBoundP
    {index : Type} {spec : OracleSpec index} [OracleSpec.Inhabited spec]
    {predicate : spec.Domain → Prop} [DecidablePred predicate]
    {computation : OracleComp spec α} {count bound : Nat}
    (hexact : ExactPredicateQueryCount predicate computation count)
    (hbound : computation.IsQueryBoundP predicate bound) :
    count ≤ bound := by
  induction hexact generalizing bound with
  | pure value => exact Nat.zero_le bound
  | query input next count hinput hnext ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      have hpositive : 0 < bound := hbound.1.resolve_left (not_not.mpr hinput)
      have hrest : (next default).IsQueryBoundP predicate (bound - 1) := by
        simpa [hinput] using hbound.2 default
      have hrec := ih default (bound := bound - 1) hrest
      omega

end ExactPredicateQueryCount

theorem oracleHash (input : HashInput) :
    ExactQueryCount (Concrete.oracleHash input : OracleComp HashSpec HashOutput) 1 := by
  exact .query input (fun output => (Pure.pure output : OracleComp HashSpec HashOutput)) 0
    (fun output => ExactQueryCount.pure output)

theorem tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    ExactQueryCount
      (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest) 1 := by
  unfold Concrete.tweakableHash
  exact (oracleHash _).map truncateHash

theorem chainWalk (parameter : PublicParameter) (epoch : Epoch)
    (chain : ChainIndex) (position steps : Nat) (value : Digest)
    (hposition : position + steps ≤ chainLength - 1) :
    ExactQueryCount
      (Concrete.chainWalk (m := OracleComp HashSpec) parameter epoch chain
        position steps value) steps := by
  induction steps generalizing value with
  | zero => exact .pure value
  | succ steps ih =>
      rw [Concrete.chainWalk]
      have hstep : position + steps < chainLength - 1 := by omega
      simp only [hstep, ↓reduceDIte]
      exact (ih value (by omega)).bind
        (fun previous => Concrete.chainHash parameter epoch chain
          ⟨position + steps, hstep⟩ previous) 1
        (fun previous => tweakableHash parameter (.chain epoch chain
          ⟨position + steps, hstep⟩) (Concrete.digestBytes previous))

theorem recoverChain (parameter : PublicParameter) (epoch : Epoch)
    (chain : ChainIndex) (digit : Digit) (value : Digest) :
    ExactQueryCount
      (Concrete.recoverChain (m := OracleComp HashSpec) parameter epoch chain digit value)
      (chainLength - 1 - digit.val) := by
  unfold Concrete.recoverChain
  apply chainWalk
  have hdigit : digit.val ≤ chainLength - 1 := Nat.le_pred_of_lt digit.isLt
  omega

theorem sequenceFin {n : Nat} (computation : Fin n → OracleComp spec α)
    (count : Fin n → Nat)
    (hcomputation : ∀ index, ExactQueryCount (computation index) (count index)) :
    ExactQueryCount (Concrete.sequenceFin computation)
      (∑ index, count index) := by
  induction n with
  | zero => exact .pure Fin.elim0
  | succ n ih =>
      rw [Concrete.sequenceFin, Fin.sum_univ_succ]
      exact (hcomputation 0).bind
        (fun head => do
          let tail ← Concrete.sequenceFin fun index : Fin n => computation index.succ
          Pure.pure (show Fin (n + 1) → α from Fin.cases head tail))
        (∑ index : Fin n, count index.succ)
        (fun head => (ih (fun index => computation index.succ)
          (fun index => count index.succ) (fun index => hcomputation index.succ)).bind
            (fun tail => Pure.pure
              (show Fin (n + 1) → α from Fin.cases head tail)) 0
            (fun tail => ExactQueryCount.pure
              (show Fin (n + 1) → α from Fin.cases head tail)))

theorem recoverEndpoints (parameter : PublicParameter) (epoch : Epoch)
    (encoding : Encoding) (signature : Signature) :
    ExactQueryCount
      (Concrete.recoverEndpoints (m := OracleComp HashSpec) parameter epoch encoding signature)
      (TargetSum.verificationWork encoding) := by
  unfold Concrete.recoverEndpoints TargetSum.verificationWork
  exact sequenceFin _ _ fun chain => recoverChain parameter epoch chain
    (encoding chain) (signature.chainValue chain)

end ExactQueryCount

theorem Concrete.verify_hashQueryBound_at_least_verificationWork
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) (q : Nat)
    (hbound : (Concrete.cappedScheme.verify publicKey epoch message signature)
      |>.IsQueryBoundP (· matches .inr _) q) :
    verificationChainHashes + 1 ≤ q := by
  obtain ⟨digest, hdigestMem⟩ := TargetSum.validDigests_nonempty
  have hdigestValid : TargetSum.ValidDigest digest :=
    (TargetSum.mem_validDigests_iff digest).mp hdigestMem
  obtain ⟨encoding, hdecode⟩ := hdigestValid
  let output : HashOutput := Rom.hashOutputEquivDigestPair.symm (0, digest)
  have htruncate : truncateHash output = digest := by
    have hpair := Rom.hashOutputEquivDigestPair.apply_symm_apply (0, digest)
    exact congrArg Prod.snd hpair
  change (liftM (Concrete.verify publicKey epoch message signature :
    OracleComp HashSpec Bool) : OracleComp OracleWorld Bool)
      |>.IsQueryBoundP (· matches .inr _) q at hbound
  have hsource :
      (Concrete.verify publicKey epoch message signature :
        OracleComp HashSpec Bool).IsQueryBoundP (fun _ => True) q :=
    ExactQueryCount.source_isQueryBoundP_of_liftComp
      (fun input => by
        change True ↔ ((Sum.inr input : OracleWorld.Domain) matches .inr _)
        simp) hbound
  have hsourceTotal :
      (Concrete.verify publicKey epoch message signature :
        OracleComp HashSpec Bool).IsTotalQueryBound q := by
    simpa [OracleComp.IsTotalQueryBound, OracleComp.IsQueryBoundP] using hsource
  let input := tweakableHashInput publicKey.parameter (.encoding epoch)
    (Concrete.encodingPayload message signature.randomness)
  change ((liftM (HashSpec.query input) >>= fun firstOutput =>
    match TargetSum.decodeDigest (truncateHash firstOutput) with
    | none => Pure.pure false
    | some decoded => do
        let endpoints ← Concrete.recoverEndpoints publicKey.parameter epoch decoded signature
        let leaf ← Concrete.leafHash publicKey.parameter epoch endpoints
        Concrete.verifyAfterLeaf publicKey epoch signature leaf) :
      OracleComp HashSpec Bool).IsTotalQueryBound q at hsourceTotal
  rw [OracleComp.isTotalQueryBound_query_bind_iff] at hsourceTotal
  have hafter := hsourceTotal.2 output
  simp only [htruncate, hdecode] at hafter
  have hrecover :
      (Concrete.recoverEndpoints (m := OracleComp HashSpec)
        publicKey.parameter epoch encoding signature).IsTotalQueryBound (q - 1) :=
    OracleComp.IsTotalQueryBound.of_bind_left hafter
  have hexactHash := ExactQueryCount.recoverEndpoints publicKey.parameter epoch
    encoding signature
  have hlower := hexactHash.le_of_isTotalQueryBound hrecover
  rw [TargetSum.verificationWork_eq encoding
    ((TargetSum.decodeDigest_eq_some_iff.mp hdecode).2)] at hlower
  omega

theorem hashQueryBound_at_least_numChains
    (adversary : Adversary Concrete.cappedScheme) (q : Nat)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q) :
    numChains ≤ q := by
  have hdetailed :=
    (hasHashQueryBound_iff_detailedGameCore Concrete.cappedScheme adversary q).mp
      hbound
  unfold detailedGameCore at hdetailed
  obtain ⟨key, hafterKeygen⟩ :=
    ExactQueryCount.exists_queryBoundP_continuation hdetailed
  unfold detailedGameAfterKeygen at hafterKeygen
  obtain ⟨adversaryResult, hfinish⟩ :=
    ExactQueryCount.exists_queryBoundP_continuation hafterKeygen
  have hverify :
      (Concrete.cappedScheme.verify key.1 adversaryResult.1.epoch
        adversaryResult.1.message adversaryResult.1.signature)
          |>.IsQueryBoundP (· matches .inr _) q :=
    OracleComp.IsQueryBoundP.of_bind_left hfinish
  have hlower := Concrete.verify_hashQueryBound_at_least_verificationWork
    key.1 adversaryResult.1.epoch adversaryResult.1.message
    adversaryResult.1.signature q hverify
  rw [verificationChainHashes_eq] at hlower
  change 42 ≤ q
  omega

end XmssSecurity
