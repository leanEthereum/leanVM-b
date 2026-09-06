import SphincsSecurity.Proof.JointProbeEncodingPotential
import SphincsSecurity.Proof.EncodingExhaustionTotalPotential

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

theorem jointCachePotentialBound_totalEncoding
    (source : JointSource α)
    (hbound : ∀ parameter position message, JointCachePotentialBound
      (encodingExhaustionPotential (encodingRetryInputs parameter position message)) source) :
    JointCachePotentialBound encodingExhaustionTotalPotential source :=
  JointCachePotentialBound.sum (Finset.univ : Finset EncodingRetryFamily)
    (fun family => encodingExhaustionPotential (encodingRetryInputs family.1 family.2.1 family.2.2))
    source (fun family _ => hbound family.1 family.2.1 family.2.2)

theorem jointCachePotentialBound_retained_totalEncoding
    (adversary : Adversary) (parameter : PublicParameter) (q : Nat) :
    JointCachePotentialBound encodingExhaustionTotalPotential (jointSourceRetained adversary parameter q) :=
  jointCachePotentialBound_totalEncoding _
    (fun encodingParameter position message =>
      jointCachePotentialBound_retained_encoding encodingParameter position message adversary parameter q)

def JointRawAnyEncodingInputsExhausted :
    AdaptiveRevealProbe.RawResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache))) → Prop
  | .stopped _ => False
  | .done _ _ none => False
  | .done _ _ (some result) => AnyEncodingInputsExhausted (ordinaryQueryCache result.value.2.2)

theorem probEvent_jointRaw_anyEncodingInputsExhausted_le
    (source : JointSource α) (hbound : JointCachePotentialBound encodingExhaustionTotalPotential source)
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat)
    (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (cache : JointSourceCache) :
    Pr[JointRawAnyEncodingInputsExhausted | AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved (source.run cache) context fuel otsTable)] ≤
        encodingExhaustionTotalPotential (ordinaryQueryCache cache.2) := by
  apply le_trans _ (hbound table state ftsFuel context fuel otsTable cache)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  cases result with
  | stopped hit => simp [JointRawAnyEncodingInputsExhausted, jointRawCachePotential]
  | done finalState remaining entry =>
      cases entry with
      | none => simp [JointRawAnyEncodingInputsExhausted, jointRawCachePotential]
      | some entry =>
          by_cases hexhausted : AnyEncodingInputsExhausted (ordinaryQueryCache entry.value.2.2)
          · simp only [JointRawAnyEncodingInputsExhausted, hexhausted, if_true, jointRawCachePotential]
            exact le_mul_of_one_le_right bot_le (one_le_encodingExhaustionTotalPotential_of_exhausted hexhausted)
          · simp [JointRawAnyEncodingInputsExhausted, hexhausted]

theorem probEvent_jointRaw_anyEncodingInputsExhausted_empty_le_inv216
    (source : JointSource α) (hbound : JointCachePotentialBound encodingExhaustionTotalPotential source)
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat)
    (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) :
    Pr[JointRawAnyEncodingInputsExhausted | AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved (source.run (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)) context fuel otsTable)] ≤
        ((2 ^ 216 : Nat) : ENNReal)⁻¹ :=
  (probEvent_jointRaw_anyEncodingInputsExhausted_le source hbound table state ftsFuel context fuel otsTable _).trans
    encodingExhaustionTotalPotential_empty_le_inv216

theorem probEvent_jointRaw_retained_anyEncodingInputsExhausted_le_inv216
    (adversary : Adversary) (parameter : PublicParameter) (q : Nat)
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat)
    (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) :
    Pr[JointRawAnyEncodingInputsExhausted | AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceRetained adversary parameter q).run
        (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)) context fuel otsTable)] ≤
        ((2 ^ 216 : Nat) : ENNReal)⁻¹ :=
  probEvent_jointRaw_anyEncodingInputsExhausted_empty_le_inv216 _
    (jointCachePotentialBound_retained_totalEncoding adversary parameter q) table state ftsFuel context fuel otsTable

end SphincsSecurity.Concrete.FtsProbeSimulation
