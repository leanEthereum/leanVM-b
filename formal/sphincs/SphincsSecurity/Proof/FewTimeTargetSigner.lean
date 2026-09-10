import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeSignerView

/-!
# Signer selection witnesses for target monitoring

This richer proof-only signer retains the exact selected message-digest input. Forgetting that input
recovers `signWithView`. It lets a later monitor recognize a fresh selected view even when signature
construction returns `none`.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

abbrev TargetSignerResult := Option Signature × Option (HashInput × FewTimeView)

def targetSignerResultView (result : TargetSignerResult) :
    Option Signature × Option FewTimeView :=
  (result.1, result.2.map Prod.snd)

noncomputable def signWithTargetView (secretKey : SecretKey) (message : Message) :
    OracleComp OracleWorld TargetSignerResult := do
  match ← signDigestLoop digestAttemptLimit secretKey message with
  | none => pure (none, none)
  | some (randomness, index, leaves) => do
      let signature ← liftM (signAfterDigest secretKey randomness index leaves)
      let input := tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)
      pure (signature, some (input, selectedFewTimeView index leaves))

theorem signWithTargetView_projection (secretKey : SecretKey) (message : Message) :
    targetSignerResultView <$> signWithTargetView secretKey message =
      signWithView secretKey message := by
  simp only [signWithTargetView, signWithView, map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro loopResult
  cases loopResult with
  | none => simp [targetSignerResultView]
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      simp [targetSignerResultView]

theorem simulateQ_signWithTargetView_projection_run
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (fun result => (targetSignerResultView result.1, result.2)) <$>
        (simulateQ romImpl (signWithTargetView secretKey message)).run cache =
      (simulateQ romImpl (signWithView secretKey message)).run cache := by
  calc
    _ = (simulateQ romImpl
        (targetSignerResultView <$> signWithTargetView secretKey message)).run cache := by
      rw [simulateQ_map, StateT.run_map]
    _ = _ := by rw [signWithTargetView_projection]

def freshTargetSignerView? (initialCache : QueryCache HashSpec)
    (result : TargetSignerResult × QueryCache HashSpec) : Option FewTimeView :=
  match result.1.2 with
  | none => none
  | some (input, view) => if initialCache input = none then some view else none

end SphincsSecurity.Concrete
