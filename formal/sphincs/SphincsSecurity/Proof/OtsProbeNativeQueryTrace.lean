import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeCanonicalQuerySelection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open _root_.OracleComp.DeferredSampling

attribute [local instance] Classical.propDecidable

noncomputable def runNativeQueryTrace
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache →
      ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) :=
  OracleComp.construct
    (fun value context fuel table cache =>
      if DeferredCompletable table context then pure (some ⟨context, fuel, (value, cache), table⟩, [])
      else pure (none, []))
    (fun input _ next context fuel table cache =>
      if DeferredCompletable table context then do
        let result ← runResolvedFromTable context fuel table
          ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
        let tail ← match result with
          | none => pure (none, [])
          | some result => next result.value.1 result.context result.remaining result.table result.value.2
        pure (tail.1, (⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection) :: tail.2)
      else pure (none, [])) computation

theorem runNativeQueryTrace_query_bind
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runNativeQueryTrace parameter root ftsSecret (OracleSpec.query input >>= next) context fuel table cache =
      if DeferredCompletable table context then do
        let result ← runResolvedFromTable context fuel table
          ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
        let tail ← match result with
          | none => pure (none, [])
          | some result =>
              runNativeQueryTrace parameter root ftsSecret (next result.value.1)
                result.context result.remaining result.table result.value.2
        pure (tail.1, (⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection) :: tail.2)
      else pure (none, []) := rfl

theorem runNativeQueryTrace_of_not_completable
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hnot : ¬DeferredCompletable table context) :
    runNativeQueryTrace parameter root ftsSecret computation context fuel table cache = pure (none, []) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [runNativeQueryTrace, OracleComp.construct_pure, hnot, ↓reduceIte]
  | query_bind input next _ => rw [runNativeQueryTrace_query_bind, if_neg hnot]

end SphincsSecurity.Concrete.OtsProbeSimulation
