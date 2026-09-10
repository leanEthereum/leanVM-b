import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootSwapStep

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem nativeRootHashSafe_failure_classify
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (input : HashInput) (context : DeferredContext)
    (hunsafe : ¬NativeRootHashSafe parameter target before after input context) :
    ¬RootInputAvoids parameter target (truncateHash before) (truncateHash after) input ∨
      (∃ candidate, (purePlanProbingHashQuery parameter input (replaceNativePosition target before context).state).candidate? = some candidate ∧
        IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate)) ∨
      ¬NativeRootActionSafe parameter target input (replaceNativePosition target before context)
        (replaceNativePosition target after context)
        (purePlanProbingHashQuery parameter input (replaceNativePosition target before context).state).action := by
  unfold NativeRootHashSafe at hunsafe
  by_cases hencoding : RootInputAvoids parameter target (truncateHash before) (truncateHash after) input
  · by_cases hprobe : ∀ candidate,
        (purePlanProbingHashQuery parameter input (replaceNativePosition target before context).state).candidate? = some candidate →
          ¬IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate)
    · exact Or.inr (Or.inr (fun haction => hunsafe ⟨hencoding, hprobe, haction⟩))
    · push Not at hprobe
      exact Or.inr (Or.inl hprobe)
  · exact Or.inl hencoding

end SphincsSecurity.Concrete.OtsProbeSimulation
