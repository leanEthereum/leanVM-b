import XmssSecurity.CappedGlobalChainHighAttackerHashSimulator

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem globalChainTableEdgeInput_not_signingComparable
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    ¬ GlobalSigningComparableHashInput parameter
      (globalChainTableEdgeInput parameter table edge) := by
  rintro ⟨epoch, message, randomness, hencoding⟩
  have hprobe : globalChainInputProbe? parameter
      (Concrete.CacheView.chainInput parameter edge.2.1 edge.1 edge.2.2
        (table (edge.1, edge.2.1, chainStepDigit edge.2.2))) =
        some ((edge.1, edge.2.1, chainStepDigit edge.2.2),
          table (edge.1, edge.2.1, chainStepDigit edge.2.2)) := by
    exact globalChainInputProbe?_chainInput parameter edge.2.1 edge.1 edge.2.2
      (table (edge.1, edge.2.1, chainStepDigit edge.2.2))
  unfold globalChainTableEdgeInput at hencoding
  rw [hencoding, globalChainInputProbe?_encodingInput] at hprobe
  simp at hprobe

end XmssSecurity.CappedChain
