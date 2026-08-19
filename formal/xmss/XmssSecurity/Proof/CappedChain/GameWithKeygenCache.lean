import XmssSecurity.Proof.DetailedExecution

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def detailedGameWithKeygenCache
    (adversary : Adversary Concrete.scheme) :
    ProbComp (((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) :=
  (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅ >>= fun keyResult =>
    (fun execution => (keyResult, execution)) <$>
      (simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1
          keyResult.1.2)).run keyResult.2

end XmssSecurity.CappedChain
