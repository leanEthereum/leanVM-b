import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CacheMessageWeight
import SphincsSecurity.Proof.SignerInputWeight

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem cachedSignerInputWeight_le_cacheMessageEntryWeight (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (input : HashInput) :
    cachedSignerInputWeight key message before weight input ≤ cacheMessageEntryWeight key.parameter weight before input := by
  unfold cachedSignerInputWeight cacheMessageEntryWeight
  cases before input with
  | none => exact le_rfl
  | some output =>
      simp only
      split_ifs with hsource htarget
      · exact le_rfl
      · obtain ⟨randomness, heq⟩ := hsource.1
        exact (htarget ⟨⟨messageDigestPayload key.root message randomness, heq.symm⟩, hsource.2⟩).elim
      · exact bot_le
      · exact le_rfl

end SphincsSecurity.Concrete
