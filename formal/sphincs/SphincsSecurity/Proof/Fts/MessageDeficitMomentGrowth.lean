import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.AdmissibleHashMoments
import SphincsSecurity.Proof.Fts.MessageDeficitScore

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def messageDeficitMoment (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (power : Nat) : ENNReal :=
  ∑ message : Message, positiveScoreMoment (messageDeficitScore parameter root message cache) power

theorem positiveScoreMoment_le_messageDeficitMoment (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (power : Nat) (message : Message) :
    positiveScoreMoment (messageDeficitScore parameter root message cache) power ≤
      messageDeficitMoment parameter root cache power := by
  unfold messageDeficitMoment
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun message : Message => positiveScoreMoment (messageDeficitScore parameter root message cache) power)
    (fun _ _ => zero_le) (Finset.mem_univ message)

theorem messageDeficitMoment_zero_of_no_inputs (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hcount : ∀ message, cachedMessageEntryCount cache parameter root message = 0)
    (power : Nat) (hpower : power ≠ 0) : messageDeficitMoment parameter root cache power = 0 := by
  apply Finset.sum_eq_zero
  intro message _
  exact positiveScoreMoment_zero_of_nonpos _
    (messageDeficitScore_of_no_inputs parameter root message cache (hcount message)) power hpower

end SphincsSecurity
