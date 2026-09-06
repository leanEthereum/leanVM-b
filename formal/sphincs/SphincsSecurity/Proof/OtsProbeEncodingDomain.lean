import SphincsSecurity.Proof.OtsProbeEncodingPotentialSigner
import SphincsSecurity.Proof.OtsProbeNativeRootHashInput

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem encodingRetryInput_ne_position_tweak
    (encodingParameter parameter : PublicParameter) (encodingPosition : EncodingPosition)
    (message : Digest) (counter : Nat) (position : Position) (payload : HashInput) :
    encodingRetryInput encodingParameter encodingPosition message counter ≠
      tweakableHashInput parameter position.domain payload := by
  intro heq
  unfold encodingRetryInput tweakableHashInput at heq
  obtain ⟨hprefix, _⟩ := List.append_inj heq (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  have hdomain := tweakBytes_injective (show encodingPosition.domain.InRange from by trivial) position.domain_inRange htweak
  cases position <;> simp [EncodingPosition.domain, Position.domain] at hdomain

theorem purePeekTableInput_ne_encodingRetryInput
    (encodingParameter parameter : PublicParameter) (encodingPosition : EncodingPosition)
    (message : Digest) (counter : Nat) (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate) :
    purePeekTableInput parameter state coordinate ≠ some (encodingRetryInput encodingParameter encodingPosition message counter) := by
  have hne (position : Position) (payload : HashInput) :=
    Ne.symm (encodingRetryInput_ne_position_tweak encodingParameter parameter encodingPosition message counter position payload)
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [purePeekTableInput]
  | position position =>
      cases position <;> simp only [purePeekTableInput]
      case chain lay tree leafIdx chainIdx step =>
        split_ifs
        · cases state.values (.chainStart lay tree leafIdx chainIdx) <;> simp [hne]
        · cases purePeekPositionValues state (Position.chain lay tree leafIdx chainIdx step).children <;> simp [hne]
      all_goals split <;> simp_all

theorem purePeekTableInput_ne_of_mem_encodingRetryInputs
    (encodingParameter parameter : PublicParameter) (encodingPosition : EncodingPosition) (message : Digest)
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate) (input : HashInput)
    (hinput : input ∈ encodingRetryInputs encodingParameter encodingPosition message) :
    purePeekTableInput parameter state coordinate ≠ some input := by
  obtain ⟨counter, _, rfl⟩ := Finset.mem_image.mp hinput
  exact purePeekTableInput_ne_encodingRetryInput encodingParameter parameter encodingPosition message counter.val state coordinate

end SphincsSecurity.Concrete.OtsProbeSimulation
