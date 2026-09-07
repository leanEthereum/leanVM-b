import SphincsSecurity.Proof.JointProbeMessageReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

noncomputable def messageAnswers (parameter : PublicParameter) (cache : QueryCache HashSpec) : HashInput → Option HashOutput :=
  fun payload => cache (tweakableHashInput parameter .message payload)

namespace JointOriginal

theorem Frame.Valid.messageAnswers
    {parameter : PublicParameter} {otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput} {ftsTable : Coordinate → Digest}
    {frame : Frame} {cache : QueryCache HashSpec} (hvalid : frame.Valid parameter otsTable ftsTable cache) :
    FtsProbeSimulation.messageAnswers parameter cache =
      FtsProbeSimulation.messageAnswers parameter (ordinaryQueryCache frame.cache.2) := by
  rcases hvalid with ⟨_, _, hinvariant, _, _⟩
  rcases hinvariant with ⟨_, _, _, hcompletion, hpartition⟩
  funext payload
  have hm : MessageHashInput parameter (tweakableHashInput parameter .message payload) := ⟨payload, rfl⟩
  have hs := OtsProbeSimulation.stableOrdinaryInput_tweakableHashInput parameter .message payload (by trivial)
    (by simp) (by simp) (by simp)
  have heq := hpartition.eq_of_stable hcompletion _ hs
  change cache (tweakableHashInput parameter .message payload) =
    frame.cache.2 (.ordinary (tweakableHashInput parameter .message payload))
  rw [← heq]
  simp only [mergedCache, hm.nonSecret.2]

end JointOriginal
end SphincsSecurity.Concrete.FtsProbeSimulation
