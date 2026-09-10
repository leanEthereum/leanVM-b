import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimePatterns

/-!
# Origins of selected few-time views

A selected cover entry always occupies its signer position. If its digest input was already cached,
it additionally has an earlier fresh direct-query source. This module packages those two disjoint
kinds of positions into one injective origin map.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

namespace Concrete

noncomputable def FewTimeCover.entriesEquivPatternSelected {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    cover.entries ≃ cover.pattern.selected := by
  classical
  let toSelected : cover.entries → cover.pattern.selected := fun entry =>
    ⟨cover.logIndex entry, by
      exact Finset.mem_image.2 ⟨entry, Finset.mem_univ _, rfl⟩⟩
  refine Equiv.ofBijective toSelected ⟨?_, ?_⟩
  · intro left right heq
    exact cover.logIndex_injective (congrArg Subtype.val heq)
  · intro selected
    obtain ⟨entry, _, hentry⟩ := Finset.mem_image.1 selected.2
    refine ⟨entry, Subtype.ext ?_⟩
    exact hentry

end Concrete

end SphincsSecurity
