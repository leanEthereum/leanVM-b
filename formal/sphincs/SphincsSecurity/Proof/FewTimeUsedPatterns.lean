import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimePadding

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

abbrev UsedFewTimePattern (signatures distinct : Nat) :=
  {pattern : FewTimePattern signatures distinct // Function.Surjective pattern.assignment}

theorem FewTimeCover.pattern_assignment_surjective {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {index : Index} {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    Function.Surjective cover.pattern.assignment := by
  intro selected
  obtain ⟨entry, _, hentry⟩ := Finset.mem_image.mp selected.2
  refine ⟨cover.representativeTree entry, ?_⟩
  apply Subtype.ext
  change cover.logIndex ⟨(cover.select (cover.representativeTree entry)).entry.flat, _⟩ = selected.1
  rw [← hentry]
  congr 1
  exact Subtype.ext (cover.representativeTree_spec entry)

theorem FewTimePattern.pad_assignment_surjective {small large distinct : Nat}
    (pattern : FewTimePattern small distinct) (hle : small ≤ large)
    (hsurjective : Function.Surjective pattern.assignment) :
    Function.Surjective (pattern.pad hle).assignment := by
  intro selected
  obtain ⟨position, hposition, hselected⟩ := Finset.mem_map.mp selected.2
  obtain ⟨tree, htree⟩ := hsurjective ⟨position, hposition⟩
  refine ⟨tree, Subtype.ext ?_⟩
  change finCastLEEmbedding hle (pattern.assignment tree).1 = selected.1
  rw [htree]
  exact hselected

end SphincsSecurity.Concrete
