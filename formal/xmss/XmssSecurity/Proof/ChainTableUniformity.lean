import XmssSecurity.Proof.ChainHiddenTable
import XmssSecurity.Proof.ChainTrajectoryComposition
import Init.Data.Vector.OfFn

open OracleComp OracleSpec ENNReal

namespace XmssSecurity


theorem fullChainTrajectory_length_eq : chainLength - 1 + 1 = chainLength := by
  decide

def FullChainTrajectory.toDigitTable
    (values : FullChainTrajectory) : Digit → Digest := fun digit =>
  values[digit.val]'(by
    have hdigit := digit.isLt
    omega)

def FullChainTrajectory.ofDigitTable
  (values : Digit → Digest) : FullChainTrajectory :=
  Vector.ofFn fun index => values ⟨index.val, by
    have hindex := index.isLt
    simpa only [fullChainTrajectory_length_eq] using hindex⟩

noncomputable def epochPosition (epoch : Epoch) : Fin allEpochs.length :=
  ⟨allEpochs.idxOf epoch, List.idxOf_lt_length_iff.mpr (mem_allEpochs epoch)⟩

@[simp]
theorem allEpochs_get_epochPosition (epoch : Epoch) :
    allEpochs.get (epochPosition epoch) = epoch := by
  exact List.idxOf_get (List.idxOf_lt_length_iff.mpr (mem_allEpochs epoch))

noncomputable def listOfChainValueTable
    (table : ChainValueIndex → Digest) : List FullChainTrajectory :=
  allEpochs.map fun epoch =>
    FullChainTrajectory.ofDigitTable fun digit => table (epoch, digit)

@[simp]
noncomputable def chainValueTableOfList
    (values : List FullChainTrajectory) : ChainValueIndex → Digest := fun index =>
  if hlength : allEpochs.length = values.length then
    (values[(epochPosition index.1).val]'(by
      have hposition := (epochPosition index.1).isLt
      omega)).toDigitTable index.2
  else
    0

@[simp]
theorem listOfChainValueTable_chainValueTableOfList
    (values : List FullChainTrajectory) (hlength : values.length = lifetime) :
    listOfChainValueTable (chainValueTableOfList values) = values := by
  apply List.ext_getElem
  · simp [listOfChainValueTable, allEpochs_length, hlength]
  · intro index hleft hright
    simp only [listOfChainValueTable, List.getElem_map]
    apply Vector.ext
    intro digit hdigit
    unfold FullChainTrajectory.ofDigitTable chainValueTableOfList
    rw [Vector.getElem_ofFn]
    split
    · rename_i htableLength
      have hindex : index < allEpochs.length := by
        rw [allEpochs_length, ← hlength]
        exact hright
      have hposition : (epochPosition allEpochs[index]).val = index := by
        exact List.get_idxOf allEpochs_nodup ⟨index, hindex⟩
      have hvalue :
          values[(epochPosition allEpochs[index]).val] = values[index] := by
        rw [← Option.some_inj, ← List.getElem?_eq_getElem,
          ← List.getElem?_eq_getElem, hposition]
      dsimp only
      rw [hvalue]
      unfold FullChainTrajectory.toDigitTable
      rfl
    · rename_i htableLength
      exact (htableLength (allEpochs_length.trans hlength.symm)).elim

end XmssSecurity
