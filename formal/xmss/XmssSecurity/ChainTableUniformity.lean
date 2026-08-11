import XmssSecurity.ChainHiddenTable
import Init.Data.Vector.OfFn

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance chainTableSampleableDigest : SampleableType Digest :=
  SampleableType.ofFintype Digest

noncomputable local instance chainTableSampleableTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

theorem fullChainTrajectory_length_eq : chainLength - 1 + 1 = chainLength := by
  native_decide

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

@[simp]
theorem FullChainTrajectory.toDigitTable_ofDigitTable
    (values : Digit → Digest) :
    (FullChainTrajectory.ofDigitTable values).toDigitTable = values := by
  funext digit
  unfold FullChainTrajectory.ofDigitTable FullChainTrajectory.toDigitTable
  rw [Vector.getElem_ofFn]

@[simp]
theorem FullChainTrajectory.ofDigitTable_toDigitTable
    (values : FullChainTrajectory) :
    FullChainTrajectory.ofDigitTable values.toDigitTable = values := by
  apply Vector.ext
  intro index hindex
  unfold FullChainTrajectory.ofDigitTable FullChainTrajectory.toDigitTable
  rw [Vector.getElem_ofFn]

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
theorem listOfChainValueTable_length (table : ChainValueIndex → Digest) :
    (listOfChainValueTable table).length = lifetime := by
  simp [listOfChainValueTable, allEpochs_length]

noncomputable def chainValueTableOfList
    (values : List FullChainTrajectory) : ChainValueIndex → Digest := fun index =>
  if hlength : allEpochs.length = values.length then
    (values[(epochPosition index.1).val]'(by
      have hposition := (epochPosition index.1).isLt
      omega)).toDigitTable index.2
  else
    0

@[simp]
theorem chainValueTableOfList_listOfChainValueTable
    (table : ChainValueIndex → Digest) :
    chainValueTableOfList (listOfChainValueTable table) = table := by
  funext index
  unfold chainValueTableOfList
  split
  · rename_i hlength
    simp only [listOfChainValueTable, List.getElem_map,
      FullChainTrajectory.toDigitTable_ofDigitTable]
    have hget : allEpochs[(epochPosition index.1).val] = index.1 := by
      exact allEpochs_get_epochPosition index.1
    rw [hget]
  · rename_i hlength
    exact (hlength (by simp [listOfChainValueTable])).elim

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

theorem chainValueTableOfList_injective_of_length
    {left right : List FullChainTrajectory}
    (hleft : left.length = lifetime) (hright : right.length = lifetime)
    (heq : chainValueTableOfList left = chainValueTableOfList right) :
    left = right := by
  rw [← listOfChainValueTable_chainValueTableOfList left hleft,
    ← listOfChainValueTable_chainValueTableOfList right hright, heq]

noncomputable def Concrete.sampledAllEpochChainValueTable
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp ((ChainValueIndex → Digest) × QueryCache HashSpec) :=
  (fun result => (chainValueTableOfList result.1, result.2)) <$>
    Concrete.sampledAllEpochChainTrajectories parameter chain

set_option maxRecDepth 10000 in
theorem Concrete.sampledAllEpochChainValueTable_probability
    (parameter : PublicParameter) (chain : ChainIndex)
    (target : ChainValueIndex → Digest) :
    Pr[fun result : (ChainValueIndex → Digest) × QueryCache HashSpec =>
        result.1 = target |
      Concrete.sampledAllEpochChainValueTable parameter chain] =
      ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ chainLength) ^ lifetime := by
  unfold Concrete.sampledAllEpochChainValueTable
  rw [probEvent_map]
  let targetList := listOfChainValueTable target
  have htargetLength : targetList.length = lifetime := by
    simp [targetList]
  have hevent :
      Pr[(fun result : (ChainValueIndex → Digest) × QueryCache HashSpec =>
          result.1 = target) ∘
          (fun result : List FullChainTrajectory × QueryCache HashSpec =>
            (chainValueTableOfList result.1, result.2)) |
        Concrete.sampledAllEpochChainTrajectories parameter chain] =
      Pr[fun result : List FullChainTrajectory × QueryCache HashSpec =>
          result.1 = targetList |
        Concrete.sampledAllEpochChainTrajectories parameter chain] := by
    apply probEvent_congr' (fun result hresult => ?_) rfl
    change (chainValueTableOfList result.1 = target ↔ result.1 = targetList)
    have hresultLength :=
      Concrete.sampledChainTrajectoriesFromCache_support_length parameter chain 0
        (chainLength - 1) allEpochs ∅ result hresult
    rw [allEpochs_length] at hresultLength
    constructor
    · intro heq
      apply chainValueTableOfList_injective_of_length hresultLength htargetLength
      rw [heq]
      exact chainValueTableOfList_listOfChainValueTable target |>.symm
    · intro heq
      rw [heq]
      exact chainValueTableOfList_listOfChainValueTable target
  rw [hevent]
  simpa only [fullChainTrajectory_length_eq] using
    Concrete.sampledAllEpochChainTrajectories_probability parameter chain targetList
      htargetLength

noncomputable def Concrete.sampledAllEpochChainValueTableOnly
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (ChainValueIndex → Digest) :=
  Prod.fst <$> Concrete.sampledAllEpochChainValueTable parameter chain

theorem Concrete.sampledAllEpochChainValueTableOnly_probability
    (parameter : PublicParameter) (chain : ChainIndex)
    (target : ChainValueIndex → Digest) :
    Pr[= target | Concrete.sampledAllEpochChainValueTableOnly parameter chain] =
      ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ chainLength) ^ lifetime := by
  unfold Concrete.sampledAllEpochChainValueTableOnly
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  exact Concrete.sampledAllEpochChainValueTable_probability parameter chain target

theorem card_chainValueIndex :
    Fintype.card ChainValueIndex = lifetime * chainLength := by
  simp [ChainValueIndex, Epoch, Digit]

theorem Concrete.evalDist_sampledAllEpochChainValueTableOnly_eq_uniform
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[Concrete.sampledAllEpochChainValueTableOnly parameter chain] =
      𝒟[$ᵗ (ChainValueIndex → Digest)] := by
  apply SPMF.ext
  intro target
  change Pr[= target | Concrete.sampledAllEpochChainValueTableOnly parameter chain] =
    Pr[= target | $ᵗ (ChainValueIndex → Digest)]
  rw [Concrete.sampledAllEpochChainValueTableOnly_probability]
  rw [probOutput_uniformSample, Fintype.card_fun, HiddenValue.card_digest,
    card_chainValueIndex]
  simp only [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow, ← pow_mul]
  congr 1

end XmssSecurity
