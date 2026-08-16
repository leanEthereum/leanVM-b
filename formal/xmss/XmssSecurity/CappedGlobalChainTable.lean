import XmssSecurity.CappedChain.ChainRevealFiltering

open OracleSpec

namespace XmssSecurity.CappedChain

abbrev GlobalChainValueIndex := ChainIndex × ChainValueIndex

noncomputable def globalKeygenChainValueTable
    (keygenCache : QueryCache HashSpec) (secretKey : SecretKey) :
    GlobalChainValueIndex → Digest := fun index =>
  keygenChainValueTable keygenCache secretKey index.1 index.2

noncomputable def globalChainInputProbe?
    (parameter : PublicParameter) (input : HashInput) :
    Option (GlobalChainValueIndex × Digest) :=
  if h : ∃ data : Epoch × ChainIndex × ChainStep × Digest,
      input = Concrete.CacheView.chainInput parameter data.1 data.2.1
        data.2.2.1 data.2.2.2 then
    let data := h.choose
    some ((data.2.1, data.1, chainStepDigit data.2.2.1), data.2.2.2)
  else
    none

@[simp]
theorem globalChainInputProbe?_chainInput
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.chainInput parameter epoch chain step value) =
      some ((chain, epoch, chainStepDigit step), value) := by
  unfold globalChainInputProbe?
  split
  · rename_i h
    let chosen := h.choose
    have hchosen := h.choose_spec
    have heq := (Concrete.CacheView.chainInput_eq_iff parameter
      chosen.1 epoch chosen.2.1 chain chosen.2.2.1 step
        chosen.2.2.2 value).mp hchosen.symm
    obtain ⟨hepoch, hchain, hstep, hvalue⟩ := heq
    simp only
    rw [hepoch, hchain, hstep, hvalue]
  · rename_i h
    exact (h ⟨(epoch, chain, step, value), rfl⟩).elim

noncomputable def AttackerActionTrace.globalChainInputProbes
    (parameter : PublicParameter) (trace : AttackerActionTrace) :
    List (GlobalChainValueIndex × Digest) :=
  trace.hashInputs.filterMap (globalChainInputProbe? parameter)

theorem AttackerActionTrace.globalChainInputProbes_length_le
    (parameter : PublicParameter) (trace : AttackerActionTrace) :
    (trace.globalChainInputProbes parameter).length ≤ trace.hashInputs.length := by
  exact List.length_filterMap_le _ _

noncomputable def globalReturnedChainValueReveals
  (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) :
    List (GlobalChainValueIndex × Digest) :=
  (List.ofFn fun chain : ChainIndex =>
    (returnedChainValueIndexList finalCache secretKey log chain).map
      fun index =>
        ((chain, index), keygenChainValueTable keygenCache secretKey chain index)).flatten

@[simp]
theorem mem_globalReturnedChainValueReveals_iff
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (index : GlobalChainValueIndex)
    (value : Digest) :
    (index, value) ∈
        globalReturnedChainValueReveals keygenCache finalCache secretKey log ↔
      (index.2, value) ∈ returnedChainValueReveals keygenCache finalCache
        secretKey log index.1 := by
  classical
  cases index with
  | mk indexChain indexCoordinate =>
      constructor
      · intro hmem
        unfold globalReturnedChainValueReveals at hmem
        rw [List.mem_flatten] at hmem
        obtain ⟨reveals, hreveals, hreveal⟩ := hmem
        rw [List.mem_ofFn] at hreveals
        obtain ⟨chain, rfl⟩ := hreveals
        rw [List.mem_map] at hreveal
        obtain ⟨coordinate, hcoordinate, heq⟩ := hreveal
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨hchain, hcoordinateEq⟩, hvalue⟩ := heq
        subst chain
        subst coordinate
        subst value
        unfold returnedChainValueReveals
        rw [List.mem_map]
        exact ⟨indexCoordinate, hcoordinate, rfl⟩
      · intro hmem
        unfold returnedChainValueReveals at hmem
        rw [List.mem_map] at hmem
        obtain ⟨coordinate, hcoordinate, heq⟩ := hmem
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hcoordinateEq, hvalue⟩ := heq
        subst coordinate
        subst value
        unfold globalReturnedChainValueReveals
        rw [List.mem_flatten]
        refine ⟨_, List.mem_ofFn.mpr ⟨indexChain, rfl⟩, ?_⟩
        rw [List.mem_map]
        exact ⟨indexCoordinate, hcoordinate, rfl⟩

theorem globalKeygenChainValueTable_agrees_with_reveals
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (reveal : GlobalChainValueIndex × Digest)
    (hreveal : reveal ∈
      globalReturnedChainValueReveals keygenCache finalCache secretKey log) :
    globalKeygenChainValueTable keygenCache secretKey reveal.1 = reveal.2 := by
  unfold globalReturnedChainValueReveals at hreveal
  rw [List.mem_flatten] at hreveal
  obtain ⟨reveals, hreveals, hreveal⟩ := hreveal
  rw [List.mem_ofFn] at hreveals
  obtain ⟨chain, rfl⟩ := hreveals
  rw [List.mem_map] at hreveal
  obtain ⟨index, _hindex, rfl⟩ := hreveal
  rfl

@[simp]
theorem mem_globalReturnedChainValueReveals_fst_iff
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (index : GlobalChainValueIndex) :
    index ∈ (globalReturnedChainValueReveals keygenCache finalCache secretKey log).map
        Prod.fst ↔
      index.2 ∈ (returnedChainValueReveals keygenCache finalCache secretKey log
        index.1).map Prod.fst := by
  constructor
  · intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨reveal, hreveal, heq⟩ := hmem
    subst index
    have hpair := mem_globalReturnedChainValueReveals_iff keygenCache finalCache
      secretKey log reveal.1 reveal.2 |>.mp hreveal
    rw [List.mem_map]
    refine ⟨(reveal.1.2, reveal.2), ?_, ?_⟩
    · exact hpair
    · rfl
  · intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨reveal, hreveal, heq⟩ := hmem
    rw [List.mem_map]
    refine ⟨((index.1, reveal.1), reveal.2), ?_, ?_⟩
    · rw [mem_globalReturnedChainValueReveals_iff]
      simpa only using hreveal
    · exact Prod.ext rfl heq

theorem install_globalReturnedChainValueReveals_eq_keygenTable
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) :
    IndexedHiddenValue.installReveals
        (globalKeygenChainValueTable keygenCache secretKey)
        (globalReturnedChainValueReveals keygenCache finalCache secretKey log) =
      globalKeygenChainValueTable keygenCache secretKey := by
  apply IndexedHiddenValue.installReveals_eq_self_of_values
  intro reveal hreveal
  exact globalKeygenChainValueTable_agrees_with_reveals keygenCache finalCache
    secretKey log reveal hreveal

end XmssSecurity.CappedChain
