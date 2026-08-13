import XmssSecurity.CausalKeygenCacheCoupling
import XmssSecurity.CausalStrategyCoupling
import XmssSecurity.KeygenCache

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

def ProgrammedFixedChainKeygenView.keyResult
    (view : ProgrammedFixedChainKeygenView) :
    (PublicKey × SecretKey) × QueryCache HashSpec :=
  ((view.publicKey, view.secretKey), view.cache)

theorem actualFixedChainKeygen_support_keyResult
    (chain : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (actualFixedChainKeygen chain)) :
    view.keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅) := by
  unfold actualFixedChainKeygen at hview
  rw [mem_support_bind_iff] at hview
  obtain ⟨keyResult, hkeyResult, hpure⟩ := hview
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst view
  exact hkeyResult

theorem programmedWarmedFixedChainKeygen_support_keyResult
    (chain : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (programmedWarmedFixedChainKeygen chain)) :
    view.keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅) := by
  apply actualFixedChainKeygen_support_keyResult chain view
  exact (mem_support_iff_of_evalDist_eq
    (evalDist_actualFixedChainKeygen_eq_programmedWarmed chain) view).mpr hview

theorem ProgrammedFixedChainKeygenView.parameter_eq
    (view : ProgrammedFixedChainKeygenView)
    (hkeyResult : view.keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅)) :
    view.publicKey.parameter = view.secretKey.parameter := by
  obtain ⟨parameter, secret, root, hkey, _hroot⟩ :=
    Concrete.keygen_support_rootTree view.keyResult hkeyResult
  exact congrArg (fun result => result.1.parameter = result.2.parameter) hkey ▸ rfl

theorem ProgrammedFixedChainKeygenView.chainTableMatches
    (chain : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hkeyResult : view.keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (htable : keygenChainValueTable view.cache view.secretKey chain =
      view.table) :
    ChainTableSeedsMatch view.secretKey chain view.table ∧
      ChainTableEdgesMatch view.cache view.secretKey.parameter chain
        view.table := by
  constructor
  · rw [← htable]
    exact keygenChainValueTable_seedsMatch view.cache view.secretKey chain
  · rw [← htable]
    exact Concrete.keygenChainValueTable_edgesMatch
      view.keyResult hkeyResult chain

theorem relTriple_signingChainWalk_run
    (parameter : PublicParameter) (selected candidate : ChainIndex)
    (epoch : Epoch) (steps : Nat) (hsteps : steps < chainLength)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftTable rightTable : ChainValueIndex → Digest)
    (initialLeft initialRight left right : QueryCache HashSpec)
    (houtside : secretOutsideChain selected leftSecret =
      secretOutsideChain selected rightSecret)
    (hleftSeeds : ChainTableSeedsMatch
      ⟨parameter, leftSecret⟩ selected leftTable)
    (hleftEdges : ChainTableEdgesMatch initialLeft parameter selected leftTable)
    (hrightSeeds : ChainTableSeedsMatch
      ⟨parameter, rightSecret⟩ selected rightTable)
    (hrightEdges : ChainTableEdgesMatch initialRight parameter selected rightTable)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) left right)
    (hleftLe : initialLeft ≤ left) (hrightLe : initialRight ≤ right) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch candidate 0 steps
          (leftSecret epoch candidate))).run left)
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch candidate 0 steps
          (rightSecret epoch candidate))).run right)
      (fun leftResult rightResult =>
        (candidate = selected →
          leftResult.1 = leftTable (epoch, ⟨steps, hsteps⟩)) ∧
        (candidate ≠ selected → leftResult.1 = rightResult.1) ∧
        HashCachesAgreeOn (OutsideChainHashInput parameter selected)
          leftResult.2 rightResult.2 ∧
        initialLeft ≤ leftResult.2 ∧ initialRight ≤ rightResult.2) := by
  by_cases hcandidate : candidate = selected
  · subst candidate
    rw [simulate_chainWalk_run_eq_pure_of_table_matches left
        ⟨parameter, leftSecret⟩ selected leftTable hleftSeeds
          (hleftEdges.mono hleftLe) epoch steps hsteps,
      simulate_chainWalk_run_eq_pure_of_table_matches right
        ⟨parameter, rightSecret⟩ selected rightTable hrightSeeds
          (hrightEdges.mono hrightLe) epoch steps hsteps]
    exact relTriple_pure_pure
      ⟨fun _ => rfl, fun hne => (hne rfl).elim, hagrees,
        hleftLe, hrightLe⟩
  · have hsecret : leftSecret epoch candidate =
        rightSecret epoch candidate :=
      secret_eq_of_outsideChain_eq selected leftSecret rightSecret
        houtside epoch candidate hcandidate
    rw [← hsecret]
    apply relTriple_post_mono
      (relTriple_chainWalk_run_outside parameter selected candidate
        hcandidate epoch 0 steps (leftSecret epoch candidate)
          left right hagrees)
    intro leftResult rightResult hresult
    exact ⟨fun heq => (hcandidate heq).elim, fun _ => hresult.1,
      hresult.2.1, hleftLe.trans hresult.2.2.1,
      hrightLe.trans hresult.2.2.2⟩

theorem relTriple_signedChainValues_run
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (encoding : Encoding)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftTable rightTable : ChainValueIndex → Digest)
    (initialLeft initialRight left right : QueryCache HashSpec)
    (houtside : secretOutsideChain selected leftSecret =
      secretOutsideChain selected rightSecret)
    (hleftSeeds : ChainTableSeedsMatch
      ⟨parameter, leftSecret⟩ selected leftTable)
    (hleftEdges : ChainTableEdgesMatch initialLeft parameter selected leftTable)
    (hrightSeeds : ChainTableSeedsMatch
      ⟨parameter, rightSecret⟩ selected rightTable)
    (hrightEdges : ChainTableEdgesMatch initialRight parameter selected rightTable)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) left right)
    (hleftLe : initialLeft ≤ left) (hrightLe : initialRight ≤ right) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.signedChainValues ⟨parameter, leftSecret⟩ epoch encoding)).run
          left)
      ((simulateQ randomOracle
        (Concrete.signedChainValues ⟨parameter, rightSecret⟩ epoch encoding)).run
          right)
      (fun leftResult rightResult =>
        leftResult.1 selected = leftTable (epoch, encoding selected) ∧
        (∀ candidate, candidate ≠ selected →
          leftResult.1 candidate = rightResult.1 candidate) ∧
        HashCachesAgreeOn (OutsideChainHashInput parameter selected)
          leftResult.2 rightResult.2 ∧
        initialLeft ≤ leftResult.2 ∧ initialRight ≤ rightResult.2) := by
  let StateRelation := fun (currentLeft currentRight : QueryCache HashSpec) =>
    HashCachesAgreeOn (OutsideChainHashInput parameter selected)
        currentLeft currentRight ∧
      initialLeft ≤ currentLeft ∧ initialRight ≤ currentRight
  let ValueRelation := fun (candidate : ChainIndex)
      (leftValue rightValue : Digest) =>
    (candidate = selected →
      leftValue = leftTable (epoch, encoding candidate)) ∧
    (candidate ≠ selected → leftValue = rightValue)
  have hstep : ∀ candidate currentLeft currentRight,
      StateRelation currentLeft currentRight →
      RelTriple
        ((simulateQ randomOracle
          (Concrete.chainWalk parameter epoch candidate 0
            (encoding candidate).val (leftSecret epoch candidate))).run
              currentLeft)
        ((simulateQ randomOracle
          (Concrete.chainWalk parameter epoch candidate 0
            (encoding candidate).val (rightSecret epoch candidate))).run
              currentRight)
        (fun leftResult rightResult =>
          ValueRelation candidate leftResult.1 rightResult.1 ∧
            StateRelation leftResult.2 rightResult.2) := by
    intro candidate currentLeft currentRight hstate
    apply relTriple_post_mono
      (relTriple_signingChainWalk_run parameter selected candidate epoch
        (encoding candidate).val (encoding candidate).isLt
        leftSecret rightSecret leftTable rightTable initialLeft initialRight
        currentLeft currentRight houtside hleftSeeds hleftEdges
        hrightSeeds hrightEdges hstate.1 hstate.2.1 hstate.2.2)
    intro leftResult rightResult hresult
    exact ⟨⟨hresult.1, hresult.2.1⟩,
      hresult.2.2.1, hresult.2.2.2.1, hresult.2.2.2.2⟩
  have hsequence := relTriple_simulate_sequenceFin_run
    (fun candidate => Concrete.chainWalk parameter epoch candidate 0
      (encoding candidate).val (leftSecret epoch candidate))
    (fun candidate => Concrete.chainWalk parameter epoch candidate 0
      (encoding candidate).val (rightSecret epoch candidate))
    StateRelation ValueRelation hstep left right
      ⟨hagrees, hleftLe, hrightLe⟩
  apply relTriple_post_mono hsequence
  intro leftResult rightResult hresult
  refine ⟨(hresult.1 selected).1 rfl, ?_, hresult.2.1,
    hresult.2.2.1, hresult.2.2.2⟩
  intro candidate hne
  exact (hresult.1 candidate).2 hne

theorem relTriple_signedChainValues_run_keys
    (selected : ChainIndex) (epoch : Epoch) (encoding : Encoding)
    (leftSecret rightSecret : SecretKey)
    (leftTable rightTable : ChainValueIndex → Digest)
    (initialLeft initialRight left right : QueryCache HashSpec)
    (hparameter : leftSecret.parameter = rightSecret.parameter)
    (houtside : secretOutsideChain selected leftSecret.chainStart =
      secretOutsideChain selected rightSecret.chainStart)
    (hleftSeeds : ChainTableSeedsMatch leftSecret selected leftTable)
    (hleftEdges : ChainTableEdgesMatch initialLeft
      leftSecret.parameter selected leftTable)
    (hrightSeeds : ChainTableSeedsMatch rightSecret selected rightTable)
    (hrightEdges : ChainTableEdgesMatch initialRight
      rightSecret.parameter selected rightTable)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput leftSecret.parameter selected) left right)
    (hleftLe : initialLeft ≤ left) (hrightLe : initialRight ≤ right) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.signedChainValues leftSecret epoch encoding)).run left)
      ((simulateQ randomOracle
        (Concrete.signedChainValues rightSecret epoch encoding)).run right)
      (fun leftResult rightResult =>
        leftResult.1 selected = leftTable (epoch, encoding selected) ∧
        (∀ candidate, candidate ≠ selected →
          leftResult.1 candidate = rightResult.1 candidate) ∧
        HashCachesAgreeOn
          (OutsideChainHashInput leftSecret.parameter selected)
          leftResult.2 rightResult.2 ∧
        initialLeft ≤ leftResult.2 ∧ initialRight ≤ rightResult.2) := by
  obtain ⟨leftParameter, leftChainStart⟩ := leftSecret
  obtain ⟨rightParameter, rightChainStart⟩ := rightSecret
  dsimp only at hparameter
  subst rightParameter
  exact relTriple_signedChainValues_run leftParameter selected epoch encoding
    leftChainStart rightChainStart leftTable rightTable initialLeft initialRight
    left right houtside hleftSeeds hleftEdges hrightSeeds hrightEdges hagrees
    hleftLe hrightLe

theorem relTriple_keygenViews_signedChainValues_run
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (epoch : Epoch) (encoding : Encoding)
    (leftCache rightCache : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput left.secretKey.parameter selected)
        leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.signedChainValues left.secretKey epoch encoding)).run
          leftCache)
      ((simulateQ randomOracle
        (Concrete.signedChainValues right.1.secretKey epoch encoding)).run
          rightCache)
      (fun leftResult rightResult =>
        leftResult.1 selected = right.2 (epoch, encoding selected) ∧
        (∀ candidate, candidate ≠ selected →
          leftResult.1 candidate = rightResult.1 candidate) ∧
        HashCachesAgreeOn
          (OutsideChainHashInput left.secretKey.parameter selected)
          leftResult.2 rightResult.2 ∧
        left.cache ≤ leftResult.2 ∧ right.1.cache ≤ rightResult.2) := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult
    selected right.1 hrightSupport
  have hleftParameter := left.parameter_eq hleftKey
  have hrightParameter := right.1.parameter_eq hrightKey
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter := hleftParameter.symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.2.1
      _ = right.1.secretKey.parameter := hrightParameter
  have hleftTable := programmedWarmedFixedChainKeygen_support_table
    selected left hleftSupport
  have hrightTable := actualFixedChainKeygen_support_table
    selected right.1 hrightSupport
  have hleftMatches := left.chainTableMatches selected hleftKey hleftTable
  have hrightMatches := right.1.chainTableMatches
    selected hrightKey hrightTable
  have houtside := hrel.1.2.2.1
  apply relTriple_post_mono
    (relTriple_signedChainValues_run_keys selected epoch encoding
      left.secretKey right.1.secretKey
      left.table right.1.table left.cache right.1.cache leftCache rightCache
      hparameter houtside hleftMatches.1 hleftMatches.2
      hrightMatches.1 hrightMatches.2 hagrees hleftLe hrightLe)
  intro leftResult rightResult hresult
  exact ⟨hresult.1.trans (congrFun hrel.1.1 (epoch, encoding selected)),
    hresult.2.1,
    hresult.2.2.1, hresult.2.2.2.1, hresult.2.2.2.2⟩

theorem Concrete.CacheReplay.chainStep_eq_of_outsideChainCachesAgree
    (parameter : PublicParameter) (selected candidate : ChainIndex)
    (hne : candidate ≠ selected)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) left right)
    (epoch : Epoch) :
    Concrete.CacheView.chainStep left parameter epoch candidate =
      Concrete.CacheView.chainStep right parameter epoch candidate := by
  funext position value
  unfold Concrete.CacheView.chainStep
  split
  · rename_i hposition
    unfold Concrete.CacheView.digestAt
    rw [hagrees _ ⟨epoch, candidate, ⟨position, hposition⟩, hne,
      by simp [Concrete.CacheView.chainInput]⟩]
  · rfl

theorem Concrete.CacheReplay.signedChainValues_other_eq
    (parameter : PublicParameter) (selected candidate : ChainIndex)
    (hne : candidate ≠ selected)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (houtside : secretOutsideChain selected leftSecret =
      secretOutsideChain selected rightSecret)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected) left right)
    (epoch : Epoch) (encoding : Encoding) :
    Concrete.CacheReplay.signedChainValues left
        ⟨parameter, leftSecret⟩ epoch encoding candidate =
    Concrete.CacheReplay.signedChainValues right
        ⟨parameter, rightSecret⟩ epoch encoding candidate := by
  unfold Concrete.CacheReplay.signedChainValues
  dsimp only [SecretKey.parameter, SecretKey.chainStart]
  rw [secret_eq_of_outsideChain_eq selected leftSecret rightSecret
      houtside epoch candidate hne,
    Concrete.CacheReplay.chainStep_eq_of_outsideChainCachesAgree
      parameter selected candidate hne left right hagrees epoch]

theorem Concrete.CacheReplay.signedChainValues_other_eq_keys
    (selected candidate : ChainIndex) (hne : candidate ≠ selected)
    (leftSecret rightSecret : SecretKey)
    (hparameter : leftSecret.parameter = rightSecret.parameter)
    (houtside : secretOutsideChain selected leftSecret.chainStart =
      secretOutsideChain selected rightSecret.chainStart)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (OutsideChainHashInput leftSecret.parameter selected) left right)
    (epoch : Epoch) (encoding : Encoding) :
    Concrete.CacheReplay.signedChainValues left leftSecret epoch encoding candidate =
      Concrete.CacheReplay.signedChainValues right rightSecret
        epoch encoding candidate := by
  obtain ⟨leftParameter, leftChainStart⟩ := leftSecret
  obtain ⟨rightParameter, rightChainStart⟩ := rightSecret
  dsimp only at hparameter
  subst rightParameter
  exact Concrete.CacheReplay.signedChainValues_other_eq leftParameter
    selected candidate hne leftChainStart rightChainStart houtside
      left right hagrees epoch encoding

theorem keygenViews_signWithEncoding_eq_replaced
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenCacheRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (epoch : Epoch) (randomness : Randomness) (encoding : Encoding) :
    Concrete.CacheReplay.signWithEncoding left.cache left.secretKey
        epoch randomness encoding =
      replaceSignatureChainValue
        (Concrete.CacheReplay.signWithEncoding right.1.cache
          right.1.secretKey epoch randomness encoding)
        selected (right.2 (epoch, encoding selected)) := by
  have hleftKey := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hrightKey := actualFixedChainKeygen_support_keyResult
    selected right.1 hrightSupport
  have hleftParameter := left.parameter_eq hleftKey
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        hleftParameter.symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.2.1
      _ = right.1.secretKey.parameter := right.1.parameter_eq hrightKey
  have hcacheAgreement : HashCachesAgreeOn
      (OutsideChainHashInput left.secretKey.parameter selected)
      left.cache right.1.cache := by
    rw [← hleftParameter]
    exact hrel.2
  have hselected :
      (Concrete.CacheReplay.signWithEncoding left.cache left.secretKey
        epoch randomness encoding).chainValue selected =
        right.2 (epoch, encoding selected) := by
    have hvalue :=
      Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
        left.keyResult hleftKey left.cache le_rfl epoch randomness encoding selected
    change (Concrete.CacheReplay.signWithEncoding left.cache left.secretKey
        epoch randomness encoding).chainValue selected =
      keygenChainValueTable left.cache left.secretKey selected
        (epoch, encoding selected) at hvalue
    calc
      _ = keygenChainValueTable left.cache left.secretKey selected
          (epoch, encoding selected) := hvalue
      _ = left.table (epoch, encoding selected) :=
        congrFun (programmedWarmedFixedChainKeygen_support_table
          selected left hleftSupport) (epoch, encoding selected)
      _ = right.2 (epoch, encoding selected) :=
        congrFun hrel.1.1 (epoch, encoding selected)
  unfold Concrete.CacheReplay.signWithEncoding replaceSignatureChainValue
  congr 1
  · funext candidate
    by_cases heq : candidate = selected
    · subst candidate
      rw [Function.update_self]
      exact hselected
    · rw [Function.update_of_ne heq]
      exact Concrete.CacheReplay.signedChainValues_other_eq_keys
        selected candidate heq left.secretKey right.1.secretKey hparameter
        hrel.1.2.2.1 left.cache right.1.cache hcacheAgreement epoch encoding
  · exact hrel.1.2.2.2 epoch

end XmssSecurity
