import SphincsSecurity.Proof.FtsProbeLift

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec

def NonOrdinaryInput (parameter : PublicParameter) (table : Coordinate → Digest) :
    HashInput → Prop :=
  fun input => ¬IsOrdinaryInput parameter table input

noncomputable instance (parameter : PublicParameter) (table : Coordinate → Digest) :
    DecidablePred (NonOrdinaryInput parameter table) :=
  fun _input => Classical.propDecidable _

def OrdinaryOnly (parameter : PublicParameter) (table : Coordinate → Digest)
    (computation : OracleComp HashSpec alpha) : Prop :=
  computation.IsQueryBoundP (NonOrdinaryInput parameter table) 0

theorem OrdinaryOnly.pure (parameter : PublicParameter) (table : Coordinate → Digest)
    (value : alpha) :
    OrdinaryOnly parameter table (pure value) := by
  simp [OrdinaryOnly]

theorem OrdinaryOnly.bind
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {left : OracleComp HashSpec alpha} {next : alpha → OracleComp HashSpec beta}
    (hleft : OrdinaryOnly parameter table left)
    (hnext : ∀ value, OrdinaryOnly parameter table (next value)) :
    OrdinaryOnly parameter table (left >>= next) := by
  exact isQueryBoundP_bind (n := 0) (m := 0) hleft fun value _ => hnext value

theorem coupled_splitHashQuery_ordinary
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (input : HashInput)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hordinary : IsOrdinaryInput parameter table input) :
    Coupled parameter table state fuel (splitHashQuery (.ordinary input))
      (randomOracle input) := by
  intro cache
  exact runDetailed_splitHashQuery_ordinary parameter table state fuel cache input hclean
    hordinary

theorem coupled_simulateQ_ordinaryHashImpl
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (computation : OracleComp HashSpec alpha)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hordinaryOnly : OrdinaryOnly parameter table computation) :
    Coupled parameter table state fuel (simulateQ ordinaryHashImpl computation)
      (simulateQ (randomOracle : QueryImpl HashSpec _) computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact Coupled.pure parameter table state fuel hclean value
  | query_bind input next ih =>
      rw [OrdinaryOnly, isQueryBoundP_query_bind_iff] at hordinaryOnly
      have hordinary : IsOrdinaryInput parameter table input := by
        by_contra hnot
        have hzero := hordinaryOnly.1
        simp [NonOrdinaryInput, hnot] at hzero
      rw [simulateQ_query_bind, simulateQ_query_bind]
      exact Coupled.bind hclean (splitHashQuery_stateFree (.ordinary input))
        (coupled_splitHashQuery_ordinary parameter table state fuel input hclean hordinary)
        fun output => ih output (by
          simpa [OrdinaryOnly, NonOrdinaryInput, hordinary] using hordinaryOnly.2 output)

theorem isOrdinaryInput_of_domain_ne_ftsLeaf
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (domain : HashDomain) (payload : HashInput)
    (hinRange : domain.InRange)
    (hne : ∀ index tree leafIdx, domain ≠ .ftsLeaf index tree leafIdx) :
    IsOrdinaryInput parameter table (tweakableHashInput parameter domain payload) := by
  apply isOrdinaryInput_of_decode_none
  rw [decodeProbe?_eq_none_iff]
  intro probe heq
  have hdomain := (tweakableHashInput_injective parameter (by trivial) hinRange heq).1
  exact hne probe.index probe.tree probe.leafIdx hdomain.symm

theorem ordinaryOnly_tweakableHash
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (domain : HashDomain) (payload : HashInput)
    (hinRange : domain.InRange)
    (hne : ∀ index tree leafIdx, domain ≠ .ftsLeaf index tree leafIdx) :
    OrdinaryOnly parameter table (tweakableHash parameter domain payload) := by
  unfold OrdinaryOnly tweakableHash oracleHash
  change ((liftM (HashSpec.query (tweakableHashInput parameter domain payload)) :
    OracleComp HashSpec HashOutput) >>= fun output => pure (truncateHash output)).IsQueryBoundP
      (NonOrdinaryInput parameter table) 0
  rw [isQueryBoundP_query_bind_iff]
  constructor
  · have hordinary := isOrdinaryInput_of_domain_ne_ftsLeaf parameter table domain payload
      hinRange hne
    simp [NonOrdinaryInput, hordinary]
  · intro output
    trivial

theorem ordinaryOnly_sequenceFin {n : Nat}
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (computation : Fin n → OracleComp HashSpec alpha)
    (hcomputation : ∀ position, OrdinaryOnly parameter table (computation position)) :
    OrdinaryOnly parameter table (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact OrdinaryOnly.pure parameter table Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun position => computation position.succ)
          (fun position => hcomputation position.succ)).bind fun tail =>
            OrdinaryOnly.pure parameter table
              (Fin.cases head tail : Fin (n + 1) → alpha)

theorem ordinaryOnly_chainWalk
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) :
    OrdinaryOnly parameter table
      (chainWalk parameter lay tree leafIdx chainIdx start steps value) := by
  induction steps with
  | zero => exact OrdinaryOnly.pure parameter table value
  | succ steps ih =>
      rw [chainWalk]
      exact ih.bind fun previous => by
        split
        · apply ordinaryOnly_tweakableHash parameter table
          · trivial
          · intros
            simp
        · exact OrdinaryOnly.pure parameter table 0

theorem ordinaryOnly_encode
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) :
    OrdinaryOnly parameter table
      (encode parameter lay tree leafIdx message counter) := by
  unfold encode
  exact (ordinaryOnly_tweakableHash parameter table (.encoding lay tree leafIdx)
    (digestBytes message ++ counterBytes counter) (by trivial) (by intros; simp)).bind
      fun digest => OrdinaryOnly.pure parameter table (TargetSum.decodeDigest digest)

theorem ordinaryOnly_otsSignFrom
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) (attempts counter : Nat) :
    OrdinaryOnly parameter table
      (otsSignFrom parameter lay tree leafIdx secret message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact OrdinaryOnly.pure parameter table none
  | succ attempts ih =>
      rw [otsSignFrom]
      exact (ordinaryOnly_encode parameter table lay tree leafIdx message
        (BitVec.ofNat counterBits counter)).bind fun encoded => by
          cases encoded with
          | none => exact ih (counter + 1)
          | some encoding =>
              exact (ordinaryOnly_sequenceFin parameter table
                (fun chainIdx => chainWalk parameter lay tree leafIdx chainIdx 0
                  (encoding chainIdx).val (secret chainIdx))
                (fun chainIdx => ordinaryOnly_chainWalk parameter table lay tree leafIdx
                  chainIdx 0 (encoding chainIdx).val (secret chainIdx))).bind fun values =>
                    OrdinaryOnly.pure parameter table
                      (some (BitVec.ofNat counterBits counter, values))

theorem ordinaryOnly_otsSign
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    OrdinaryOnly parameter table
      (otsSign parameter lay tree leafIdx secret message) :=
  ordinaryOnly_otsSignFrom parameter table lay tree leafIdx secret message
    encodingAttemptLimit 0

theorem ordinaryOnly_oneTimePublicKey
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) :
    OrdinaryOnly parameter table
      (oneTimePublicKey parameter lay tree leafIdx secret) := by
  unfold oneTimePublicKey
  exact ordinaryOnly_sequenceFin parameter table _ fun chainIdx =>
    ordinaryOnly_chainWalk parameter table lay tree leafIdx chainIdx 0
      (chainLength - 1) (secret chainIdx)

theorem ordinaryOnly_leafHash
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    OrdinaryOnly parameter table (leafHash parameter lay tree leafIdx endpoints) :=
  ordinaryOnly_tweakableHash parameter table (.leaf lay tree leafIdx)
    (leafPayload endpoints) (by trivial) (by intros; simp)

theorem ordinaryOnly_treeNode
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight)
    (hrange : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight) :
    OrdinaryOnly parameter table (treeNode parameter lay tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_zero_eq]
      exact (ordinaryOnly_oneTimePublicKey parameter table lay tree (leafOfNat nodeIdx)
        (secret (leafOfNat nodeIdx))).bind fun endpoints =>
          ordinaryOnly_leafHash parameter table lay tree (leafOfNat nodeIdx) endpoints
  | succ level ih =>
      rw [treeNode_succ_eq]
      have hleftRange : 2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ maxLayerHeight := by
        rw [pow_succ] at hrange
        nlinarith [Nat.two_pow_pos level]
      have hrightRange : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤ 2 ^ maxLayerHeight := by
        rw [pow_succ] at hrange
        nlinarith [Nat.two_pow_pos level]
      have hlevelSmall : level + 1 < 2 ^ 32 := by
        norm_num [maxLayerHeight] at hlevel ⊢
        omega
      have hnodeSmall : nodeIdx < 2 ^ 32 := by
        norm_num [maxLayerHeight] at hrange ⊢
        nlinarith [Nat.two_pow_pos (level + 1)]
      exact (ih (2 * nodeIdx) (by omega) hleftRange).bind fun left =>
        (ih (2 * nodeIdx + 1) (by omega) hrightRange).bind fun right =>
          ordinaryOnly_tweakableHash parameter table (.node lay tree (level + 1) nodeIdx)
            (nodePayload left right) ⟨hlevelSmall, hnodeSmall⟩ (by intros; simp)

theorem ordinaryOnly_treeRoot
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) :
    OrdinaryOnly parameter table (treeRoot parameter lay tree secret) := by
  unfold treeRoot
  apply ordinaryOnly_treeNode parameter table lay tree secret (layerHeight lay) 0
  · exact layerHeight_le lay
  · simp only [zero_add, mul_one]
    exact pow_le_pow_right' (by omega) (layerHeight_le lay)

theorem sibling_node_bound (height leaf level : Nat)
    (hlevel : level < height) (hleaf : leaf < 2 ^ height) :
    2 ^ level * (Nat.xor (leaf / 2 ^ level) 1 + 1) ≤ 2 ^ height := by
  let bound := 2 ^ (height - level)
  have hquotient : leaf / 2 ^ level < bound := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos level)).2
    change leaf < 2 ^ (height - level) * 2 ^ level
    rw [← pow_add]
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hlevel)] using hleaf
  have hboundEven : ∃ half, bound = 2 * half := by
    refine ⟨2 ^ (height - level - 1), ?_⟩
    change 2 ^ (height - level) = _
    rw [show height - level = (height - level - 1) + 1 by omega, pow_succ]
    exact Nat.mul_comm _ _
  have hsibling : Nat.xor (leaf / 2 ^ level) 1 < bound := by
    obtain ⟨parent, hcase⟩ := index_sibling_cases (leaf / 2 ^ level)
    obtain ⟨half, hbound⟩ := hboundEven
    rcases hcase with hcase | hcase <;> omega
  calc
    2 ^ level * (Nat.xor (leaf / 2 ^ level) 1 + 1) ≤ 2 ^ level * bound :=
      Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hsibling)
    _ = 2 ^ height := by
      change 2 ^ level * 2 ^ (height - level) = _
      rw [← pow_add]
      congr 1
      omega

theorem ordinaryOnly_treePath
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leafIdx : LeafIndex)
    (hleaf : leafIdx.val < 2 ^ layerHeight lay) :
    OrdinaryOnly parameter table (treePath parameter lay tree secret leafIdx) := by
  unfold treePath
  apply ordinaryOnly_sequenceFin parameter table
  intro level
  split <;> rename_i hlevel
  · apply ordinaryOnly_treeNode parameter table lay tree secret level.val
      (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact (Nat.le_of_lt hlevel).trans (layerHeight_le lay)
    · exact (sibling_node_bound (layerHeight lay) leafIdx.val level.val hlevel hleaf).trans
        (pow_le_pow_right' (by omega) (layerHeight_le lay))
  · exact OrdinaryOnly.pure parameter table 0

theorem simulateQ_ordinaryHashImpl_stateFree
    (computation : OracleComp HashSpec alpha) :
    StateFree (simulateQ ordinaryHashImpl computation) := by
  intro cache
  apply (isQueryBoundP_false computation 0).simulateQ_run_StateT_of_step
  intro input workingCache
  exact splitHashQuery_stateFree (.ordinary input) workingCache

def secretKeyWithFtsTable (secretKey : SecretKey) (table : Coordinate → Digest) : SecretKey :=
  { secretKey with
    ftsSecret := fun index tree leafIdx => table (index, tree, leafIdx) }

@[simp] theorem secretKeyWithFtsTable_parameter
    (secretKey : SecretKey) (table : Coordinate → Digest) :
    (secretKeyWithFtsTable secretKey table).parameter = secretKey.parameter := rfl

@[simp] theorem secretKeyWithFtsTable_root
    (secretKey : SecretKey) (table : Coordinate → Digest) :
    (secretKeyWithFtsTable secretKey table).root = secretKey.root := rfl

@[simp] theorem secretKeyWithFtsTable_otsSecret
    (secretKey : SecretKey) (table : Coordinate → Digest) :
    (secretKeyWithFtsTable secretKey table).otsSecret = secretKey.otsSecret := rfl

@[simp] theorem secretKeyWithFtsTable_ftsSecret
    (secretKey : SecretKey) (table : Coordinate → Digest) (index : Index)
    (tree : FtsTree) (leafIdx : FtsLeaf) :
    (secretKeyWithFtsTable secretKey table).ftsSecret index tree leafIdx =
      table (index, tree, leafIdx) := rfl

theorem maskedLayerMessage_stateFree
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    StateFree (maskedLayerMessage secretKey index lay) := by
  unfold maskedLayerMessage
  split
  · exact simulateQ_ordinaryHashImpl_stateFree _
  · exact maskedFtsKey_stateFree secretKey.parameter index

theorem coupled_maskedLayerMessage
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (index : Index) (lay : Layer)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    Coupled secretKey.parameter table state fuel (maskedLayerMessage secretKey index lay)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (layerMessage (secretKeyWithFtsTable secretKey table) index lay)) := by
  unfold maskedLayerMessage layerMessage
  split
  · apply coupled_simulateQ_ordinaryHashImpl secretKey.parameter table state fuel _ hclean
    exact ordinaryOnly_treeRoot secretKey.parameter table _ _ _
  · simpa only [secretKeyWithFtsTable] using
      coupled_maskedFtsKey secretKey.parameter table state fuel index hclean

theorem maskedSignLayer_stateFree
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    StateFree (maskedSignLayer secretKey index lay) := by
  unfold maskedSignLayer
  exact (maskedLayerMessage_stateFree secretKey index lay).bind fun message =>
    (simulateQ_ordinaryHashImpl_stateFree
      (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
        message)).bind fun signed => by
      cases signed with
      | none => exact StateFree.pure none
      | some part =>
          exact (simulateQ_ordinaryHashImpl_stateFree
            (treePath secretKey.parameter lay (treeIndexAt index lay)
              (secretKey.otsSecret lay (treeIndexAt index lay))
              (leafIndexAt index lay))).bind fun path =>
                StateFree.pure (some (part.1, part.2, path))

theorem coupled_maskedSignLayer
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (index : Index) (lay : Layer)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    Coupled secretKey.parameter table state fuel (maskedSignLayer secretKey index lay)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signLayer (secretKeyWithFtsTable secretKey table) index lay)) := by
  unfold maskedSignLayer signLayer
  rw [simulateQ_bind]
  refine Coupled.bind hclean (maskedLayerMessage_stateFree secretKey index lay)
    (coupled_maskedLayerMessage secretKey table state fuel index lay hclean) ?_
  intro message
  rw [simulateQ_bind]
  refine Coupled.bind hclean
    (simulateQ_ordinaryHashImpl_stateFree
      (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay)) message))
    (coupled_simulateQ_ordinaryHashImpl secretKey.parameter table state fuel _ hclean
      (ordinaryOnly_otsSign secretKey.parameter table lay (treeIndexAt index lay)
        (leafIndexAt index lay)
        (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay)) message)) ?_
  intro signed
  cases signed with
  | none =>
      exact Coupled.pure secretKey.parameter table state fuel hclean none
  | some part =>
      rw [simulateQ_bind]
      refine Coupled.bind hclean
        (simulateQ_ordinaryHashImpl_stateFree
          (treePath secretKey.parameter lay (treeIndexAt index lay)
            (secretKey.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay)))
        (coupled_simulateQ_ordinaryHashImpl secretKey.parameter table state fuel _ hclean
          (ordinaryOnly_treePath secretKey.parameter table lay (treeIndexAt index lay)
            (secretKey.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay)
            (leafIndexAt_lt index lay))) ?_
      intro path
      exact Coupled.pure secretKey.parameter table state fuel hclean
        (some (part.1, part.2, path))

def SplitCacheLE (initial final : SplitHashCache) : Prop :=
  ∀ key output, initial key = some output → final key = some output

theorem SplitCacheLE.refl (cache : SplitHashCache) : SplitCacheLE cache cache := by
  intro key output hlookup
  exact hlookup

theorem SplitCacheLE.trans {first second third : SplitHashCache}
    (hfirst : SplitCacheLE first second) (hsecond : SplitCacheLE second third) :
    SplitCacheLE first third := by
  intro key output hlookup
  exact hsecond key output (hfirst key output hlookup)

def CachePreserving
    (computation : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ initial result, result ∈ support (computation.run initial) →
    SplitCacheLE initial result.2

theorem CachePreserving.pure (value : alpha) :
    CachePreserving (pure value : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha) := by
  intro initial result hresult
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
  subst result
  exact SplitCacheLE.refl initial

theorem CachePreserving.bind
    {left : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) beta}
    (hleft : CachePreserving left) (hnext : ∀ value, CachePreserving (next value)) :
    CachePreserving (left >>= next) := by
  intro initial result hresult
  rw [StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hfinal⟩ := hresult
  exact (hleft initial middle hmiddle).trans
    (hnext middle.1 middle.2 result hfinal)

theorem CachePreserving.map
    {computation : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    (hcomputation : CachePreserving computation) (transform : alpha → beta) :
    CachePreserving (transform <$> computation) := by
  rw [map_eq_bind_pure_comp]
  exact hcomputation.bind fun value => CachePreserving.pure (transform value)

theorem splitHashQuery_cachePreserving (key : SplitHashKey) :
    CachePreserving (splitHashQuery key) := by
  intro initial result hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : initial key with
  | some output =>
      simp only [hlookup, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact SplitCacheLE.refl initial
  | none =>
      simp only [hlookup, mem_support_bind_iff] at hresult
      obtain ⟨sample, hsample, hresult⟩ := hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      intro oldKey oldOutput hold
      change Function.update initial key (some sample) oldKey = some oldOutput
      by_cases heq : oldKey = key
      · subst oldKey
        rw [hlookup] at hold
        simp at hold
      · rw [Function.update_of_ne heq]
        exact hold

theorem simulateQ_ordinaryHashImpl_cachePreserving
    (computation : OracleComp HashSpec alpha) :
    CachePreserving (simulateQ ordinaryHashImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact CachePreserving.pure value
  | query_bind input next ih =>
      rw [simulateQ_query_bind]
      exact (splitHashQuery_cachePreserving (.ordinary input)).bind fun output => ih output

theorem hiddenFtsLeafHash_cachePreserving
    (parameter : PublicParameter) (coordinate : Coordinate) :
    CachePreserving (hiddenFtsLeafHash parameter coordinate) := by
  unfold hiddenFtsLeafHash
  exact (splitHashQuery_cachePreserving (.hiddenLeaf coordinate)).bind fun output =>
    CachePreserving.pure (truncateHash output)

theorem ordinaryTweakableHash_cachePreserving
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    CachePreserving (ordinaryTweakableHash parameter domain payload) := by
  unfold ordinaryTweakableHash
  exact (splitHashQuery_cachePreserving
    (.ordinary (tweakableHashInput parameter domain payload))).bind fun output =>
      CachePreserving.pure (truncateHash output)

theorem sequenceFin_cachePreserving {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ position, CachePreserving (computation position)) :
    CachePreserving (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact CachePreserving.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun position => computation position.succ)
          (fun position => hcomputation position.succ)).bind fun tail =>
            CachePreserving.pure (Fin.cases head tail : Fin (n + 1) → alpha)

theorem maskedFtsNode_cachePreserving
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (level nodeIdx : Nat) :
    CachePreserving (maskedFtsNode parameter index tree level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      exact hiddenFtsLeafHash_cachePreserving parameter
        (index, tree, ftsLeafOfNat nodeIdx)
  | succ level ih =>
      rw [maskedFtsNode]
      exact (ih (2 * nodeIdx)).bind fun left =>
        (ih (2 * nodeIdx + 1)).bind fun right =>
          ordinaryTweakableHash_cachePreserving parameter
            (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right)

theorem maskedFtsKey_cachePreserving (parameter : PublicParameter) (index : Index) :
    CachePreserving (maskedFtsKey parameter index) := by
  unfold maskedFtsKey
  exact (sequenceFin_cachePreserving
    (fun tree => maskedFtsNode parameter index tree ftsTreeHeight 0)
    (fun tree => maskedFtsNode_cachePreserving parameter index tree ftsTreeHeight 0)).bind
      fun roots => ordinaryTweakableHash_cachePreserving parameter (.ftsRoots index)
        (ftsRootsPayload roots)

theorem maskedFtsOpen_cachePreserving
    (parameter : PublicParameter) (index : Index) (leaves : DigestTree → FtsLeaf) :
    CachePreserving (maskedFtsOpen parameter index leaves) := by
  unfold maskedFtsOpen
  apply sequenceFin_cachePreserving
  intro tree
  apply sequenceFin_cachePreserving
  intro level
  exact maskedFtsNode_cachePreserving parameter index tree level.val
    (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)

theorem maskedLayerMessage_cachePreserving
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    CachePreserving (maskedLayerMessage secretKey index lay) := by
  unfold maskedLayerMessage
  split
  · exact simulateQ_ordinaryHashImpl_cachePreserving _
  · exact maskedFtsKey_cachePreserving secretKey.parameter index

theorem maskedSignLayer_cachePreserving
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    CachePreserving (maskedSignLayer secretKey index lay) := by
  unfold maskedSignLayer
  exact (maskedLayerMessage_cachePreserving secretKey index lay).bind fun message =>
    (simulateQ_ordinaryHashImpl_cachePreserving
      (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
        message)).bind fun signed => by
      cases signed with
      | none => exact CachePreserving.pure none
      | some part =>
          exact (simulateQ_ordinaryHashImpl_cachePreserving
            (treePath secretKey.parameter lay (treeIndexAt index lay)
              (secretKey.otsSecret lay (treeIndexAt index lay))
              (leafIndexAt index lay))).bind fun path =>
                CachePreserving.pure (some (part.1, part.2, path))

theorem RevealedSynced.mono
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {initial final : SplitHashCache}
    (hsynced : RevealedSynced parameter table state initial)
    (hle : SplitCacheLE initial final) :
    RevealedSynced parameter table state final := by
  intro coordinate value hrevealed
  obtain ⟨hvalue, output, hhidden, hordinary⟩ :=
    hsynced coordinate value hrevealed
  exact ⟨hvalue, output, hle _ output hhidden, hle _ output hordinary⟩

theorem revealedSynced_of_mem_runDetailed_stateFree
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (initial final : SplitHashCache) (value : alpha)
    (computation : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state initial)
    (hstateFree : StateFree computation)
    (hpreserving : CachePreserving computation)
    (hresult : .done false finalState (value, final) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel (computation.run initial))) :
    RevealedSynced parameter table finalState final := by
  obtain ⟨rawValue, heq⟩ := AdaptiveRevealProbe.runDetailed_stateFree_support
    table state fuel (computation.run initial) (hstateFree initial) hclean
    (.done false finalState (value, final)) hresult
  have hstate : finalState = state := by
    exact AdaptiveRevealProbe.DetailedResult.done.inj heq |>.2.1
  have hvalue : (value, final) = rawValue := by
    exact AdaptiveRevealProbe.DetailedResult.done.inj heq |>.2.2
  subst finalState
  subst rawValue
  have hraw : (value, final) ∈ support (computation.run initial) :=
    AdaptiveRevealProbe.mem_support_of_mem_runDetailed_done table state state fuel
      (computation.run initial) false (value, final) hresult
  exact hsynced.mono (hpreserving initial (value, final) hraw)

def HiddenIndexCached (index : Index) (cache : SplitHashCache) : Prop :=
  ∀ tree leafIdx, ∃ output,
    cache (.hiddenLeaf (index, tree, leafIdx)) = some output

theorem HiddenIndexCached.mono
    {index : Index} {initial final : SplitHashCache}
    (hcached : HiddenIndexCached index initial) (hle : SplitCacheLE initial final) :
    HiddenIndexCached index final := by
  intro tree leafIdx
  obtain ⟨output, houtput⟩ := hcached tree leafIdx
  exact ⟨output, hle _ output houtput⟩

set_option maxHeartbeats 800000 in
theorem cacheProperty_of_mem_runDetailed_sequenceFin {n : Nat}
    (table : Coordinate → Digest) (property : SplitHashCache → Prop)
    (hmono : ∀ {initial final}, property initial → SplitCacheLE initial final → property final)
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha)
    (hstateFree : ∀ position, StateFree (computation position))
    (hpreserving : ∀ position, CachePreserving (computation position))
    (position : Fin n)
    (hselected : ∀ state finalState fuel initial final value,
      AdaptiveRevealProbe.tableHits state table = false →
      .done false finalState (value, final) ∈ support
          (AdaptiveRevealProbe.runDetailed table state fuel
            ((computation position).run initial)) →
        property final)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (initial final : SplitHashCache) (values : Fin n → alpha)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hresult : .done false finalState (values, final) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((sequenceFin computation).run initial))) :
    property final := by
  induction n generalizing state finalState initial final with
  | zero => exact position.elim0
  | succ n ih =>
      rw [sequenceFin, StateT.run_bind] at hresult
      obtain ⟨headResult, hhead, hafterHead⟩ :=
        AdaptiveRevealProbe.mem_support_runDetailed_bind_stateFree
          table state finalState fuel ((computation 0).run initial)
          (fun result => ((sequenceFin (fun tailPosition => computation tailPosition.succ) >>= fun tail =>
            pure (Fin.cases result.1 tail : Fin (n + 1) → alpha)).run result.2))
          (hstateFree 0 initial) hclean false (values, final) hresult
      rcases headResult with ⟨head, headCache⟩
      rw [StateT.run_bind] at hafterHead
      obtain ⟨tailResult, htail, hfinished⟩ :=
        AdaptiveRevealProbe.mem_support_runDetailed_bind_stateFree
          table state finalState fuel
          ((sequenceFin (fun tailPosition => computation tailPosition.succ)).run headCache)
          (fun result => (pure (Fin.cases head result.1 : Fin (n + 1) → alpha) :
            StateT SplitHashCache
              (OracleComp (AdaptiveRevealProbe.World Coordinate)) (Fin (n + 1) → alpha)).run
                result.2)
          (sequenceFin_stateFree (fun tailPosition => computation tailPosition.succ)
            (fun tailPosition => hstateFree tailPosition.succ) headCache)
          hclean false (values, final) hafterHead
      rcases tailResult with ⟨tail, tailCache⟩
      change AdaptiveRevealProbe.DetailedResult.done false finalState (values, final) ∈ support
        (pure (AdaptiveRevealProbe.DetailedResult.done
          (AdaptiveRevealProbe.tableHits state table) state
          ((Fin.cases head tail : Fin (n + 1) → alpha), tailCache))) at hfinished
      rw [hclean] at hfinished
      have hfinishedEq := OracleComp.eq_of_mem_support_pure
        (AdaptiveRevealProbe.DetailedResult.done false state
          ((Fin.cases head tail : Fin (n + 1) → alpha), tailCache)) hfinished
      have hfinalCache : final = tailCache := by
        exact (Prod.mk.inj
          (AdaptiveRevealProbe.DetailedResult.done.inj hfinishedEq).2.2).2
      subst final
      cases position using Fin.cases with
      | zero =>
          have hproperty : property headCache :=
            hselected state state fuel initial headCache head hclean hhead
          have hraw : (tail, tailCache) ∈ support
              ((sequenceFin (fun tailPosition => computation tailPosition.succ)).run headCache) :=
            AdaptiveRevealProbe.mem_support_of_mem_runDetailed_done table state state fuel
              ((sequenceFin (fun tailPosition => computation tailPosition.succ)).run headCache)
              false (tail, tailCache) htail
          exact hmono hproperty
            (sequenceFin_cachePreserving
              (fun tailPosition => computation tailPosition.succ)
              (fun tailPosition => hpreserving tailPosition.succ)
              headCache (tail, tailCache) hraw)
      | succ position =>
          exact ih
            (computation := fun tailPosition => computation tailPosition.succ)
            (hstateFree := fun tailPosition => hstateFree tailPosition.succ)
            (hpreserving := fun tailPosition => hpreserving tailPosition.succ)
            (position := position)
            (hselected := fun selectedState selectedFinalState selectedFuel selectedInitial selectedFinal
              selectedValue selectedClean selectedResult =>
                hselected selectedState selectedFinalState selectedFuel selectedInitial
                  selectedFinal selectedValue selectedClean selectedResult)
            (state := state) (finalState := state)
            (initial := headCache) (final := tailCache) (values := tail) hclean htail

noncomputable def maskedSignLayerAfterMessage
    (secretKey : SecretKey) (index : Index) (lay : Layer) (message : Digest) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate))
        (Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))) := do
  let tree := treeIndexAt index lay
  let leafIdx := leafIndexAt index lay
  match ← simulateQ ordinaryHashImpl
      (otsSign secretKey.parameter lay tree leafIdx
        (secretKey.otsSecret lay tree leafIdx) message) with
  | none => pure none
  | some (counter, values) => do
      let path ← simulateQ ordinaryHashImpl
        (treePath secretKey.parameter lay tree (secretKey.otsSecret lay tree) leafIdx)
      pure (some (counter, values, path))

theorem maskedSignLayer_eq
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    maskedSignLayer secretKey index lay = (do
      let message ← maskedLayerMessage secretKey index lay
      maskedSignLayerAfterMessage secretKey index lay message) := by
  unfold maskedSignLayer maskedSignLayerAfterMessage
  rfl

theorem maskedSignLayerAfterMessage_cachePreserving
    (secretKey : SecretKey) (index : Index) (lay : Layer) (message : Digest) :
    CachePreserving (maskedSignLayerAfterMessage secretKey index lay message) := by
  unfold maskedSignLayerAfterMessage
  exact (simulateQ_ordinaryHashImpl_cachePreserving
    (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
      message)).bind fun signed => by
    cases signed with
    | none => exact CachePreserving.pure none
    | some part =>
        exact (simulateQ_ordinaryHashImpl_cachePreserving
          (treePath secretKey.parameter lay (treeIndexAt index lay)
            (secretKey.otsSecret lay (treeIndexAt index lay))
            (leafIndexAt index lay))).bind fun path =>
              CachePreserving.pure (some (part.1, part.2, path))

theorem maskedLayerMessage_bottomLayer
    (secretKey : SecretKey) (index : Index) :
    maskedLayerMessage secretKey index bottomLayer =
      maskedFtsKey secretKey.parameter index := by
  unfold maskedLayerMessage
  simp [bottomLayer, numLayers]

set_option maxHeartbeats 800000 in
theorem hiddenIndexCached_of_mem_runDetailed_maskedSignLayer_bottom
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (initial final : SplitHashCache) (index : Index)
    (value : Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest)))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hresult : .done false finalState (value, final) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((maskedSignLayer secretKey index bottomLayer).run initial))) :
    HiddenIndexCached index final := by
  rw [maskedSignLayer_eq, StateT.run_bind,
    AdaptiveRevealProbe.runDetailed_bind_stateFree table state fuel
      ((maskedLayerMessage secretKey index bottomLayer).run initial)
      (fun result => (maskedSignLayerAfterMessage secretKey index bottomLayer result.1).run
        result.2)
      (maskedLayerMessage_stateFree secretKey index bottomLayer initial),
    mem_support_bind_iff] at hresult
  obtain ⟨messageResult, hmessage, hrest⟩ := hresult
  obtain ⟨messageCache, hmessageEq⟩ :=
    AdaptiveRevealProbe.runDetailed_stateFree_support table state fuel
      ((maskedLayerMessage secretKey index bottomLayer).run initial)
      (maskedLayerMessage_stateFree secretKey index bottomLayer initial) hclean
      messageResult hmessage
  subst messageResult
  simp only at hrest
  have hmessage' := hmessage
  rw [maskedLayerMessage_bottomLayer] at hmessage'
  have hcached : HiddenIndexCached index messageCache.2 :=
    hiddenLeaves_cached_of_mem_runDetailed_maskedFtsKey secretKey.parameter table state state
      fuel initial messageCache.2 index messageCache.1 hclean hmessage'
  have hraw : (value, final) ∈ support
      ((maskedSignLayerAfterMessage secretKey index bottomLayer messageCache.1).run
        messageCache.2) :=
    AdaptiveRevealProbe.mem_support_of_mem_runDetailed_done table state finalState fuel
      ((maskedSignLayerAfterMessage secretKey index bottomLayer messageCache.1).run
        messageCache.2) false (value, final) hrest
  exact hcached.mono
    (maskedSignLayerAfterMessage_cachePreserving secretKey index bottomLayer messageCache.1
      messageCache.2 (value, final) hraw)

set_option maxHeartbeats 800000 in
theorem hiddenIndexCached_of_mem_runDetailed_maskedSignLayers
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (initial final : SplitHashCache) (index : Index)
    (values : Layer →
      Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest)))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hresult : .done false finalState (values, final) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((sequenceFin (fun lay => maskedSignLayer secretKey index lay)).run initial))) :
    HiddenIndexCached index final := by
  exact cacheProperty_of_mem_runDetailed_sequenceFin table (HiddenIndexCached index)
    (fun hcached hle => hcached.mono hle)
    (fun lay => maskedSignLayer secretKey index lay)
    (fun lay => maskedSignLayer_stateFree secretKey index lay)
    (fun lay => maskedSignLayer_cachePreserving secretKey index lay)
    bottomLayer
    (fun selectedState selectedFinalState selectedFuel selectedInitial selectedFinal
      selectedValue selectedClean selectedResult =>
        hiddenIndexCached_of_mem_runDetailed_maskedSignLayer_bottom secretKey table
          selectedState selectedFinalState selectedFuel selectedInitial selectedFinal index
          selectedValue selectedClean selectedResult)
    state finalState fuel initial final values hclean hresult

end SphincsSecurity.Concrete.FtsProbeSimulation
