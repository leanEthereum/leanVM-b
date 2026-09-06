import SphincsSecurity.Proof.OtsProbeChronologicalLayerBody
import SphincsSecurity.Proof.OtsProbeCacheMapActions

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def OrdinaryCacheMonotoneSupport
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ cache result, result ∈ support (computation.run cache) →
    ordinaryQueryCache cache ≤ ordinaryQueryCache result.2

theorem OrdinaryCacheMonotoneSupport.pure (value : α) :
    OrdinaryCacheMonotoneSupport (pure value : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro cache result hresult
  simp only [StateT.run_pure, mem_support_pure_iff] at hresult
  subst result
  exact le_rfl

theorem OrdinaryCacheMonotoneSupport.bind
    {left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : OrdinaryCacheMonotoneSupport left)
    (hnext : ∀ value, OrdinaryCacheMonotoneSupport (next value)) :
    OrdinaryCacheMonotoneSupport (left >>= next) := by
  intro cache result hresult
  rw [StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hrest⟩ := hresult
  exact (hleft cache middle hmiddle).trans (hnext middle.1 middle.2 result hrest)

theorem OrdinaryCacheIndependent.support
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (h : OrdinaryCacheIndependent computation) : OrdinaryCacheSupport computation := by
  intro cache result hresult
  have heq := h cache (ordinaryQueryCache cache)
  rw [replaceOrdinaryCache_self] at heq
  rw [heq, support_map] at hresult
  obtain ⟨entry, _, rfl⟩ := hresult
  rfl

theorem OrdinaryCacheSupport.monotone
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (h : OrdinaryCacheSupport computation) : OrdinaryCacheMonotoneSupport computation := by
  intro cache result hresult
  rw [h cache result hresult]

theorem ordinaryCacheSupport_of_cacheMapCommutes
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (h : ∀ ordinary, CacheMapCommutes (fun cache => replaceOrdinaryCache cache ordinary) computation) :
    OrdinaryCacheSupport computation :=
  OrdinaryCacheIndependent.support (fun cache ordinary => h ordinary cache)

theorem ordinaryCacheMonotoneSupport_ordinaryHash (input : HashInput) :
    OrdinaryCacheMonotoneSupport (ordinaryHashImpl input) := by
  intro cache result hresult
  change result ∈ support ((splitHashQuery (.ordinary input)).run cache) at hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache (.ordinary input) with
  | some output =>
      simp only [hlookup, mem_support_pure_iff] at hresult
      subst result
      exact le_rfl
  | none =>
      simp only [hlookup, mem_support_bind_iff, mem_support_pure_iff] at hresult
      obtain ⟨output, _, rfl⟩ := hresult
      intro other value hcached
      by_cases heq : other = input
      · subst other
        change cache (.ordinary input) = some value at hcached
        simp [hlookup] at hcached
      · simpa [ordinaryQueryCache, Function.update, heq] using hcached

theorem ordinaryCacheMonotoneSupport_simulateQ_ordinaryHashImpl
    (computation : OracleComp HashSpec α) :
    OrdinaryCacheMonotoneSupport (simulateQ ordinaryHashImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact OrdinaryCacheMonotoneSupport.pure value
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact (ordinaryCacheMonotoneSupport_ordinaryHash input).bind ih

theorem ordinaryCacheMonotoneSupport_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (h : ∀ index, OrdinaryCacheMonotoneSupport (computation index)) :
    OrdinaryCacheMonotoneSupport (sequenceFin computation) := by
  induction n with
  | zero => simpa [sequenceFin] using OrdinaryCacheMonotoneSupport.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (h 0).bind fun head => (ih (fun index => computation index.succ) (fun index => h index.succ)).bind
        fun tail => OrdinaryCacheMonotoneSupport.pure (Fin.cases head tail : Fin (n + 1) → α)

theorem ordinaryCacheMonotoneSupport_maskedOtsSignFrom
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (attempts counter : Nat) :
    OrdinaryCacheMonotoneSupport (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact OrdinaryCacheMonotoneSupport.pure none
  | succ attempts ih =>
      unfold maskedOtsSignFrom
      apply (ordinaryCacheMonotoneSupport_simulateQ_ordinaryHashImpl _).bind
      intro encoded
      cases encoded with
      | none => exact ih (counter + 1)
      | some encoding =>
          apply (ordinaryCacheMonotoneSupport_sequenceFin _ fun chainIdx =>
            (ordinaryCacheSupport_of_cacheMapCommutes fun _ => cacheMapCommutes_ensureChainPrefix _ lay tree leafIdx chainIdx (encoding chainIdx)).monotone).bind
          intro _
          exact OrdinaryCacheMonotoneSupport.pure _

theorem ordinaryCacheMonotoneSupport_maskedOtsLayerAfterMessage
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    OrdinaryCacheMonotoneSupport (maskedOtsLayerAfterMessage parameter index lay message) := by
  unfold maskedOtsLayerAfterMessage maskedOtsSign
  apply (ordinaryCacheMonotoneSupport_maskedOtsSignFrom parameter lay (treeIndexAt index lay)
    (leafIndexAt index lay) message encodingAttemptLimit 0).bind
  intro result
  cases result with
  | none => exact OrdinaryCacheMonotoneSupport.pure none
  | some result =>
      exact (ordinaryCacheSupport_of_cacheMapCommutes fun _ =>
        cacheMapCommutes_ensureTreePath _ lay (treeIndexAt index lay) (leafIndexAt index lay)).monotone.bind
          fun _ => OrdinaryCacheMonotoneSupport.pure (some result)

theorem ordinaryCacheMonotoneSupport_maskedChronologicalLayerAfterMessage
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    OrdinaryCacheMonotoneSupport (maskedChronologicalLayerAfterMessage parameter index lay message) := by
  unfold maskedChronologicalLayerAfterMessage
  apply (ordinaryCacheMonotoneSupport_maskedOtsLayerAfterMessage parameter index lay message).bind
  intro result
  cases result with
  | none => exact OrdinaryCacheMonotoneSupport.pure none
  | some result =>
      rcases result with ⟨counter, encoding⟩
      exact (ordinaryCacheSupport_of_cacheMapCommutes fun ordinary =>
        cacheMapCommutes_revealPrivateLayerValues _ (fun cache coordinate output =>
          replaceOrdinaryCache_update_hidden cache ordinary coordinate output) index lay encoding).monotone.bind
        fun _ => OrdinaryCacheMonotoneSupport.pure _

theorem ordinaryCacheMonotoneSupport_maskedUpperChronologicalLayers
    (parameter : PublicParameter) (index : Index) :
    OrdinaryCacheMonotoneSupport (maskedUpperChronologicalLayers parameter index) := by
  unfold maskedUpperChronologicalLayers
  apply ordinaryCacheMonotoneSupport_sequenceFin
  intro lay
  unfold maskedUpperChronologicalLayer
  apply (ordinaryCacheSupport_of_cacheMapCommutes fun ordinary =>
    cacheMapCommutes_maskedTreeRoot _ (fun cache coordinate output =>
      replaceOrdinaryCache_update_hidden cache ordinary coordinate output) _ _).monotone.bind
  intro message
  exact ordinaryCacheMonotoneSupport_maskedChronologicalLayerAfterMessage parameter index _ message

attribute [local irreducible] ftsOpen ftsKey

theorem ordinaryCacheMonotoneSupport_maskedPublishedChronologicalSignAfterDigest
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    OrdinaryCacheMonotoneSupport (maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves) := by
  rw [maskedPublishedChronologicalSignAfterDigest_eq_ftsBoundary]
  apply (ordinaryCacheMonotoneSupport_simulateQ_ordinaryHashImpl _).bind
  intro path
  apply (ordinaryCacheMonotoneSupport_maskedUpperChronologicalLayers parameter index).bind
  intro upper
  apply (ordinaryCacheMonotoneSupport_simulateQ_ordinaryHashImpl _).bind
  intro root
  apply (ordinaryCacheMonotoneSupport_maskedChronologicalLayerAfterMessage parameter index bottomLayer root).bind
  intro bottom
  rw [publishChronologicalSignature_eq_body, map_eq_bind_pure_comp]
  exact (ordinaryCacheSupport_publishSignatureBody randomness index path (Fin.snoc upper bottom)).monotone.bind
    fun _ => OrdinaryCacheMonotoneSupport.pure _

end SphincsSecurity.Concrete.OtsProbeSimulation
