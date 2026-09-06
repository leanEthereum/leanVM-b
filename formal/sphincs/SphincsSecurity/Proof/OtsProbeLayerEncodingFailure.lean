import SphincsSecurity.Proof.OtsProbeEncodingFailureSupport
import SphincsSecurity.Proof.OtsProbeResolvedCacheSupport

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OrdinaryCacheMonotoneSupport maskedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem anyEncodingInputsExhausted_of_mem_sequenceFin_none {n : Nat}
    (computation : Fin n → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) (Option α))
    (hmonotone : ∀ index, OrdinaryCacheMonotoneSupport (computation index))
    (hfailure : ∀ index context fuel table cache result,
      some result ∈ support (runResolvedFromTable context fuel table ((computation index).run cache)) →
      result.value.1 = none → AnyEncodingInputsExhausted (ordinaryQueryCache result.value.2))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult ((Fin n → Option α) × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table ((sequenceFin computation).run cache)))
    (index : Fin n) (hfailed : result.value.1 index = none) :
    AnyEncodingInputsExhausted (ordinaryQueryCache result.value.2) := by
  induction n generalizing context fuel table cache with
  | zero => exact Fin.elim0 index
  | succ n ih =>
      rw [sequenceFin, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
      obtain ⟨headOption, hhead, hrest⟩ := hresult
      cases headOption with
      | none => simp at hrest
      | some head =>
          dsimp only at hrest
          rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
          obtain ⟨tailOption, htail, hreturn⟩ := hrest
          cases tailOption with
          | none => simp at hreturn
          | some tail =>
              simp [runResolvedFromTable] at hreturn
              subst result
              cases index using Fin.cases with
              | zero =>
                  have hexhausted := hfailure 0 context fuel table cache head hhead hfailed
                  exact hexhausted.mono ((ordinaryCacheMonotoneSupport_sequenceFin _
                    (fun i => hmonotone i.succ)).resolved head.context head.remaining head.table head.value.2 tail htail)
              | succ index =>
                  exact ih (fun i => computation i.succ) (fun i => hmonotone i.succ) (fun i => hfailure i.succ)
                    head.context head.remaining head.table head.value.2 tail htail index hfailed

theorem anyEncodingInputsExhausted_of_mem_failed_upperChronologicalLayer
    (parameter : PublicParameter) (index : Index) (lay : Fin (numLayers - 1))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option ChronologicalLayerPart × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedUpperChronologicalLayer parameter index lay).run cache)))
    (hfailed : result.value.1 = none) : AnyEncodingInputsExhausted (ordinaryQueryCache result.value.2) := by
  rw [maskedUpperChronologicalLayer, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨rootOption, hroot, hrest⟩ := hresult
  cases rootOption with
  | none => simp at hrest
  | some root =>
      exact ⟨parameter, _, root.value.1,
        encodingInputsExhausted_of_mem_failed_chronologicalLayerAfterMessage parameter index _ root.value.1
          root.context root.remaining root.table root.value.2 result hrest hfailed⟩

theorem anyEncodingInputsExhausted_of_mem_upperChronologicalLayers_none
    (parameter : PublicParameter) (index : Index)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult ((Fin (numLayers - 1) → Option ChronologicalLayerPart) × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedUpperChronologicalLayers parameter index).run cache)))
    (lay : Fin (numLayers - 1)) (hfailed : result.value.1 lay = none) :
    AnyEncodingInputsExhausted (ordinaryQueryCache result.value.2) := by
  apply anyEncodingInputsExhausted_of_mem_sequenceFin_none (maskedUpperChronologicalLayer parameter index) _
    (fun lay => anyEncodingInputsExhausted_of_mem_failed_upperChronologicalLayer parameter index lay)
    context fuel table cache result hresult lay hfailed
  intro lay
  unfold maskedUpperChronologicalLayer
  exact (ordinaryCacheSupport_of_cacheMapCommutes fun ordinary =>
    cacheMapCommutes_maskedTreeRoot _ (fun cache coordinate output =>
      replaceOrdinaryCache_update_hidden cache ordinary coordinate output) _ _).monotone.bind
      fun message => ordinaryCacheMonotoneSupport_maskedChronologicalLayerAfterMessage parameter index _ message

end SphincsSecurity.Concrete.OtsProbeSimulation
