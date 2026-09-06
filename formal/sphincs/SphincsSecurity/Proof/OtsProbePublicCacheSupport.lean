import SphincsSecurity.Proof.OtsProbeCoupling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def OrdinaryCacheSupport
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ cache result, result ∈ support (computation.run cache) →
    ordinaryQueryCache result.2 = ordinaryQueryCache cache

theorem OrdinaryCacheSupport.pure (value : α) :
    OrdinaryCacheSupport (pure value : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro cache result hresult
  simp only [StateT.run_pure, mem_support_pure_iff] at hresult
  subst result
  rfl

theorem OrdinaryCacheSupport.bind
    {left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : OrdinaryCacheSupport left)
    (hnext : ∀ value, OrdinaryCacheSupport (next value)) :
    OrdinaryCacheSupport (left >>= next) := by
  intro cache result hresult
  rw [StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hrest⟩ := hresult
  exact (hnext middle.1 middle.2 result hrest).trans (hleft cache middle hmiddle)

theorem ordinaryCacheSupport_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomponent : ∀ index, OrdinaryCacheSupport (computation index)) :
    OrdinaryCacheSupport (sequenceFin computation) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using OrdinaryCacheSupport.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun head =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun tail =>
            OrdinaryCacheSupport.pure
              (Fin.cases head tail : Fin (n + 1) → alpha)

theorem ordinaryCacheSupport_revealCoordinate (coordinate : Coordinate) :
    OrdinaryCacheSupport (revealCoordinate coordinate) := by
  intro cache result hresult
  rw [revealCoordinate_run, mem_support_bind_iff] at hresult
  obtain ⟨output, _, hresult⟩ := hresult
  simp only [mem_support_pure_iff] at hresult
  subst result
  exact ordinaryQueryCache_update_hidden cache coordinate output

theorem ordinaryCacheSupport_publishCoordinate (coordinate : Coordinate) :
    OrdinaryCacheSupport (publishCoordinate coordinate) := by
  intro cache result hresult
  simp only [publishCoordinate, StateT.run_liftM, mem_support_bind_iff, mem_support_pure_iff] at hresult
  obtain ⟨output, _, rfl⟩ := hresult
  rfl

theorem ordinaryCacheSupport_revealPublishedCoordinate
    (coordinate : Coordinate) :
    OrdinaryCacheSupport (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (ordinaryCacheSupport_revealCoordinate coordinate).bind fun _ =>
    (ordinaryCacheSupport_publishCoordinate coordinate).bind fun _ =>
      OrdinaryCacheSupport.pure _

theorem ordinaryCacheSupport_revealLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    OrdinaryCacheSupport (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (ordinaryCacheSupport_sequenceFin _ fun chainIdx =>
    ordinaryCacheSupport_revealPublishedCoordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx))).bind fun _ =>
      (ordinaryCacheSupport_sequenceFin _ fun level => by
        split
        · cases hlevelValue : level.val with
          | zero => exact ordinaryCacheSupport_revealPublishedCoordinate _
          | succ current =>
              rw [show current + 1 = Nat.succ current by omega]
              change OrdinaryCacheSupport
                (if hlevel : current < maxLayerHeight then
                  revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                    ⟨current, hlevel⟩ (leafOfNat
                      (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                else pure 0)
              by_cases hlevel : current < maxLayerHeight
              · rw [dif_pos hlevel]
                exact ordinaryCacheSupport_revealPublishedCoordinate _
              · rw [dif_neg hlevel]
                exact OrdinaryCacheSupport.pure 0
        · exact OrdinaryCacheSupport.pure 0).bind fun _ =>
          OrdinaryCacheSupport.pure _

end SphincsSecurity.Concrete.OtsProbeSimulation
