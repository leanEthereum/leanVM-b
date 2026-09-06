import SphincsSecurity.Proof.OtsProbeChronologicalLayerBody

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

def CacheMapCommutes (rewrite : SplitHashCache → SplitHashCache)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ cache, computation.run (rewrite cache) =
    (fun result => (result.1, rewrite result.2)) <$> computation.run cache

theorem CacheMapCommutes.pure (rewrite : SplitHashCache → SplitHashCache) (value : α) :
    CacheMapCommutes rewrite (pure value : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro cache
  simp [StateT.run_pure]

theorem CacheMapCommutes.bind
    {rewrite : SplitHashCache → SplitHashCache}
    {left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : CacheMapCommutes rewrite left) (hnext : ∀ value, CacheMapCommutes rewrite (next value)) :
    CacheMapCommutes rewrite (left >>= next) := by
  intro cache
  rw [StateT.run_bind, hleft, bind_map_left, StateT.run_bind, map_bind]
  apply bind_congr
  intro result
  exact hnext result.1 result.2

theorem CacheMapCommutes.liftM (rewrite : SplitHashCache → SplitHashCache)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    CacheMapCommutes rewrite (liftM computation) := by
  intro cache
  simp only [StateT.run_liftM, map_bind, map_pure]

theorem cacheMapCommutes_sequenceFin {n : Nat} (rewrite : SplitHashCache → SplitHashCache)
    (computation : Fin n → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index, CacheMapCommutes rewrite (computation index)) :
    CacheMapCommutes rewrite (sequenceFin computation) := by
  induction n with
  | zero => simpa [sequenceFin] using CacheMapCommutes.pure rewrite Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun head =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun tail =>
            CacheMapCommutes.pure rewrite (Fin.cases head tail : Fin (n + 1) → α)

end SphincsSecurity.Concrete.OtsProbeSimulation
