import SphincsSecurity.Proof.OtsProbeNativeOrdinaryCacheHash
import SphincsSecurity.Proof.OtsProbeLiveHashSelection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def OrdinaryCacheSelectionRel : Option CanonicalQuerySelection → Option CanonicalQuerySelection → Prop
  | some left, some right =>
      left.input = right.input ∧ left.context = right.context ∧ left.fuel = right.fuel ∧
        left.table = right.table ∧ OrdinarySplitCacheEq left.cache right.cache
  | none, none => True
  | _, _ => False

theorem relTriple_liveNativeHashQuerySelection_ordinaryCache
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ input, OrdinaryCacheNativeCouples (impl input))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache) (hcache : OrdinarySplitCacheEq leftCache rightCache) :
    RelTriple (liveNativeHashQuerySelection impl computation ordinal context fuel table leftCache)
      (liveNativeHashQuerySelection impl computation ordinal context fuel table rightCache)
      OrdinaryCacheSelectionRel := by
  induction computation using OracleComp.inductionOn generalizing ordinal context fuel table leftCache rightCache with
  | pure value => exact relTriple_pure_pure trivial
  | query_bind input next ih =>
      rw [liveNativeHashQuerySelection_query_bind, liveNativeHashQuerySelection_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, if_pos hcomplete]
        by_cases hselected : IsOuterHash input ∧ ordinal = 0
        · rw [if_pos hselected, if_pos hselected]
          exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
        · rw [if_neg hselected, if_neg hselected]
          apply relTriple_bind (himpl input leftCache rightCache hcache context fuel table)
          intro left right hrel
          cases left with
          | none =>
              cases right with
              | none => exact relTriple_pure_pure trivial
              | some right => contradiction
          | some left =>
              cases right with
              | none => contradiction
              | some right =>
                  rcases hrel with ⟨hcontext, hfuel, htable, hvalue, hcaches⟩
                  simp only
                  rw [← hcontext, ← hfuel, ← htable, ← hvalue]
                  exact ih left.value.1 _ left.context left.remaining left.table left.value.2 right.value.2 hcaches
      · rw [if_neg hcomplete, if_neg hcomplete]
        exact relTriple_pure_pure trivial

def eraseHiddenSplitCache (cache : SplitHashCache) : SplitHashCache
  | .ordinary input => cache (.ordinary input)
  | .hidden _ => none

def eraseHiddenSelectionCache (selection : Option CanonicalQuerySelection) : Option CanonicalQuerySelection :=
  selection.map fun selection => { selection with cache := eraseHiddenSplitCache selection.cache }

theorem OrdinaryCacheSelectionRel.eraseHiddenCache
    {left right : Option CanonicalQuerySelection} (h : OrdinaryCacheSelectionRel left right) :
    eraseHiddenSelectionCache left = eraseHiddenSelectionCache right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => contradiction
  | some left =>
      cases right with
      | none => contradiction
      | some right =>
          rcases h with ⟨hinput, hcontext, hfuel, htable, hcache⟩
          have hcaches : eraseHiddenSplitCache left.cache = eraseHiddenSplitCache right.cache := by
            funext key
            cases key with
            | ordinary input => exact hcache input
            | hidden coordinate => rfl
          simp only [eraseHiddenSelectionCache, Option.map_some, hinput, hcontext, hfuel, htable, hcaches]

theorem evalDist_nativeChronologicalHashSelection_eraseHiddenCache
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache) (hcache : OrdinarySplitCacheEq leftCache rightCache) :
    evalDist (eraseHiddenSelectionCache <$>
      liveNativeHashQuerySelection (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        computation ordinal context fuel table leftCache) =
    evalDist (eraseHiddenSelectionCache <$>
      liveNativeHashQuerySelection (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        computation ordinal context fuel table rightCache) := by
  apply evalDist_map_eq_of_relTriple
  apply relTriple_post_mono
    (relTriple_liveNativeHashQuerySelection_ordinaryCache _
      (ordinaryCacheNativeCouples_chronologicalOuterQuery parameter root ftsSecret)
      computation ordinal context fuel table leftCache rightCache hcache)
  intro left right hrel
  exact hrel.eraseHiddenCache

end SphincsSecurity.Concrete.OtsProbeSimulation
