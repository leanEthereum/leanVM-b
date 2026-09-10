import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FtsProbeSimulation
import SphincsSecurity.Proof.OtsProbeSimulation

/-!
# Materialized root-avoiding ordinal prefix

The auxiliary prefix executes against the already materialized shadow but derives every planned
candidate from its canonical public view. Before the selected ordinal it stops if a candidate
guesses either distinguished root. On the surviving branch every direct query satisfies the cache
quotient's safe-input premise.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

noncomputable def purePeekPositionValues
    (state : LazyRevealProbe.State Coordinate) : List Position → Option (List Digest)
  | [] => some []
  | position :: remaining =>
      match truncateHash <$> state.values (.position position) with
      | none => none
      | some value =>
          match purePeekPositionValues state remaining with
          | none => none
          | some values => some (value :: values)

noncomputable def purePeekTableInput
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate) :
    Coordinate → Option HashInput
  | .chainStart _ _ _ _ => none
  | .position position@(.chain lay tree leafIdx chainIdx step) =>
      if step.val = 0 then
        match truncateHash <$> state.values (.chainStart lay tree leafIdx chainIdx) with
        | none => none
        | some value => some (tweakableHashInput parameter position.domain (digestBytes value))
      else
        match purePeekPositionValues state position.children with
        | none => none
        | some values => some (tweakableHashInput parameter position.domain
            (values.flatMap digestBytes))
  | .position position =>
      match purePeekPositionValues state position.children with
      | none => none
      | some values => some (tweakableHashInput parameter position.domain
          (values.flatMap digestBytes))

noncomputable def resolvePublicKnownInput
    (parameter : PublicParameter) (publicState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (input : HashInput) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput :=
  match purePeekTableInput parameter publicState coordinate with
  | some knownInput =>
      if knownInput = input then do
        let output ← revealCoordinateOutput coordinate
        publishCoordinate coordinate
        modify fun cache : SplitHashCache =>
          Function.update cache (.ordinary input) (some output)
        pure output
      else splitHashQuery (.ordinary input)
  | none => splitHashQuery (.ordinary input)

end SphincsSecurity.Concrete.OtsProbeSimulation
