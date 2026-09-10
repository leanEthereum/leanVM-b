import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeOrdinaryCacheSigner

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

theorem ordinaryCacheNativeCouples_peekPositionValues
    : ∀ positions,
    OrdinaryCacheNativeCouples
      (peekPositionValues positions)
  | [] => by
      rw [peekPositionValues]
      exact ordinaryCacheNativeCouples_pure (some [])
  | position :: remaining => by
      rw [peekPositionValues]
      apply (ordinaryCacheNativeCouples_peekCoordinate
        (.position position)).bind
      intro value
      cases value with
      | none => exact ordinaryCacheNativeCouples_pure none
      | some value =>
          apply (ordinaryCacheNativeCouples_peekPositionValues
            remaining).bind
          intro values
          cases values with
          | none => exact ordinaryCacheNativeCouples_pure none
          | some values =>
              exact ordinaryCacheNativeCouples_pure
                (some (value :: values))

theorem ordinaryCacheNativeCouples_peekTableInput
    (parameter : PublicParameter) (coordinate : Coordinate) :
    OrdinaryCacheNativeCouples
      (peekTableInput parameter coordinate) := by
  cases coordinate with
  | chainStart =>
      exact ordinaryCacheNativeCouples_pure none
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            exact (ordinaryCacheNativeCouples_peekCoordinate
              (.chainStart lay tree leafIdx chainIdx)).bind fun value =>
                match value with
                | none => ordinaryCacheNativeCouples_pure none
                | some _ => ordinaryCacheNativeCouples_pure _
          · rw [if_neg hzero]
            exact (ordinaryCacheNativeCouples_peekPositionValues
              (Position.chain lay tree leafIdx chainIdx step).children).bind fun values =>
                match values with
                | none => ordinaryCacheNativeCouples_pure none
                | some _ => ordinaryCacheNativeCouples_pure _
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [peekTableInput]
          exact (ordinaryCacheNativeCouples_peekPositionValues
            _).bind fun values =>
              match values with
              | none => ordinaryCacheNativeCouples_pure none
              | some _ => ordinaryCacheNativeCouples_pure _

theorem ordinaryCacheNativeCouples_resolveKnownInput
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    OrdinaryCacheNativeCouples (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  apply (ordinaryCacheNativeCouples_peekTableInput parameter coordinate).bind
  intro knownInput
  cases knownInput with
  | none => exact ordinaryCacheNativeCouples_splitHashQuery input
  | some knownInput =>
      simp only
      by_cases heq : knownInput = input
      · rw [if_pos heq]
        exact (ordinaryCacheNativeCouples_revealCoordinateOutput coordinate).bind fun output =>
          (ordinaryCacheNativeCouples_publishCoordinate coordinate).bind fun _ =>
            (ordinaryCacheNativeCouples_modifyOrdinary input output).bind fun _ =>
              ordinaryCacheNativeCouples_pure output
      · rw [if_neg heq]
        exact ordinaryCacheNativeCouples_splitHashQuery input

theorem ordinaryCacheNativeCouples_probeFirstMissingInputCoordinate (input : HashInput) :
    ∀ slot coordinates, OrdinaryCacheNativeCouples (probeFirstMissingInputCoordinate input slot coordinates)
  | _, [] => ordinaryCacheNativeCouples_pure ()
  | slot, coordinate :: remaining => by
      rw [probeFirstMissingInputCoordinate]
      apply (ordinaryCacheNativeCouples_peekCoordinate coordinate).bind
      intro value
      cases value with
      | none => exact ordinaryCacheNativeCouples_probe _
      | some value => exact ordinaryCacheNativeCouples_probeFirstMissingInputCoordinate input (slot + 1) remaining

theorem ordinaryCacheNativeCouples_prepareLeafInputProbe
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    OrdinaryCacheNativeCouples (prepareLeafInputProbe input candidate lay tree leafIdx) := by
  unfold prepareLeafInputProbe
  apply (ordinaryCacheNativeCouples_peekCoordinate candidate.coordinate).bind
  intro value
  cases value with
  | none => exact ordinaryCacheNativeCouples_probe candidate
  | some value => exact ordinaryCacheNativeCouples_probeFirstMissingInputCoordinate input 0 _

theorem ordinaryCacheNativeCouples_probingHashQuery
    (parameter : PublicParameter) (input : HashInput) :
    OrdinaryCacheNativeCouples (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => exact ordinaryCacheNativeCouples_splitHashQuery input
      | some position =>
          cases position with
          | chain | leaf => exact ordinaryCacheNativeCouples_resolveKnownInput parameter _ input
          | node =>
              exact (ordinaryCacheNativeCouples_probeFirstMissingInputCoordinate input 0 _).bind fun _ =>
                ordinaryCacheNativeCouples_resolveKnownInput parameter _ input
          | ftsLeaf | ftsNode | ftsRoots => exact ordinaryCacheNativeCouples_splitHashQuery input
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none =>
          exact (ordinaryCacheNativeCouples_probe candidate).bind fun _ =>
            ordinaryCacheNativeCouples_resolveKnownInput parameter _ input
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              exact (ordinaryCacheNativeCouples_prepareLeafInputProbe input candidate lay tree leafIdx).bind fun _ =>
                ordinaryCacheNativeCouples_resolveKnownInput parameter _ input
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              exact (ordinaryCacheNativeCouples_probe candidate).bind fun _ =>
                ordinaryCacheNativeCouples_resolveKnownInput parameter _ input

theorem ordinaryCacheNativeCouples_chronologicalOuterQuery
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) :
    OrdinaryCacheNativeCouples (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input) := by
  cases input with
  | inl input =>
      cases input with
      | inl n => exact ordinaryCacheNativeCouples_splitUniformImpl n
      | inr input => exact ordinaryCacheNativeCouples_probingHashQuery parameter input
  | inr message => exact ordinaryCacheNativeCouples_chronologicalSign parameter root ftsSecret message

end SphincsSecurity.Concrete.OtsProbeSimulation
