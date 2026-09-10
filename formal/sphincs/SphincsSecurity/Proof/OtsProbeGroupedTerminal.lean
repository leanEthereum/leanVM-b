import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeTerminal
import SphincsSecurity.Proof.TerminalSampling

/-!
# Grouped one-time terminal event

Fresh layer openings and backward chain openings both imply the same retained verifier probe.
Grouping them before the terminal union bound charges that probe event once.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def cleanOtsOpeningEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  cleanFreshEvent parameter otsSecret ftsSecret result ∨
    cleanBackwardEvent parameter otsSecret ftsSecret result

namespace OtsProbeSimulation

def WinningRetainedOtsOpeningWitness (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  WinningRetainedWitnessFor parameter table ftsSecret
    fun f cache secretKey log forgery index leaves =>
      ¬Bad parameter (tableOtsSecret table) ftsSecret cache ∧
        (SettledForgedFreshLayerOpening f cache secretKey log index leaves forgery.signature ∨
          SettledForgedBackwardChainOpening f cache secretKey log index leaves forgery.signature)

theorem winningRetainedOtsOpening_imp_verifyProbe
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : RetainedGameResult × QueryCache HashSpec)
    (hwitness : WinningRetainedOtsOpeningWitness parameter table ftsSecret result) :
    WinningRetainedVerifyProbeWitness parameter table ftsSecret result := by
  rcases hwitness with ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest,
    hadmissible, heval, hbad, hfresh | hbackward⟩
  · exact winningRetainedFresh_imp_verifyProbe parameter table ftsSecret result
      ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval,
        hbad, hfresh⟩
  · exact winningRetainedBackward_imp_verifyProbe parameter table ftsSecret result
      ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval,
        hbad, hbackward⟩

end OtsProbeSimulation

end SphincsSecurity.Concrete
