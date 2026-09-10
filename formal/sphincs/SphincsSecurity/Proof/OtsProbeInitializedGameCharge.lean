import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeEnsuredInitialization
import SphincsSecurity.Proof.OtsProbeLiveGameCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedNativeDirectRisk
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat) : ENNReal :=
  (∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit nativeCutCandidate |
    sampledEnsuredNativeProbeCut targets (nativeChronologicalRetainedComputation adversary parameter ftsSecret) fuel ordinal]) +
  ∑' table, Pr[= table | sampleOtsHashTable] *
    ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table (ensuredInitialContext targets) fuel
          (privatePositionProbeCutAt target (nativeChronologicalRetainedComputation adversary parameter ftsSecret) ordinal)]

noncomputable def sampledInitializedNativeDirectRisk
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] * initializedNativeDirectRisk targets adversary parameter ftsSecret fuel q

end SphincsSecurity.Concrete.OtsProbeSimulation
