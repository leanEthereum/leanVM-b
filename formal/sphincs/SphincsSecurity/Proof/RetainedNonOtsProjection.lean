import SphincsSecurity.Proof.SecurityParentResidualEndpoint
import SphincsSecurity.Proof.JointPrimitiveTerminal

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation

set_option backward.isDefEq.respectTransparency false

theorem retainedAfterSecretsComputation_rom_projection
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (simulateQ romImpl (retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret)).run ∅ =
      actualRetainedGameAfterOtsSecret adversary parameter ftsSecret otsSecret := by
  rw [retainedAfterSecretsComputation, simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM]
  unfold actualRetainedGameAfterOtsSecret
  apply bind_congr
  rintro ⟨root, cache⟩
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [← simulateQ_unloggedMapped_eq_expanded]

theorem relTriple_firstParentRetained_viewed_log
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    RelTriple (runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
      (retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ none)
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret)
      (fun left right => retainedGameLogProjection left.1 = OtsProbeSimulation.viewedGameLogProjection right) := by
  classical
  have hretained := runFirstException_project (CleanParentSettlement parameter otsSecret ftsSecret)
    (retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ none
  rw [retainedAfterSecretsComputation_rom_projection] at hretained
  have hview := gameAfterSecretsWithViewTrace_actualRetained_projection adversary parameter ftsSecret
    (tableOfOtsSecret otsSecret)
  rw [actualRetainedGameAfterTable_eq_afterOtsSecret, tableOtsSecret_tableOfOtsSecret, ← hretained,
    Functor.map_map] at hview
  exact relTriple_of_evalDist_map_eq_general _ _ _ _ (congrArg evalDist hview.symm)

theorem cleanOtsOpening_imp_retainedProbe_of_log_eq
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (left : RetainedGameResult × QueryCache HashSpec)
    (right : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hlog : retainedGameLogProjection left = OtsProbeSimulation.viewedGameLogProjection right)
    (hopening : cleanOtsOpeningEvent parameter otsSecret ftsSecret right) :
    WinningRetainedVerifyProbeAfterOtsSecret parameter otsSecret ftsSecret left := by
  let table := tableOfOtsSecret otsSecret
  have hopen : cleanOtsOpeningEvent parameter (tableOtsSecret table) ftsSecret right := by
    simpa only [table, tableOtsSecret_tableOfOtsSecret] using hopening
  apply winningRetainedOtsOpening_imp_verifyProbe parameter table ftsSecret left
  apply logProjection_winningWitness_imp_retained
  rw [hlog]
  rcases hopen with hfresh | hbackward
  · rcases hfresh with ⟨⟨hbad, hwin⟩, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval, hfresh⟩
    exact ⟨hwin, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval, hbad, Or.inl hfresh⟩
  · rcases hbackward with ⟨⟨hbad, hwin⟩, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval, hbackward⟩
    exact ⟨hwin, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, heval, hbad, Or.inr hbackward⟩

def nonOtsViewedTerminalEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result ∨
    cleanUncoveredEvent parameter otsSecret ftsSecret result ∨
    cleanMessageEvent parameter otsSecret ftsSecret result ∨
    ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result

theorem nonOtsViewedTerminalEvent_of_retained_log (adversary : Adversary) (secrets : SampledSecrets)
    (left : (RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)
    (right : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hlog : retainedGameLogProjection left.1 = OtsProbeSimulation.viewedGameLogProjection right)
    (hright : right ∈ support (gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret secrets.ftsSecret))
    (hleft : retainedNonOtsResidual (secrets, left)) :
    nonOtsViewedTerminalEvent secrets.parameter secrets.otsSecret secrets.ftsSecret right := by
  have hwinEq := congrArg (fun result : RetainedGameLogResult => result.1.2.2) hlog
  have hcacheEq := congrArg (fun result : RetainedGameLogResult => result.2.1) hlog
  change retainedRestVerdict left.1.1.2 = right.1.2.2 at hwinEq
  change left.1.2 = right.2.cache at hcacheEq
  have hwin : right.1.2.2 = true := hwinEq.symm.trans hleft.1
  have hclean : ¬ Bad secrets.parameter secrets.otsSecret secrets.ftsSecret right.2.cache := hcacheEq ▸ hleft.2.1
  have hnotOpening : ¬ cleanOtsOpeningEvent secrets.parameter secrets.otsSecret secrets.ftsSecret right :=
    fun h => hleft.2.2 (cleanOtsOpening_imp_retainedProbe_of_log_eq secrets.parameter secrets.otsSecret secrets.ftsSecret left.1 right hlog h)
  have hterminal := (gameAfterSecretsWithViewTrace_winning_honestLeakTerminal_classify adversary
    secrets.parameter secrets.otsSecret secrets.ftsSecret right hright hwin).resolve_left hclean
  rcases viewedWinningHonestLeakTerminalWitness_cases secrets.parameter secrets.otsSecret secrets.ftsSecret right
    hterminal with hfresh | hencoding | hbackward | hmessage | hforest | huncovered
  · exact False.elim (hnotOpening (Or.inl ⟨⟨hclean, hwin⟩, hfresh⟩))
  · exact Or.inl hencoding
  · exact False.elim (hnotOpening (Or.inr ⟨⟨hclean, hwin⟩, hbackward⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hclean, hmessage⟩))
  · exact Or.inr (Or.inr (Or.inr hforest))
  · exact Or.inr (Or.inl ⟨hclean, huncovered⟩)

theorem probEvent_retainedNonOtsResidual_le_viewed_afterSecrets (adversary : Adversary) (secrets : SampledSecrets) :
    Pr[fun result => retainedNonOtsResidual (secrets, result) |
      runFirstException (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
        (retainedAfterSecretsComputation adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ none] ≤
      Pr[nonOtsViewedTerminalEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
        gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret secrets.ftsSecret] := by
  apply probEvent_le_of_relTriple (FtsProbeSimulation.relTriple_and_right_support
    (relTriple_firstParentRetained_viewed_log adversary secrets.parameter secrets.otsSecret secrets.ftsSecret))
  intro left right hrel hleft
  exact nonOtsViewedTerminalEvent_of_retained_log adversary secrets left right hrel.1 hrel.2 hleft

theorem probEvent_retainedNonOtsResidual_le_viewed (adversary : Adversary) :
    Pr[retainedNonOtsResidual | sampledFirstParentRetainedGame adversary] ≤
      Pr[SampledViewedEvent nonOtsViewedTerminalEvent | sampledViewedGame adversary] := by
  rw [sampledFirstParentRetainedGame, probEvent_bind_eq_tsum, probEvent_sampledViewedGame_eq_weighted]
  apply ENNReal.tsum_le_tsum
  intro secrets
  apply mul_le_mul' le_rfl
  simpa only [bind_pure_comp, probEvent_map, Function.comp_def] using
    probEvent_retainedNonOtsResidual_le_viewed_afterSecrets adversary secrets

end SphincsSecurity.Concrete
