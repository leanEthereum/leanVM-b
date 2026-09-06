import SphincsSecurity.Proof.FirstOtsParentQuery
import SphincsSecurity.Proof.OtsProbeEarlyParentRetained
import SphincsSecurity.Proof.OtsProbeCanonicalChargeGame

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem relTriple_firstParentGame_prehitRetained
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
    RelTriple (runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
      (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ none)
      (prehitRetainedQueryTrace adversary parameter table ftsSecret)
      (fun left right => FirstOtsParentRecord parameter left → EarlyOtsParentAtQuery parameter otsSecret ftsSecret right) := by
  classical
  dsimp only
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  let exception := CleanParentSettlement parameter otsSecret ftsSecret
  let rootComputation : OracleComp OracleWorld Digest :=
    liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)
  have hleft := runFirstException_project exception rootComputation ∅ none
  have hright := TightEncoding.runEncodingPrehitMonitor_project accountingKey rootComputation ∅ false
  have hroot := relTriple_of_evalDist_map_eq_general
    (runFirstException exception rootComputation ∅ none)
    (TightEncoding.runEncodingPrehitMonitor accountingKey rootComputation ∅ false)
    Prod.fst Prod.fst (congrArg evalDist (hleft.trans hright.symm))
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hroot
    (fun left => left.2 = none) (by
      intro left hleft
      exact runFirstException_treeRoot_no_record accountingKey exception (fun _ _ _ h => h.2)
        topLayer rootTree hleft)
  rw [gameAfterSecrets, runFirstException_bind]
  unfold prehitRetainedQueryTrace
  apply relTriple_bind hsupported
  rintro ⟨⟨root, cache⟩, saved⟩ ⟨⟨actualRoot, actualCache⟩, hit⟩ hroot
  have heq : root = actualRoot ∧ cache = actualCache := Prod.mk.inj hroot.1
  rcases heq with ⟨rfl, rfl⟩
  have hsaved : saved = none := hroot.2
  subst saved
  dsimp only
  rw [gameRest_eq_map_retained, runFirstException_map]
  let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  have htail := relTriple_firstException_prehitQueryTrace exception accountingKey secretKey
    (retainedGameRestComputation adversary ⟨root, parameter⟩)
    (⟨cache, ⟨[], [], []⟩, [], none⟩, hit) none
  have hmap := relTriple_map
    (f := fun left : (RetainedRestResult × QueryCache HashSpec) × Option ExceptionRecord =>
      ((decide (SigningTranscript.Valid left.1.1.1.2 ∧
        ¬SigningTranscript.Contains left.1.1.1.2 left.1.1.1.1) && left.1.1.2, left.1.2), left.2))
    (g := fun right : (RetainedRestResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot =>
      (((root, right.1.1), right.1.2), right.2))
    (R := fun left right => FirstOtsParentRecord parameter left →
      EarlyOtsParentAtQuery parameter otsSecret ftsSecret right)
    (relTriple_post_mono htail (fun _ _ hrel hrecord =>
      hrel.early_parent_of_ots_record (fun _ _ _ h => h.2) hrecord))
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using hmap

theorem probEvent_firstOtsParentRecord_game_le_early_parent
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
    Pr[FirstOtsParentRecord parameter | runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
      (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ none] ≤
      Pr[EarlyOtsParentAtQuery parameter otsSecret ftsSecret | prehitRetainedQueryTrace adversary parameter table ftsSecret] := by
  exact probEvent_le_of_relTriple (relTriple_firstParentGame_prehitRetained adversary parameter table ftsSecret)
    (fun _ _ hrel hrecord => hrel hrecord)

theorem probEvent_firstOtsParentRecord_game_le_nativeTerminalFailure
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
    Pr[FirstOtsParentRecord parameter | runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
      (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ none] ≤
      Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot targets adversary parameter table ftsSecret fuel] := by
  exact (probEvent_firstOtsParentRecord_game_le_early_parent adversary parameter table ftsSecret).trans
    (probEvent_earlyOtsParentAtQuery_le_nativeTerminalFailure targets adversary parameter table ftsSecret fuel)

end SphincsSecurity.Concrete.OtsProbeSimulation
