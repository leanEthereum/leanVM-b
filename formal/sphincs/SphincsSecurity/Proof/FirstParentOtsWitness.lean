import SphincsSecurity.Proof.FirstOtsParentRetained
import SphincsSecurity.Proof.OtsProbeNativeParentTerminal

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def retainedAfterSecretsComputation
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) : OracleComp OracleWorld RetainedGameResult := do
  let root ← liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)
  let rest ← simulateQ (expandedAdversaryImpl ⟨parameter, root, otsSecret, ftsSecret⟩)
    (retainedGameRestComputation adversary ⟨root, parameter⟩)
  pure (root, rest)

theorem retainedAfterSecretsComputation_verdict
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (fun result => retainedRestVerdict result.2) <$>
      retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret =
        gameAfterSecrets adversary parameter otsSecret ftsSecret := by
  rw [retainedAfterSecretsComputation, gameAfterSecrets, map_bind]
  apply bind_congr
  intro root
  rw [gameRest_eq_map_retained]
  simp only [bind_pure_comp, Functor.map_map, retainedRestVerdict]

def firstParentRetainedVerdictProjection
    (result : (RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord) :
    (Bool × QueryCache HashSpec) × Option ExceptionRecord :=
  ((retainedRestVerdict result.1.1.2, result.1.2), result.2)

theorem firstParentRetained_verdict_projection
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    firstParentRetainedVerdictProjection <$>
      runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
        (retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ none =
      runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ none := by
  rw [← retainedAfterSecretsComputation_verdict, runFirstException_map]
  rfl

theorem relTriple_firstParentRetained_prehit
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
    RelTriple (runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
      (retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ none)
      (prehitRetainedQueryTrace adversary parameter table ftsSecret)
      (fun left right => left.1 = (right.1.1, right.1.2.1.cache) ∧
        (FirstOtsParentRecord parameter left → EarlyOtsParentAtQuery parameter otsSecret ftsSecret right)) := by
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
  rw [retainedAfterSecretsComputation, runFirstException_bind]
  unfold prehitRetainedQueryTrace
  apply relTriple_bind hsupported
  rintro ⟨⟨root, cache⟩, saved⟩ ⟨⟨actualRoot, actualCache⟩, hit⟩ hroot
  have heq : root = actualRoot ∧ cache = actualCache := Prod.mk.inj hroot.1
  rcases heq with ⟨rfl, rfl⟩
  have hsaved : saved = none := hroot.2
  subst saved
  dsimp only
  rw [bind_pure_comp, runFirstException_map]
  let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  have htail := relTriple_firstException_prehitQueryTrace exception accountingKey secretKey
    (retainedGameRestComputation adversary ⟨root, parameter⟩)
    (⟨cache, ⟨[], [], []⟩, [], none⟩, hit) none
  have hmap := relTriple_map
    (f := fun left : (RetainedRestResult × QueryCache HashSpec) × Option ExceptionRecord =>
      (((root, left.1.1), left.1.2), left.2))
    (g := fun right : (RetainedRestResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot =>
      (((root, right.1.1), right.1.2), right.2))
    (R := fun left right => left.1 = (right.1.1, right.1.2.1.cache) ∧
      (FirstOtsParentRecord parameter left → EarlyOtsParentAtQuery parameter otsSecret ftsSecret right))
    (relTriple_post_mono htail (fun _ _ hrel =>
      ⟨Prod.ext (congrArg (root, ·) hrel.1) hrel.2.1,
        fun hrecord => hrel.early_parent_of_ots_record (fun _ _ _ h => h.2) hrecord⟩))
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using hmap


def FirstParentOrOtsWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord) : Prop :=
  FirstOtsParentRecord parameter result ∨
    WinningRetainedVerifyProbeAfterOtsSecret parameter otsSecret ftsSecret result.1

theorem probEvent_firstParentOrOtsWitness_le_nativeTerminalFailure
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
    Pr[FirstParentOrOtsWitness parameter otsSecret ftsSecret |
      runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
        (retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ none] ≤
      Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot Finset.univ adversary parameter table ftsSecret fuel] := by
  dsimp only
  have hbound := probEvent_parentOrRetainedOtsWitness_le_nativeTerminalFailure adversary parameter table ftsSecret fuel
  have heq := (evalDist_nativeTerminalFailureAfterRoot_eq_chronological ∅ adversary parameter table ftsSecret fuel).trans
    (evalDist_nativeTerminalFailureAfterRoot_eq_chronological Finset.univ adversary parameter table ftsSecret fuel).symm
  rw [_root_.OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) heq] at hbound
  apply le_trans _ hbound
  apply probEvent_le_of_relTriple (relTriple_firstParentRetained_prehit adversary parameter table ftsSecret)
  intro left right hrel hwitness
  rcases hwitness with hparent | hwitness
  · exact Or.inl (hrel.2 hparent)
  · apply Or.inr
    rw [WinningRetainedVerifyProbeAfterOtsSecret, hrel.1] at hwitness
    exact (winningRetainedVerifyProbe_congr_tableOtsSecret parameter ftsSecret _ _
      (by rw [tableOtsSecret_tableOfOtsSecret, tableOtsSecret_extendStartTable]; rfl) _).mp hwitness

end SphincsSecurity.Concrete.OtsProbeSimulation
