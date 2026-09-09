import SphincsSecurity.Proof.PublicSigningRecord

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec AdaptiveHiddenLabels
set_option backward.isDefEq.respectTransparency false

variable {AuxIndex Memory : Type} {auxSpec : OracleSpec AuxIndex}

def nativeDisclosure (coordinate : CanonicalCoordinate) : OracleComp (World auxSpec CanonicalCoordinate) Digest :=
  liftM ((World auxSpec CanonicalCoordinate).query (.inr (.inr coordinate)))

def disclosureSequenceState (environment : Environment auxSpec CanonicalCoordinate Memory)
    (labels : CanonicalCoordinate → Digest) {n : Nat} (coordinates : Fin n → CanonicalCoordinate)
    (state : ObservationState CanonicalCoordinate Memory) : ObservationState CanonicalCoordinate Memory :=
  (List.ofFn coordinates).foldl (fun state coordinate => disclosedState environment state coordinate (labels coordinate)) state

theorem observedRun_disclosureSequence_bind {Result : Type}
    (environment : Environment auxSpec CanonicalCoordinate Memory) (labels : CanonicalCoordinate → Digest)
    {n : Nat} (coordinates : Fin n → CanonicalCoordinate)
    (next : (Fin n → Digest) → OracleComp (World auxSpec CanonicalCoordinate) Result)
    (state : ObservationState CanonicalCoordinate Memory) :
    observedRun environment labels ((sequenceFin fun index => nativeDisclosure (coordinates index)) >>= next) state =
      observedRun environment labels (next (fun index => labels (coordinates index)))
        (disclosureSequenceState environment labels coordinates state) := by
  induction n generalizing state with
  | zero =>
      have hvalues : (Fin.elim0 : Fin 0 → Digest) = (fun index => labels (coordinates index)) := by
        funext index
        exact Fin.elim0 index
      simp only [sequenceFin, pure_bind, hvalues, disclosureSequenceState, List.ofFn_zero, List.foldl_nil]
  | succ n ih =>
      rw [sequenceFin, bind_assoc]
      change runWith (observedImpl environment labels)
        (liftM ((World auxSpec CanonicalCoordinate).query (.inr (.inr (coordinates 0)))) >>= _) state = _
      rw [runWith_query_bind]
      simp only [observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, bind_assoc]
      change observedRun environment labels
        ((sequenceFin fun index => nativeDisclosure (coordinates index.succ)) >>=
          fun tail => next (Fin.cons (labels (coordinates 0)) tail))
        (disclosedState environment state (coordinates 0) (labels (coordinates 0))) = _
      rw [ih]
      have hvalues : Fin.cons (labels (coordinates 0)) (fun index => labels (coordinates index.succ)) =
          (fun index => labels (coordinates index)) := by
        funext index
        cases index using Fin.cases <;> rfl
      rw [hvalues]
      simp only [disclosureSequenceState, List.ofFn_succ, List.foldl_cons]

def nativeCompleteSigningRecord (record : PublicSigningRecord) :
    OracleComp (World auxSpec CanonicalCoordinate) ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) :=
  match record.1.1, record.1.2 with
  | some plan, some view => do
      let secrets ← sequenceFin fun tree => nativeDisclosure (.ftsStart view.1 tree (view.2 tree))
      pure ((some (plan.finish secrets), some view), record.2)
  | _, _ => pure ((none, record.1.2), record.2)

def completedSigningState (environment : Environment auxSpec CanonicalCoordinate Memory)
    (labels : CanonicalCoordinate → Digest) (record : PublicSigningRecord)
    (state : ObservationState CanonicalCoordinate Memory) : ObservationState CanonicalCoordinate Memory :=
  match record.1.1, record.1.2 with
  | some _, some view => disclosureSequenceState environment labels (fun tree => .ftsStart view.1 tree (view.2 tree)) state
  | _, _ => state

theorem observedRun_nativeCompleteSigningRecord
    (environment : Environment auxSpec CanonicalCoordinate Memory) (labels : CanonicalCoordinate → Digest)
    (record : PublicSigningRecord) (state : ObservationState CanonicalCoordinate Memory) :
    observedRun environment labels (nativeCompleteSigningRecord record) state =
      pure (some (completePublicSigningRecord (fun index tree leaf => labels (.ftsStart index tree leaf)) record),
        completedSigningState environment labels record state) := by
  obtain ⟨⟨plan, view⟩, trace⟩ := record
  cases plan <;> cases view <;> simp only [nativeCompleteSigningRecord, completePublicSigningRecord, completedSigningState,
    Option.map_none, Option.map_some]
  all_goals first
    | exact runWith_pure (observedImpl environment labels) _ _
    | rw [observedRun_disclosureSequence_bind]; exact runWith_pure (observedImpl environment labels) _ _

theorem nativeCompleteSigningRecord_failed (record : PublicSigningRecord) (hfailed : record.1.1 = none) :
    nativeCompleteSigningRecord (auxSpec := auxSpec) record = pure ((none, record.1.2), record.2) := by
  rw [nativeCompleteSigningRecord, hfailed]

end SphincsSecurity.Concrete
