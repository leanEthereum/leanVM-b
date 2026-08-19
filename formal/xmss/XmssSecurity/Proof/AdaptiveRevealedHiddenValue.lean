import XmssSecurity.Proof.IndexedHiddenValue
import Mathlib.Data.List.GetD

namespace XmssSecurity.IndexedHiddenValue

variable {Index : Type} [Fintype Index] [DecidableEq Index]

def installReveals (table : Index → Digest) :
    List (Index × Digest) → Index → Digest
  | [] => table
  | reveal :: reveals =>
      Function.update (installReveals table reveals) reveal.1 reveal.2

omit [Fintype Index] in
@[simp]
theorem installReveals_nil (table : Index → Digest) :
    installReveals table [] = table := rfl

omit [Fintype Index] in
theorem installReveals_cons (table : Index → Digest)
    (reveal : Index × Digest) (reveals : List (Index × Digest)) :
    installReveals table (reveal :: reveals) =
      Function.update (installReveals table reveals) reveal.1 reveal.2 := rfl

omit [Fintype Index] in
theorem installReveals_eq_self_of_values
    (table : Index → Digest) (reveals : List (Index × Digest))
    (hvalues : ∀ reveal ∈ reveals, table reveal.1 = reveal.2) :
    installReveals table reveals = table := by
  induction reveals with
  | nil => rfl
  | cons reveal reveals ih =>
      rw [installReveals_cons, ih (fun candidate hcandidate =>
        hvalues candidate (by simp [hcandidate]))]
      funext index
      by_cases heq : index = reveal.1
      · subst index
        simp [hvalues reveal (by simp)]
      · simp [Function.update_of_ne heq]

def AvoidsReveals
    (reveals : List (Index × Digest))
    (strategy : List Bool → Index × Digest) : Prop :=
  ∀ history, (strategy history).1 ∉ reveals.map Prod.fst

def listStrategy (default : Index × Digest)
    (probes : List (Index × Digest)) : List Bool → Index × Digest :=
  fun history => probes.getD history.length default

omit [Fintype Index] [DecidableEq Index] in
theorem listStrategy_mem
    (default : Index × Digest) (probes : List (Index × Digest))
    (hdefault : default ∈ probes) (history : List Bool) :
    listStrategy default probes history ∈ probes := by
  unfold listStrategy
  by_cases hlength : history.length < probes.length
  · rw [List.getD_eq_getElem probes default hlength]
    exact List.getElem_mem _
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hlength)]
    exact hdefault

omit [Fintype Index] [DecidableEq Index] in
theorem listStrategy_avoids
    (reveals probes : List (Index × Digest))
    (default : Index × Digest) (hdefault : default ∈ probes)
    (hprobes : ∀ probe ∈ probes, probe.1 ∉ reveals.map Prod.fst) :
    AvoidsReveals reveals (listStrategy default probes) := by
  intro history
  exact hprobes _ (listStrategy_mem default probes hdefault history)

omit [Fintype Index] [DecidableEq Index] in
theorem readMany_listStrategy_eq_true_of_mem
    (table : Index → Digest) (queries : Nat)
    (probes : List (Index × Digest)) (default probe : Index × Digest)
    (hqueries : probes.length ≤ queries) (hprobe : probe ∈ probes)
    (hhit : table probe.1 = probe.2) :
    readMany table queries (listStrategy default probes) = true := by
  rw [readMany_true_iff]
  obtain ⟨round, hround, hget⟩ := List.mem_iff_getElem.mp hprobe
  refine ⟨round, hround.trans_le hqueries, ?_⟩
  unfold listStrategy
  simp only [List.length_replicate]
  rw [List.getD_eq_getElem probes default hround, hget]
  exact hhit

end XmssSecurity.IndexedHiddenValue
