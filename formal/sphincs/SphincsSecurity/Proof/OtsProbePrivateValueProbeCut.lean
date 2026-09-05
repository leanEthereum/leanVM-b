import SphincsSecurity.Proof.OtsProbePrivateValueHistoryRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def IsPrivatePositionDisclosure (target : Position) : LazyRevealProbe.Query Coordinate → Prop
  | .reveal coordinate | .publish coordinate => coordinate = .position target
  | _ => False

def IsPrivatePositionProbe (target : Position) : LazyRevealProbe.Query Coordinate → Prop
  | .probe coordinate _ => coordinate = .position target
  | _ => False

noncomputable def privatePositionProbeCutAt
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    Nat → OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α) :=
  OracleComp.construct (fun value _ => pure (.done value))
    (fun input next recursivelyCut ordinal =>
      if IsPrivatePositionDisclosure target input then pure (.query input next)
      else if IsPrivatePositionProbe target input then
        match ordinal with
        | 0 => pure (.query input next)
        | ordinal + 1 => (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
            fun output => recursivelyCut output ordinal
      else (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
        fun output => recursivelyCut output ordinal) computation

theorem privatePositionProbeCutAt_query_bind
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α) (ordinal : Nat) :
    privatePositionProbeCutAt target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) ordinal =
      (if IsPrivatePositionDisclosure target input then pure (.query input next)
      else if IsPrivatePositionProbe target input then
        match ordinal with
        | 0 => pure (.query input next)
        | ordinal + 1 => (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
            fun output => privatePositionProbeCutAt target (next output) ordinal
      else (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
        fun output => privatePositionProbeCutAt target (next output) ordinal) := rfl

theorem privatePositionProbeCutAt_resume
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (ordinal : Nat) :
    privatePositionProbeCutAt target computation ordinal >>= PrivateValueCut.resume = computation := by
  induction computation using OracleComp.inductionOn generalizing ordinal with
  | pure value => rfl
  | query_bind input next ih =>
      rw [privatePositionProbeCutAt_query_bind]
      split_ifs
      · rfl
      · cases ordinal with
        | zero => rfl
        | succ ordinal =>
            rw [bind_assoc]
            exact bind_congr fun output => ih output ordinal
      · rw [bind_assoc]
        exact bind_congr fun output => ih output ordinal

theorem privatePositionProbeCutAt_no_disclosure
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (ordinal : Nat) :
    (privatePositionProbeCutAt target computation ordinal).IsQueryBoundP (IsPrivatePositionDisclosure target) 0 := by
  induction computation using OracleComp.inductionOn generalizing ordinal with
  | pure value => simp [privatePositionProbeCutAt]
  | query_bind input next ih =>
      rw [privatePositionProbeCutAt_query_bind]
      split_ifs with hdisclose hprobe
      · simp
      · cases ordinal with
        | zero => simp
        | succ ordinal =>
            rw [OracleComp.isQueryBoundP_query_bind_iff]
            exact ⟨Or.inl hdisclose, fun output => by simpa only [if_neg hdisclose] using ih output ordinal⟩
      · rw [OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl hdisclose, fun output => by simpa only [if_neg hdisclose] using ih output ordinal⟩

theorem privatePositionProbeCutAt_probe_bound
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (ordinal : Nat) :
    (privatePositionProbeCutAt target computation ordinal).IsQueryBoundP (IsPrivatePositionProbe target) ordinal := by
  induction computation using OracleComp.inductionOn generalizing ordinal with
  | pure value => simp [privatePositionProbeCutAt]
  | query_bind input next ih =>
      rw [privatePositionProbeCutAt_query_bind]
      split_ifs with hdisclose hprobe
      · simp
      · cases ordinal with
        | zero => simp
        | succ ordinal =>
            rw [OracleComp.isQueryBoundP_query_bind_iff]
            exact ⟨Or.inr (by omega), fun output => by simpa only [if_pos hprobe, Nat.add_sub_cancel] using ih output ordinal⟩
      · rw [OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl hprobe, fun output => by simpa only [if_neg hprobe] using ih output ordinal⟩

theorem privatePositionProbeCutAt_zero
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    privatePositionProbeCutAt target computation 0 = privatePositionAccessCut target computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [privatePositionProbeCutAt_query_bind, privatePositionAccessCut_query_bind]
      have haccess : IsPrivatePositionAccess target input ↔
          IsPrivatePositionDisclosure target input ∨ IsPrivatePositionProbe target input := by
        cases input <;> simp [IsPrivatePositionAccess, IsPrivatePositionDisclosure, IsPrivatePositionProbe]
      rw [propext haccess]
      by_cases hdisclose : IsPrivatePositionDisclosure target input
      · simp [hdisclose]
      · by_cases hprobe : IsPrivatePositionProbe target input
        · simp [hdisclose, hprobe]
        · simp only [if_neg hdisclose, if_neg hprobe, if_neg (not_or.mpr ⟨hdisclose, hprobe⟩)]
          exact bind_congr ih

end SphincsSecurity.Concrete.OtsProbeSimulation
