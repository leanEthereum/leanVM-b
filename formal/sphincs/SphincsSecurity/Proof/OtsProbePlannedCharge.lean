import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FtsProbeSimulation
import SphincsSecurity.Proof.LazyRevealProbeCharge
import SphincsSecurity.Proof.OtsProbeSimulation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

def unmaterializedCandidateCharge (state : LazyRevealProbe.State Coordinate) : Option Probe → Nat
  | none => 0
  | some candidate => if candidate.coordinate ∈ state.revealed then 0
      else LazyRevealProbe.pendingProbeCharge state candidate.coordinate candidate.candidate

def materializedCandidateCharge (state : LazyRevealProbe.State Coordinate) : Option Probe → Nat
  | none => 0
  | some candidate => if candidate.coordinate ∈ state.revealed ∨
      (candidate.coordinate, candidate.candidate) ∈ state.pending then 0
      else if state.values candidate.coordinate ≠ none then 1 else 0

theorem candidateCharge_sum_le_one (state : LazyRevealProbe.State Coordinate) (candidate : Option Probe) :
    unmaterializedCandidateCharge state candidate + materializedCandidateCharge state candidate ≤ 1 := by
  cases candidate with
  | none => exact Nat.zero_le 1
  | some candidate =>
      simp only [unmaterializedCandidateCharge, materializedCandidateCharge, LazyRevealProbe.pendingProbeCharge]
      split_ifs <;> omega

end SphincsSecurity.Concrete.OtsProbeSimulation
