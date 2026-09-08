import SphincsSecurity.Proof.JointProbeOriginalFailureMonitor
import SphincsSecurity.Proof.WorldPairReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

theorem runWithFailure_original_cache_projection
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    (fun result => result.1.2.1) <$> runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed =
      evalDist ((simulateQ romImpl (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation)).run cache) := by
  calc
    _ = Prod.fst <$> (Prod.snd <$> (Prod.fst <$> runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed)) := by
      simp only [Functor.map_map]
    _ = _ := by
      rw [runWithFailure_project, run_original, ← evalDist_map, runExceptionMonitor_project]

theorem runWithFailure_support_nonempty
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    (support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed)).Nonempty := by
  obtain ⟨actual, ha⟩ := simulateQ_romImpl_support_nonempty
    (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation) cache
  have hm : actual ∈ support (evalDist ((simulateQ romImpl
      (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation)).run cache)) :=
    (SPMF.mem_support_iff _ _).2 ((mem_support_iff_evalDist_apply_ne_zero _ _).1 ha)
  rw [← runWithFailure_original_cache_projection exception parameter root otsTable ftsTable computation frame cache hit failed, support_map] at hm
  obtain ⟨result, hr, _⟩ := hm
  exact ⟨result, hr⟩

theorem runWithFailure_cache_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (result) (hr : result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed)) :
    cache ≤ result.1.2.1.2 := by
  have hm : result.1.2.1 ∈ support ((fun result => result.1.2.1) <$>
      runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed) := by
    rw [support_map]
    exact ⟨result, hr, rfl⟩
  rw [runWithFailure_original_cache_projection] at hm
  exact simulateQ_romImpl_cache_le _ cache result.1.2.1
    ((mem_support_iff_evalDist_apply_ne_zero _ _).2 ((SPMF.mem_support_iff _ _).1 hm))

theorem runWithFailure_initial_cache_cap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (cap : ENNReal) (hcap : ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed),
      QueryCache.enncard result.1.2.1.2 ≤ cap) : QueryCache.enncard cache ≤ cap := by
  obtain ⟨result, hr⟩ := runWithFailure_support_nonempty exception parameter root otsTable ftsTable computation frame cache hit failed
  exact (QueryCache.enncard_mono (runWithFailure_cache_le exception parameter root otsTable ftsTable computation frame cache hit failed result hr)).trans
    (hcap result hr)

theorem runWithFailure_tail_cache_cap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) (cap : ENNReal)
    (hcap : ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable (OracleSpec.query input >>= next) frame cache hit failed),
      QueryCache.enncard result.1.2.1.2 ≤ cap)
    (head) (hh : head ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed)) :
    ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable (next head.1.2.1.1)
      head.1.1 head.1.2.1.2 head.1.2.2 head.2), QueryCache.enncard result.1.2.1.2 ≤ cap := by
  intro result hr
  apply hcap result
  rw [runWithFailure_query_bind, mem_support_bind_iff]
  exact ⟨head, hh, hr⟩

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
