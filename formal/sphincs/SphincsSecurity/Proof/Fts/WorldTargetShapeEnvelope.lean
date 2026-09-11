import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ConcreteTargetShapeQuery
import SphincsSecurity.Proof.Fts.InterleavedCoverStep

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def observedTargetShapeVector (key : SecretKey) (payload : HashInput) (target : FewTimeView) (state : CoverLogState) : TargetShapeVector :=
  targetShapeMoments key state.1 state.2 payload target

theorem expected_fresh_targetShape_le (key : SecretKey) (payload : HashInput) (target : FewTimeView)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      observedTargetShapeVector key payload target (before.cacheQuery input output, log) groups remaining) ≤
        targetShapeQuery (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          (observedTargetShapeVector key payload target (before, log)) groups remaining := by
  have h := expected_randomOracle_targetShapeMoments_le key before log payload target groups remaining hvalid input hsigned
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul] at h
  exact h

end SphincsSecurity.Concrete
