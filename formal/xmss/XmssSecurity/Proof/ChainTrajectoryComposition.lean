import XmssSecurity.Proof.ChainTrajectoryUniformity

namespace XmssSecurity

abbrev FullChainTrajectory := Vector Digest (chainLength - 1 + 1)

noncomputable def allEpochs : List Epoch :=
  Finset.univ.toList

theorem allEpochs_nodup : allEpochs.Nodup := by
  exact Finset.nodup_toList Finset.univ

theorem mem_allEpochs (epoch : Epoch) : epoch ∈ allEpochs := by
  simp [allEpochs]

theorem allEpochs_length : allEpochs.length = lifetime := by
  simp [allEpochs, Epoch]

attribute [irreducible] allEpochs

end XmssSecurity
