import SphincsSecurity.Proof.SettledCollisionViewedProjection
import SphincsSecurity.Proof.VerifierPrimitiveTerminal

namespace SphincsSecurity.Concrete.SettledCollision

open OracleComp OracleSpec ENNReal

abbrev ViewedResult := (Digest × Forgery × Bool) × (ViewedFullTraceState × History)

def eraseHistory (result : ViewedResult) : (Digest × Forgery × Bool) × ViewedFullTraceState :=
  (result.1, result.2.1)

def UnsettledVerifierCollision (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (result : ViewedResult) : Prop :=
  result.1.2.2 = true ∧
    evalWithAnswerFn (fromCache result.2.1.cache)
      (verify ⟨result.1.1, parameter⟩ result.1.2.1.message result.1.2.1.signature) = true ∧
    CachedRun result.2.1.cache (fromCache result.2.1.cache)
      (verify ⟨result.1.1, parameter⟩ result.1.2.1.message result.1.2.1.signature) ∧
    BadOnInputs ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ result.2.1.cache
      ({input | input ∈ queriedInputs (fromCache result.2.1.cache)
        (verify ⟨result.1.1, parameter⟩ result.1.2.1.message result.1.2.1.signature)} ∩
        ↑result.2.2.unsettled)

theorem UnsettledVerifierCollision.structuralCollision {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest} {result : ViewedResult}
    (hevent : UnsettledVerifierCollision parameter otsSecret ftsSecret result) :
    ViewedVerifierStructuralCollision parameter otsSecret ftsSecret (eraseHistory result) := by
  rw [viewedVerifierStructuralCollision_iff_fromCache]
  obtain ⟨hwin, heval, hrun, hbad⟩ := hevent
  exact ⟨hwin, heval, hrun, hbad.mono_inputs Set.inter_subset_left⟩

theorem historyInvariant_gameAfterSecretsWithView (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (result : ViewedResult)
    (hresult : result ∈ support (gameAfterSecretsWithView adversary parameter otsSecret ftsSecret)) :
    HistoryInvariant (primitiveAccountingKey parameter otsSecret ftsSecret) result.2.1.cache result.2.2 := by
  have hproject : ((result.1.2.2, result.2.1.cache), result.2.2) ∈ support
      (runMonitor (primitiveAccountingKey parameter otsSecret ftsSecret)
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ initialHistory) := by
    rw [← gameAfterSecretsWithView_monitor_projection, support_map]
    exact ⟨result, hresult, rfl⟩
  exact historyInvariant_runMonitor _ _ ∅ initialHistory (historyInvariant_initial _) _ hproject

theorem structuralCollision_implies_hit_or_unsettled (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (result : ViewedResult)
    (hresult : result ∈ support (gameAfterSecretsWithView adversary parameter otsSecret ftsSecret))
    (hcollision : ViewedVerifierStructuralCollision parameter otsSecret ftsSecret (eraseHistory result)) :
    result.2.2.hit = true ∨ UnsettledVerifierCollision parameter otsSecret ftsSecret result := by
  rw [viewedVerifierStructuralCollision_iff_fromCache] at hcollision
  obtain ⟨hwin, heval, hrun, hbad⟩ := hcollision
  have hinvariant : HistoryInvariant ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.1.cache result.2.2 :=
    historyInvariant_gameAfterSecretsWithView adversary parameter otsSecret ftsSecret result hresult
  rcases badOnInputs_implies_hit_or_unsettled hinvariant hbad with hhit | hunsettled
  · exact Or.inl hhit
  · exact Or.inr ⟨hwin, heval, hrun, hunsettled⟩

def remainingPrimitiveEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (result : ViewedResult) : Prop :=
  result.2.2.hit = false ∧ result.1.2.2 = true ∧
    (UnsettledVerifierCollision parameter otsSecret ftsSecret result ∨
      ViewedEncodingCollisionWitness parameter otsSecret ftsSecret (eraseHistory result) ∨
      ViewedWinningFreshLayerOpeningWitness parameter otsSecret ftsSecret (eraseHistory result) ∨
      ViewedWinningBackwardChainOpeningWitness parameter otsSecret ftsSecret (eraseHistory result) ∨
      ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret (eraseHistory result))

theorem remainingPrimitiveEvent_implies_verifierPrimitiveEvent
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (result : ViewedResult)
    (hevent : remainingPrimitiveEvent parameter otsSecret ftsSecret result) :
    verifierPrimitiveEvent parameter otsSecret ftsSecret (eraseHistory result) := by
  obtain ⟨_, hwin, hcollision | hrest⟩ := hevent
  · exact ⟨hwin, Or.inl hcollision.structuralCollision⟩
  · exact ⟨hwin, Or.inr hrest⟩

theorem verifierPrimitiveEvent_implies_hit_or_remaining (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (result : ViewedResult)
    (hresult : result ∈ support (gameAfterSecretsWithView adversary parameter otsSecret ftsSecret))
    (hevent : verifierPrimitiveEvent parameter otsSecret ftsSecret (eraseHistory result)) :
    result.2.2.hit = true ∨ remainingPrimitiveEvent parameter otsSecret ftsSecret result := by
  by_cases hhit : result.2.2.hit = true
  · exact Or.inl hhit
  have hfalse := Bool.eq_false_iff.mpr hhit
  obtain ⟨hwin, hcollision | hrest⟩ := hevent
  · rcases structuralCollision_implies_hit_or_unsettled adversary parameter otsSecret ftsSecret
      result hresult hcollision with hhit | hunsettled
    · exact Or.inl hhit
    · exact Or.inr ⟨hfalse, hwin, Or.inl hunsettled⟩
  · exact Or.inr ⟨hfalse, hwin, Or.inr hrest⟩

theorem probEvent_verifierPrimitive_le_hit_add_remaining (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[verifierPrimitiveEvent parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
    Pr[fun result => result.2.2.hit = true | gameAfterSecretsWithView adversary parameter otsSecret ftsSecret] +
      Pr[remainingPrimitiveEvent parameter otsSecret ftsSecret |
        gameAfterSecretsWithView adversary parameter otsSecret ftsSecret] := by
  rw [← gameAfterSecretsWithView_projection, probEvent_map]
  apply le_trans _ (probEvent_or_le _ _ _)
  apply probEvent_mono
  intro result hresult hevent
  exact verifierPrimitiveEvent_implies_hit_or_remaining adversary parameter otsSecret ftsSecret result hresult hevent

end SphincsSecurity.Concrete.SettledCollision
