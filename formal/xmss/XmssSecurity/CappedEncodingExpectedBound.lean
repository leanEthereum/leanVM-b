import XmssSecurity.CappedEncodingMonitor
import XmssSecurity.CappedEncodingQueryBound
import XmssSecurity.ExpectedQueryCount

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000

namespace XmssSecurity.CappedEncodingMonitor

noncomputable def expectedEncodingSamplingQueryCount
    (predicate : EncodingSamplingWorld.Domain → Prop) [DecidablePred predicate]
    (computation : OracleComp EncodingSamplingWorld α) : ENNReal :=
  OracleComp.recOn (motive := fun _ => ENNReal) computation
    (fun _ => 0)
    (fun input _ continuationCounts =>
      (if predicate input then 1 else 0) +
        ∑' output, Pr[= output | encodingSamplingWorldImpl input] *
          continuationCounts output)

noncomputable def expectedAttackerEncodingQueries
    (computation : OracleComp EncodingSamplingWorld α) : ENNReal :=
  expectedEncodingSamplingQueryCount IsAttackerEncodingQuery computation

def IsEpochEncodingSample : EncodingSamplingWorld.Domain → Prop
  | .inr ⟨_, some _, _⟩ => True
  | _ => False

noncomputable instance : DecidablePred IsEpochEncodingSample :=
  Classical.decPred _

noncomputable def expectedEpochEncodingSamples
    (computation : OracleComp EncodingSamplingWorld α) : ENNReal :=
  expectedEncodingSamplingQueryCount IsEpochEncodingSample computation

@[simp]
theorem expectedEpochEncodingSamples_pure (value : α) :
    expectedEpochEncodingSamples
      (pure value : OracleComp EncodingSamplingWorld α) = 0 := by
  rfl

@[simp]
theorem expectedAttackerEncodingQueries_pure (value : α) :
    expectedAttackerEncodingQueries
      (pure value : OracleComp EncodingSamplingWorld α) = 0 := by
  rfl

@[simp]
theorem expectedAttackerEncodingQueries_query_bind
    (input : EncodingSamplingWorld.Domain)
    (next : EncodingSamplingWorld.Range input →
      OracleComp EncodingSamplingWorld α) :
    expectedAttackerEncodingQueries
        (liftM (EncodingSamplingWorld.query input) >>= next) =
      (if IsAttackerEncodingQuery input then 1 else 0) +
      ∑' output, Pr[= output | encodingSamplingWorldImpl input] *
          expectedAttackerEncodingQueries (next output) := by
  rfl

theorem expectedAttackerEncodingQueries_sample_query_bind
    (address : EncodingSampleAddress)
    (next : HashOutput → OracleComp EncodingSamplingWorld α) :
    expectedAttackerEncodingQueries
        (liftM (EncodingSamplingWorld.query (.inr address)) >>= next) =
      (if IsAttackerEncodingQuery (.inr address) then 1 else 0) +
        ∑' output : HashOutput, Pr[= output | uniformHashOutput] *
          expectedAttackerEncodingQueries (next output) := by
  rfl

@[simp]
theorem expectedEncodingSamplingQueryCount_pure
    (predicate : EncodingSamplingWorld.Domain → Prop) [DecidablePred predicate]
    (value : α) :
    expectedEncodingSamplingQueryCount predicate
      (pure value : OracleComp EncodingSamplingWorld α) = 0 := by
  rfl

@[simp]
theorem expectedEncodingSamplingQueryCount_query_bind
    (predicate : EncodingSamplingWorld.Domain → Prop) [DecidablePred predicate]
    (input : EncodingSamplingWorld.Domain)
    (next : EncodingSamplingWorld.Range input →
      OracleComp EncodingSamplingWorld α) :
    expectedEncodingSamplingQueryCount predicate
        (liftM (EncodingSamplingWorld.query input) >>= next) =
      (if predicate input then 1 else 0) +
        ∑' output, Pr[= output | encodingSamplingWorldImpl input] *
          expectedEncodingSamplingQueryCount predicate (next output) := by
  rfl

@[simp]
theorem expectedEncodingSamplingQueryCount_query
    (predicate : EncodingSamplingWorld.Domain → Prop) [DecidablePred predicate]
    (input : EncodingSamplingWorld.Domain) :
    expectedEncodingSamplingQueryCount predicate
        (liftM (EncodingSamplingWorld.query input)) =
      if predicate input then 1 else 0 := by
  rw [← bind_pure (liftM (EncodingSamplingWorld.query input) :
    OracleComp EncodingSamplingWorld _)]
  rw [expectedEncodingSamplingQueryCount_query_bind]
  simp

theorem expectedEncodingSamplingQueryCount_bind
    {α β : Type}
    (predicate : EncodingSamplingWorld.Domain → Prop) [DecidablePred predicate]
    (head : OracleComp EncodingSamplingWorld α)
    (continuation : α → OracleComp EncodingSamplingWorld β) :
    expectedEncodingSamplingQueryCount predicate (head >>= continuation) =
      expectedEncodingSamplingQueryCount predicate head +
        ∑' result, Pr[= result | simulateQ encodingSamplingWorldImpl head] *
          expectedEncodingSamplingQueryCount predicate (continuation result) := by
  induction head using OracleComp.inductionOn with
  | pure value =>
      simp [simulateQ_pure, tsum_probOutput_pure_mul]
  | query_bind input next ih =>
      rw [bind_assoc, expectedEncodingSamplingQueryCount_query_bind,
        expectedEncodingSamplingQueryCount_query_bind]
      simp_rw [ih, mul_add]
      rw [ENNReal.tsum_add]
      rw [simulateQ_bind, simulateQ_query, tsum_probOutput_bind_mul]
      simp only [OracleQuery.input_query, OracleQuery.cont_query]
      rw [id_map]
      ac_rfl

theorem expectedEncodingSamplingQueryCount_map
    {α β : Type}
    (predicate : EncodingSamplingWorld.Domain → Prop) [DecidablePred predicate]
    (project : α → β) (computation : OracleComp EncodingSamplingWorld α) :
    expectedEncodingSamplingQueryCount predicate (project <$> computation) =
      expectedEncodingSamplingQueryCount predicate computation := by
  rw [map_eq_bind_pure_comp]
  change expectedEncodingSamplingQueryCount predicate
      (computation >>= fun value => pure (project value)) = _
  calc
    _ = expectedEncodingSamplingQueryCount predicate computation +
        ∑' result, Pr[= result | simulateQ encodingSamplingWorldImpl computation] *
          expectedEncodingSamplingQueryCount predicate (pure (project result)) :=
      expectedEncodingSamplingQueryCount_bind predicate computation
        (fun value => pure (project value))
    _ = _ := by simp

theorem expectedEpochEncodingSamples_map
    {α β : Type}
    (project : α → β)
    (computation : OracleComp EncodingSamplingWorld α) :
    expectedEpochEncodingSamples (project <$> computation) =
      expectedEpochEncodingSamples computation := by
  exact expectedEncodingSamplingQueryCount_map IsEpochEncodingSample
    project computation

theorem expectedEpochEncodingSamples_bind
    {α β : Type}
    (head : OracleComp EncodingSamplingWorld α)
    (continuation : α → OracleComp EncodingSamplingWorld β) :
    expectedEpochEncodingSamples (head >>= continuation) =
      expectedEpochEncodingSamples head +
        ∑' result, Pr[= result | simulateQ encodingSamplingWorldImpl head] *
          expectedEpochEncodingSamples (continuation result) := by
  exact expectedEncodingSamplingQueryCount_bind IsEpochEncodingSample
    head continuation

theorem expectedEncodingSamplingQueryCount_mono
    (left right : EncodingSamplingWorld.Domain → Prop)
    [DecidablePred left] [DecidablePred right]
    (hsubset : ∀ input, left input → right input)
    (computation : OracleComp EncodingSamplingWorld α) :
    expectedEncodingSamplingQueryCount left computation ≤
      expectedEncodingSamplingQueryCount right computation := by
  induction computation using OracleComp.recOn with
  | pure value =>
      change (0 : ENNReal) ≤ 0
      exact le_rfl
  | queryBind input next ih =>
      change (if left input then 1 else 0) +
          ∑' output, Pr[= output | encodingSamplingWorldImpl input] *
            expectedEncodingSamplingQueryCount left (next output) ≤
        (if right input then 1 else 0) +
          ∑' output, Pr[= output | encodingSamplingWorldImpl input] *
            expectedEncodingSamplingQueryCount right (next output)
      apply add_le_add
      · by_cases hleft : left input
        · simp [hleft, hsubset input hleft]
        · simp [hleft]
      · apply ENNReal.tsum_le_tsum
        intro output
        gcongr
        exact ih output

theorem expectedAttackerEncodingQueries_le_epochSamples
    (computation : OracleComp EncodingSamplingWorld α) :
    expectedAttackerEncodingQueries computation ≤
      expectedEpochEncodingSamples computation := by
  apply expectedEncodingSamplingQueryCount_mono
  intro input hinput
  cases input with
  | inl index => simp [IsAttackerEncodingQuery] at hinput
  | inr address =>
      rcases address with ⟨kind, epoch, input⟩
      cases kind <;> cases epoch <;>
        simp [IsAttackerEncodingQuery, IsEpochEncodingSample] at hinput ⊢

def IsEncodingHashQuery (parameter : PublicParameter) :
    OracleWorld.Domain → Prop
  | .inr input => (encodingInputEpoch? parameter input).isSome
  | _ => False

noncomputable instance (parameter : PublicParameter) :
    DecidablePred (IsEncodingHashQuery parameter) :=
  Classical.decPred _

theorem expectedEpochEncodingSamples_splitUniformOracle
    (index : unifSpec.Domain) (cache : QueryCache HashSpec) :
    expectedEpochEncodingSamples ((splitUniformOracle index).run cache) = 0 := by
  rw [splitUniformOracle, QueryImpl.liftTarget_apply, StateT.run_monadLift,
    show (do
      let result ← monadLift (encodingUniformQuery index)
      pure (result, cache)) =
        (fun result => (result, cache)) <$> encodingUniformQuery index by rfl,
    expectedEpochEncodingSamples_map]
  unfold encodingUniformQuery expectedEpochEncodingSamples
  rw [OracleComp.liftComp_query]
  rw [expectedEncodingSamplingQueryCount_map]
  change expectedEncodingSamplingQueryCount IsEpochEncodingSample
    (liftM (EncodingSamplingWorld.query (.inl index))) = 0
  rw [expectedEncodingSamplingQueryCount_query]
  simp [IsEpochEncodingSample]

theorem expectedEpochEncodingSamples_splitRandomOracle_le
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (input : HashInput) (cache : QueryCache HashSpec) :
    expectedEpochEncodingSamples
        ((splitRandomOracle parameter kind input).run cache) ≤
      if IsEncodingHashQuery parameter (.inr input) then 1 else 0 := by
  unfold splitRandomOracle
  cases hcache : cache input with
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hcache]
      simp [expectedEpochEncodingSamples]
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcache]
      rw [show (fun output => (output, cache.cacheQuery input output)) <$>
          freshEncodingSampleImpl parameter kind input =
        (fun output => (output, cache.cacheQuery input output)) <$>
          freshEncodingSampleImpl parameter kind input by rfl]
      rw [expectedEpochEncodingSamples_map]
      unfold freshEncodingSampleImpl encodingSampleAddress
      cases hepoch : encodingInputEpoch? parameter input with
      | none =>
          simp only [encodingSampleAddressFromEpoch]
          unfold encodingSampleQuery expectedEpochEncodingSamples
          rw [OracleComp.liftComp_query]
          rw [expectedEncodingSamplingQueryCount_map]
          change expectedEncodingSamplingQueryCount IsEpochEncodingSample
            (liftM (EncodingSamplingWorld.query (.inr
              ⟨EncodingSampleKind.side, none, input⟩))) ≤ _
          rw [expectedEncodingSamplingQueryCount_query]
          simp [IsEpochEncodingSample, IsEncodingHashQuery, hepoch]

      | some epoch =>
          simp only [encodingSampleAddressFromEpoch]
          unfold encodingSampleQuery expectedEpochEncodingSamples
          rw [OracleComp.liftComp_query]
          rw [expectedEncodingSamplingQueryCount_map]
          change expectedEncodingSamplingQueryCount IsEpochEncodingSample
            (liftM (EncodingSamplingWorld.query (.inr ⟨kind, some epoch, input⟩))) ≤ _
          rw [expectedEncodingSamplingQueryCount_query]
          simp [IsEpochEncodingSample, IsEncodingHashQuery, hepoch]

theorem expectedEpochEncodingSamples_splitXmssRom_step_le
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    expectedEpochEncodingSamples
        ((splitXmssRomImpl parameter kind input).run cache) ≤
      if IsEncodingHashQuery parameter input then 1 else 0 := by
  cases input with
  | inl index =>
      simp only [splitXmssRomImpl, QueryImpl.add_apply_inl,
        IsEncodingHashQuery, if_false]
      exact (expectedEpochEncodingSamples_splitUniformOracle index cache).le
  | inr hashInput =>
      simp only [splitXmssRomImpl, QueryImpl.add_apply_inr]
      exact expectedEpochEncodingSamples_splitRandomOracle_le
        parameter kind hashInput cache

theorem expectedEpochEncodingSamples_simulate_splitXmssRom_le
    (parameter : PublicParameter) (kind : EncodingSampleKind)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedEpochEncodingSamples
        ((simulateQ (splitXmssRomImpl parameter kind) computation).run cache) ≤
      expectedSimulatedQueryCount xmssRomImpl
        (IsEncodingHashQuery parameter) computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [expectedEpochEncodingSamples]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind,
        expectedEpochEncodingSamples_bind,
        expectedSimulatedQueryCount_query_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      let splitStep := (splitXmssRomImpl parameter kind input).run cache
      let sourceStep := (xmssRomImpl input).run cache
      have hstep : expectedEpochEncodingSamples splitStep ≤
          if IsEncodingHashQuery parameter input then 1 else 0 := by
        exact expectedEpochEncodingSamples_splitXmssRom_step_le
          parameter kind input cache
      have hdist : evalDist (simulateQ encodingSamplingWorldImpl splitStep) =
          evalDist sourceStep := by
        cases input with
        | inl index =>
            exact congrArg evalDist (splitUniformOracle_bridge index cache)
        | inr hashInput =>
            exact congrArg evalDist
              (splitRandomOracle_bridge parameter kind hashInput cache)
      calc
        expectedEpochEncodingSamples splitStep +
            ∑' result, Pr[= result |
                simulateQ encodingSamplingWorldImpl splitStep] *
              expectedEpochEncodingSamples
                ((simulateQ (splitXmssRomImpl parameter kind)
                  (next result.1)).run result.2) ≤
          (if IsEncodingHashQuery parameter input then 1 else 0) +
            ∑' result, Pr[= result |
                simulateQ encodingSamplingWorldImpl splitStep] *
              expectedSimulatedQueryCount xmssRomImpl
                (IsEncodingHashQuery parameter) (next result.1) result.2 := by
          apply add_le_add hstep
          apply ENNReal.tsum_le_tsum
          intro result
          gcongr
          exact ih result.1 result.2
        _ = (if IsEncodingHashQuery parameter input then 1 else 0) +
            ∑' result, Pr[= result | sourceStep] *
              expectedSimulatedQueryCount xmssRomImpl
                (IsEncodingHashQuery parameter) (next result.1) result.2 := by
          congr 1
          apply tsum_congr
          intro result
          rw [OracleComp.probOutput_congr rfl hdist]

theorem expectedEpochEncodingSamples_cappedSplitUnlogged_step_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec) :
    expectedEpochEncodingSamples
        ((cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey input).run cache) ≤
      expectedSimulatedQueryCount xmssRomImpl
        (IsEncodingHashQuery secretKey.parameter)
        (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey input) cache := by
  cases input with
  | inl worldInput =>
      simpa [cappedSplitUnloggedMappedAdversaryImpl,
        cappedSourceUnloggedMappedAdversaryImpl] using
        (expectedEpochEncodingSamples_simulate_splitXmssRom_le
          secretKey.parameter .query
          (liftM (OracleWorld.query worldInput)) cache)
  | inr request =>
      simpa [cappedSplitUnloggedMappedAdversaryImpl,
        cappedSourceUnloggedMappedAdversaryImpl] using
        (expectedEpochEncodingSamples_simulate_splitXmssRom_le
          secretKey.parameter .sign
          (Concrete.scheme.sign publicKey secretKey request.epoch request.message)
          cache)

theorem expectedEpochEncodingSamples_simulate_cappedSplitUnloggedMapped_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    expectedEpochEncodingSamples
        ((simulateQ (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
          computation).run cache) ≤
      expectedSimulatedQueryCount xmssRomImpl
        (IsEncodingHashQuery secretKey.parameter)
        (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
          computation) cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [expectedEpochEncodingSamples]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind,
        expectedEpochEncodingSamples_bind, simulateQ_query_bind,
        expectedSimulatedQueryCount_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      let splitStep :=
        (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey input).run cache
      let sourceStep :=
        cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey input
      have hstep : expectedEpochEncodingSamples splitStep ≤
          expectedSimulatedQueryCount xmssRomImpl
            (IsEncodingHashQuery secretKey.parameter) sourceStep cache := by
        exact expectedEpochEncodingSamples_cappedSplitUnlogged_step_le
          publicKey secretKey input cache
      have hdist : evalDist (simulateQ encodingSamplingWorldImpl splitStep) =
          evalDist ((simulateQ xmssRomImpl sourceStep).run cache) :=
        by
          have hsource : (simulateQ xmssRomImpl sourceStep).run cache =
              (cappedUnloggedMappedAdversaryImpl publicKey secretKey input).run
                cache := by
            unfold sourceStep
            cases input <;>
              simp [cappedSourceUnloggedMappedAdversaryImpl,
                cappedUnloggedMappedAdversaryImpl, simulateQ_query]
          rw [hsource]
          exact cappedSplitUnloggedMappedAdversaryImpl_query_bridge
            publicKey secretKey input cache
      calc
        expectedEpochEncodingSamples splitStep +
            ∑' result, Pr[= result |
                simulateQ encodingSamplingWorldImpl splitStep] *
              expectedEpochEncodingSamples
                ((simulateQ
                  (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
                  (next result.1)).run result.2) ≤
          expectedSimulatedQueryCount xmssRomImpl
              (IsEncodingHashQuery secretKey.parameter) sourceStep cache +
            ∑' result, Pr[= result |
                simulateQ encodingSamplingWorldImpl splitStep] *
              expectedSimulatedQueryCount xmssRomImpl
                (IsEncodingHashQuery secretKey.parameter)
                (simulateQ
                  (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
                  (next result.1)) result.2 := by
          apply add_le_add hstep
          apply ENNReal.tsum_le_tsum
          intro result
          gcongr
          exact ih result.1 result.2
        _ = expectedSimulatedQueryCount xmssRomImpl
              (IsEncodingHashQuery secretKey.parameter) sourceStep cache +
            ∑' result, Pr[= result |
                (simulateQ xmssRomImpl sourceStep).run cache] *
              expectedSimulatedQueryCount xmssRomImpl
                (IsEncodingHashQuery secretKey.parameter)
                (simulateQ
                  (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
                  (next result.1)) result.2 := by
          congr 1
          apply tsum_congr
          intro result
          rw [OracleComp.probOutput_congr rfl hdist]

theorem cappedUnloggedMappedAdversaryImpl_eq_source_compose
    (publicKey : PublicKey) (secretKey : SecretKey) :
    cappedUnloggedMappedAdversaryImpl publicKey secretKey =
      xmssRomImpl ∘ₛ
        cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey := by
  funext input
  cases input with
  | inl worldInput =>
      simp [cappedUnloggedMappedAdversaryImpl,
        cappedSourceUnloggedMappedAdversaryImpl]
  | inr request => rfl

theorem cappedUnloggedMappedAdversary_simulateQ_run_eq_source
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    (simulateQ (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        computation).run cache =
      (simulateQ xmssRomImpl
        (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
          computation)).run cache := by
  rw [cappedUnloggedMappedAdversaryImpl_eq_source_compose,
    QueryImpl.simulateQ_compose]

theorem expectedEpochEncodingSamples_splitDetailedGameAfterKeygen_le_source
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    expectedEpochEncodingSamples
        (cappedSplitUnloggedDetailedGameAfterKeygen adversary publicKey secretKey
          initialCache) ≤
      expectedSimulatedQueryCount xmssRomImpl
        (IsEncodingHashQuery secretKey.parameter)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary publicKey secretKey)
        initialCache := by
  let splitHead :=
    (simulateQ (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run initialCache
  let sourceHead := simulateQ
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
    (adversary.main publicKey)
  let splitFinish : Forgery × QueryCache HashSpec →
      OracleComp EncodingSamplingWorld ((Forgery × Bool) × QueryCache HashSpec) :=
    fun result => do
      let verifiedResult ←
        (simulateQ (splitXmssRomImpl secretKey.parameter .query)
          (Concrete.scheme.verify publicKey result.1.epoch result.1.message
            result.1.signature)).run result.2
      pure ((result.1, verifiedResult.1), verifiedResult.2)
  let sourceFinish : Forgery → OracleComp OracleWorld (Forgery × Bool) :=
    fun forgery => do
      let verified ← Concrete.scheme.verify publicKey forgery.epoch
        forgery.message forgery.signature
      pure (forgery, verified)
  have hhead : expectedEpochEncodingSamples splitHead ≤
      expectedSimulatedQueryCount xmssRomImpl
        (IsEncodingHashQuery secretKey.parameter) sourceHead initialCache := by
    exact expectedEpochEncodingSamples_simulate_cappedSplitUnloggedMapped_le
      publicKey secretKey (adversary.main publicKey) initialCache
  have hdist : evalDist (simulateQ encodingSamplingWorldImpl splitHead) =
      evalDist ((simulateQ xmssRomImpl sourceHead).run initialCache) := by
    calc
      _ = evalDist
          ((simulateQ (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
            (adversary.main publicKey)).run initialCache) :=
        cappedSplitUnloggedMappedAdversary_evalDist_simulation
          publicKey secretKey (adversary.main publicKey) initialCache
      _ = _ := by
        rw [cappedUnloggedMappedAdversary_simulateQ_run_eq_source]
  have hfinish : ∀ result : Forgery × QueryCache HashSpec,
      expectedEpochEncodingSamples (splitFinish result) ≤
        expectedSimulatedQueryCount xmssRomImpl
          (IsEncodingHashQuery secretKey.parameter)
          (sourceFinish result.1) result.2 := by
    intro result
    let verification := Concrete.scheme.verify publicKey result.1.epoch
      result.1.message result.1.signature
    have hverify := expectedEpochEncodingSamples_simulate_splitXmssRom_le
      secretKey.parameter .query verification result.2
    calc
      expectedEpochEncodingSamples (splitFinish result) =
          expectedEpochEncodingSamples
            ((simulateQ (splitXmssRomImpl secretKey.parameter .query)
              verification).run result.2) := by
        unfold splitFinish
        rw [expectedEpochEncodingSamples_bind]
        simp
        rfl
      _ ≤ expectedSimulatedQueryCount xmssRomImpl
          (IsEncodingHashQuery secretKey.parameter) verification result.2 := hverify
      _ = expectedSimulatedQueryCount xmssRomImpl
          (IsEncodingHashQuery secretKey.parameter)
          (sourceFinish result.1) result.2 := by
        unfold sourceFinish verification
        rw [expectedSimulatedQueryCount_bind]
        simp
  unfold cappedSplitUnloggedDetailedGameAfterKeygen
    cappedSourceUnloggedDetailedGameAfterKeygen
  change expectedEpochEncodingSamples (splitHead >>= splitFinish) ≤
    expectedSimulatedQueryCount xmssRomImpl
      (IsEncodingHashQuery secretKey.parameter)
      (sourceHead >>= sourceFinish) initialCache
  rw [expectedEpochEncodingSamples_bind,
    expectedSimulatedQueryCount_bind]
  calc
    expectedEpochEncodingSamples splitHead +
        ∑' result, Pr[= result | simulateQ encodingSamplingWorldImpl splitHead] *
          expectedEpochEncodingSamples (splitFinish result) ≤
      expectedSimulatedQueryCount xmssRomImpl
          (IsEncodingHashQuery secretKey.parameter) sourceHead initialCache +
        ∑' result, Pr[= result | simulateQ encodingSamplingWorldImpl splitHead] *
          expectedSimulatedQueryCount xmssRomImpl
            (IsEncodingHashQuery secretKey.parameter)
            (sourceFinish result.1) result.2 := by
      apply add_le_add hhead
      apply ENNReal.tsum_le_tsum
      intro result
      gcongr
      exact hfinish result
    _ = expectedSimulatedQueryCount xmssRomImpl
          (IsEncodingHashQuery secretKey.parameter) sourceHead initialCache +
        ∑' result, Pr[= result |
            (simulateQ xmssRomImpl sourceHead).run initialCache] *
          expectedSimulatedQueryCount xmssRomImpl
            (IsEncodingHashQuery secretKey.parameter)
            (sourceFinish result.1) result.2 := by
      congr 1
      apply tsum_congr
      intro result
      rw [OracleComp.probOutput_congr rfl hdist]

theorem expectedAttackerEncodingQueries_splitDetailedGameAfterKeygen_le_source
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    expectedAttackerEncodingQueries
        (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary publicKey
          secretKey initialCache) ≤
      expectedSimulatedQueryCount xmssRomImpl
        (IsEncodingHashQuery secretKey.parameter)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary publicKey secretKey)
        initialCache := by
  calc
    expectedAttackerEncodingQueries
        (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary publicKey
          secretKey initialCache) ≤
      expectedEpochEncodingSamples
        (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary publicKey
          secretKey initialCache) :=
      expectedAttackerEncodingQueries_le_epochSamples _
    _ = expectedEpochEncodingSamples
        (cappedSplitUnloggedDetailedGameAfterKeygen adversary publicKey secretKey
          initialCache) := by
      have hprojection := congrArg expectedEpochEncodingSamples
        (cappedSplitDetailedGameAfterKeygenWithEncodingTrace_unlogged_projection
          adversary publicKey secretKey initialCache)
      rw [expectedEpochEncodingSamples_map] at hprojection
      exact hprojection
    _ ≤ _ := expectedEpochEncodingSamples_splitDetailedGameAfterKeygen_le_source
      adversary publicKey secretKey initialCache

noncomputable def expectedPostKeygenEncodingQueries
    (adversary : Adversary Concrete.scheme) : ENNReal :=
  ∑' keyResult,
    Pr[= keyResult | (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅] *
      expectedSimulatedQueryCount xmssRomImpl
        (IsEncodingHashQuery keyResult.1.2.parameter)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary
          keyResult.1.1 keyResult.1.2) keyResult.2

theorem sampledHashOutput_expected_snd_eq_uniform
    (cost : HashOutput → ENNReal) :
    ∑' digest, Pr[= digest | ($ᵗ Digest)] *
        ∑' output, Pr[= output | Rom.sampleHashOutputWithDigest digest] *
          cost output =
      ∑' output, Pr[= output | uniformHashOutput] * cost output := by
  rw [← tsum_probOutput_bind_mul]
  unfold uniformHashOutput
  apply tsum_congr
  intro output
  rw [OracleComp.probOutput_congr rfl
    Rom.evalDist_uniformDigest_bind_sampleHashOutputWithDigest]

theorem applyUniformQueryMonitor_true_probability_le_expected
    (epoch : Epoch)
    (resume : Digest → EncodingMonitor.State → ProbComp Bool)
    (cost : Digest → ENNReal) (state : EncodingMonitor.State)
    (hresume : ∀ digest nextState,
      Pr[(· = true) | resume digest nextState] ≤
        cost digest + State.pendingRisk nextState) :
    Pr[(· = true) | applyUniformQueryMonitor epoch resume state] ≤
      (Fintype.card Digest : ENNReal)⁻¹ +
        (∑' digest, Pr[= digest | ($ᵗ Digest)] * cost digest) +
          State.pendingRisk state := by
  cases hsigned : state.signed epoch with
  | some target =>
      unfold applyUniformQueryMonitor
      rw [hsigned, probEvent_bind_eq_tsum, tsum_fintype]
      calc
        _ ≤ ∑ digest : Digest, Pr[= digest | ($ᵗ Digest)] *
            ((if digest = target then 1 else 0) +
              cost digest + State.pendingRisk state) := by
          apply Finset.sum_le_sum
          intro digest _hdigest
          apply mul_le_mul_right
          by_cases heq : digest = target
          · simp only [heq, ↓reduceIte, probEvent_pure]
            exact le_add_right (le_add_right le_rfl)
          · simpa [heq] using hresume digest state
        _ = (∑ digest : Digest, Pr[= digest | ($ᵗ Digest)] *
              (if digest = target then 1 else 0)) +
            (∑ digest : Digest, Pr[= digest | ($ᵗ Digest)] * cost digest) +
            (∑ digest : Digest, Pr[= digest | ($ᵗ Digest)]) *
              State.pendingRisk state := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_mul]
        _ = _ := by
          have hcollision :
              ∑ digest : Digest, Pr[= digest | ($ᵗ Digest)] *
                  (if digest = target then 1 else 0) =
                (Fintype.card Digest : ENNReal)⁻¹ := by
            convert uniformDigest_mem_bonus_sum_eq ({target} : Finset Digest) using 1 <;>
              simp
          rw [hcollision]
          rw [sum_probOutput_eq_one (mx := ($ᵗ Digest)) (by simp), one_mul]
          simp only [tsum_fintype]
  | none =>
      unfold applyUniformQueryMonitor
      rw [hsigned, probEvent_bind_eq_tsum, tsum_fintype]
      calc
        _ ≤ ∑ digest : Digest, Pr[= digest | ($ᵗ Digest)] *
            (cost digest + State.pendingRisk state +
              if TargetSum.ValidDigest digest then
                (TargetSum.validDigests.card : ENNReal)⁻¹ else 0) := by
          apply Finset.sum_le_sum
          intro digest _hdigest
          apply mul_le_mul_right
          by_cases hvalid : TargetSum.ValidDigest digest
          · simp only [hvalid, ↓reduceIte]
            calc
              _ ≤ cost digest + State.pendingRisk (state.addPending epoch digest) :=
                hresume digest (state.addPending epoch digest)
              _ ≤ cost digest + (State.pendingRisk state +
                    (TargetSum.validDigests.card : ENNReal)⁻¹) := by
                gcongr
                exact State.pendingRisk_addPending_le state epoch digest
              _ = _ := by ac_rfl
          · simpa [hvalid] using hresume digest state
        _ = (∑ digest : Digest, Pr[= digest | ($ᵗ Digest)] * cost digest) +
            State.pendingRisk state +
            (Fintype.card Digest : ENNReal)⁻¹ := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.sum_mul]
          rw [sum_probOutput_eq_one (mx := ($ᵗ Digest)) (by simp), one_mul,
            uniformDigest_valid_bonus_sum_eq]
        _ = _ := by
          simp only [tsum_fintype]
          calc
            _ = (Fintype.card Digest : ENNReal)⁻¹ +
                ((∑ digest : Digest, Pr[= digest | ($ᵗ Digest)] * cost digest) +
                  State.pendingRisk state) := add_comm _ _
            _ = _ := (add_assoc _ _ _).symm

theorem applyUniformSignAttemptMonitor_true_probability_le_expected
    (epoch : Epoch)
    (resume : Digest → EncodingMonitor.State → ProbComp Bool)
    (cost : Digest → ENNReal) (state : EncodingMonitor.State)
    (hresume : ∀ digest nextState,
      Pr[(· = true) | resume digest nextState] ≤
        cost digest + State.pendingRisk nextState) :
    Pr[(· = true) | applyUniformSignAttemptMonitor epoch resume state] ≤
      (∑' digest, Pr[= digest | ($ᵗ Digest)] * cost digest) +
        State.pendingRisk state := by
  cases hsigned : state.signed epoch with
  | some target =>
      unfold applyUniformSignAttemptMonitor
      rw [probEvent_bind_eq_tsum, tsum_fintype]
      calc
        _ ≤ ∑ digest : Digest, Pr[= digest | ($ᵗ Digest)] *
            (cost digest + State.pendingRisk state) := by
          apply Finset.sum_le_sum
          intro digest _hdigest
          apply mul_le_mul_right
          by_cases hvalid : TargetSum.ValidDigest digest
          · simp [hvalid, hsigned]
          · simpa [hvalid] using hresume digest state
        _ = _ := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul,
            sum_probOutput_eq_one (mx := ($ᵗ Digest)) (by simp), one_mul]
          simp only [tsum_fintype]
  | none =>
      let remaining := State.pendingRisk (state.install epoch 0)
      let removed := ((state.pending epoch).card : ENNReal) *
        (TargetSum.validDigests.card : ENNReal)⁻¹
      have hrisk : remaining + removed = State.pendingRisk state :=
        State.pendingRisk_install_add state epoch 0
      unfold applyUniformSignAttemptMonitor
      rw [probEvent_bind_eq_tsum, tsum_fintype]
      calc
        _ ≤ ∑ digest : Digest, Pr[= digest | ($ᵗ Digest)] *
            (cost digest + remaining +
              if TargetSum.ValidDigest digest then
                if digest ∈ state.pending epoch then 1 else 0
              else removed) := by
          apply Finset.sum_le_sum
          intro digest _hdigest
          apply mul_le_mul_right
          by_cases hvalid : TargetSum.ValidDigest digest
          · simp only [hvalid, ↓reduceIte, hsigned]
            by_cases hmem : digest ∈ state.pending epoch
            · simp [hmem]
            · simp only [hmem, ↓reduceIte, add_zero]
              have hriskEq :
                  State.pendingRisk (state.install epoch digest) = remaining := by
                unfold remaining State.pendingRisk
                rw [EncodingMonitor.State.pendingCount_install_eq state epoch digest 0]
              simpa [hriskEq] using hresume digest (state.install epoch digest)
          · simp only [hvalid, ↓reduceIte]
            calc
              _ ≤ cost digest + State.pendingRisk state := hresume digest state
              _ = cost digest + remaining + removed := by rw [← hrisk]; ac_rfl
        _ = (∑ digest : Digest, Pr[= digest | ($ᵗ Digest)] * cost digest) +
            remaining +
            ∑ digest : Digest, Pr[= digest | ($ᵗ Digest)] *
              (if TargetSum.ValidDigest digest then
                if digest ∈ state.pending epoch then 1 else 0
              else removed) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.sum_mul]
          rw [sum_probOutput_eq_one (mx := ($ᵗ Digest)) (by simp), one_mul]
        _ ≤ (∑ digest : Digest, Pr[= digest | ($ᵗ Digest)] * cost digest) +
            remaining + removed := by
          gcongr
          exact uniformDigest_sign_bonus_sum_le (state.pending epoch)
        _ = _ := by
          simp only [tsum_fintype]
          rw [← hrisk]
          exact add_assoc _ _ _

theorem applyProgrammedQueryMonitor_true_probability_le_expected
    (epoch : Epoch)
    (resume : HashOutput → EncodingMonitor.State → ProbComp Bool)
    (cost : HashOutput → ENNReal) (state : EncodingMonitor.State)
    (hresume : ∀ output nextState,
      Pr[(· = true) | resume output nextState] ≤
        cost output + State.pendingRisk nextState) :
    Pr[(· = true) | applyProgrammedQueryMonitor epoch resume state] ≤
      (Fintype.card Digest : ENNReal)⁻¹ +
        (∑' output, Pr[= output | uniformHashOutput] * cost output) +
          State.pendingRisk state := by
  let digestCost : Digest → ENNReal := fun digest =>
    ∑' output, Pr[= output | Rom.sampleHashOutputWithDigest digest] * cost output
  have hconditional : ∀ digest nextState,
      Pr[(· = true) |
        Rom.sampleHashOutputWithDigest digest >>= fun output =>
          resume output nextState] ≤
        digestCost digest + State.pendingRisk nextState := by
    intro digest nextState
    rw [probEvent_bind_eq_tsum]
    calc
      _ ≤ ∑' output, Pr[= output | Rom.sampleHashOutputWithDigest digest] *
          (cost output + State.pendingRisk nextState) := by
        apply ENNReal.tsum_le_tsum
        intro output
        gcongr
        exact hresume output nextState
      _ = digestCost digest +
          (∑' output, Pr[= output | Rom.sampleHashOutputWithDigest digest]) *
            State.pendingRisk nextState := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      _ = digestCost digest + State.pendingRisk nextState := by
        rw [tsum_probOutput_eq_one' (by simp [Rom.sampleHashOutputWithDigest]), one_mul]
  unfold applyProgrammedQueryMonitor
  exact (applyUniformQueryMonitor_true_probability_le_expected epoch
    (fun digest nextState =>
      Rom.sampleHashOutputWithDigest digest >>= fun output =>
        resume output nextState) digestCost state hconditional).trans_eq (by
      rw [sampledHashOutput_expected_snd_eq_uniform cost])

theorem applyProgrammedSignAttemptMonitor_true_probability_le_expected
    (epoch : Epoch)
    (resume : HashOutput → EncodingMonitor.State → ProbComp Bool)
    (cost : HashOutput → ENNReal) (state : EncodingMonitor.State)
    (hresume : ∀ output nextState,
      Pr[(· = true) | resume output nextState] ≤
        cost output + State.pendingRisk nextState) :
    Pr[(· = true) | applyProgrammedSignAttemptMonitor epoch resume state] ≤
      (∑' output, Pr[= output | uniformHashOutput] * cost output) +
        State.pendingRisk state := by
  let digestCost : Digest → ENNReal := fun digest =>
    ∑' output, Pr[= output | Rom.sampleHashOutputWithDigest digest] * cost output
  have hconditional : ∀ digest nextState,
      Pr[(· = true) |
        Rom.sampleHashOutputWithDigest digest >>= fun output =>
          resume output nextState] ≤
        digestCost digest + State.pendingRisk nextState := by
    intro digest nextState
    rw [probEvent_bind_eq_tsum]
    calc
      _ ≤ ∑' output, Pr[= output | Rom.sampleHashOutputWithDigest digest] *
          (cost output + State.pendingRisk nextState) := by
        apply ENNReal.tsum_le_tsum
        intro output
        gcongr
        exact hresume output nextState
      _ = digestCost digest +
          (∑' output, Pr[= output | Rom.sampleHashOutputWithDigest digest]) *
            State.pendingRisk nextState := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      _ = digestCost digest + State.pendingRisk nextState := by
        rw [tsum_probOutput_eq_one' (by simp [Rom.sampleHashOutputWithDigest]), one_mul]
  unfold applyProgrammedSignAttemptMonitor
  exact (applyUniformSignAttemptMonitor_true_probability_le_expected epoch
    (fun digest nextState =>
      Rom.sampleHashOutputWithDigest digest >>= fun output =>
        resume output nextState) digestCost state hconditional).trans_eq (by
      rw [sampledHashOutput_expected_snd_eq_uniform cost])

theorem probEvent_bind_le_expected_mul_add
    (mx : ProbComp β) (resume : β → ProbComp Bool)
    (cost : β → ENNReal) (scale risk : ENNReal)
    (hresume : ∀ output,
      Pr[(· = true) | resume output] ≤ cost output * scale + risk)
    (hmass : ∑' output, Pr[= output | mx] = 1) :
    Pr[(· = true) | mx >>= resume] ≤
      (∑' output, Pr[= output | mx] * cost output) * scale + risk := by
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' output, Pr[= output | mx] * (cost output * scale + risk) := by
      apply ENNReal.tsum_le_tsum
      intro output
      exact mul_le_mul_right (hresume output) _
    _ = (∑' output, Pr[= output | mx] * cost output) * scale +
        (∑' output, Pr[= output | mx]) * risk := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
      congr 1
      · simp_rw [← mul_assoc]
        rw [ENNReal.tsum_mul_right]
      · rw [ENNReal.tsum_mul_right]
    _ = _ := by rw [hmass, one_mul]

theorem runRawStructural_true_probability_le_expected
    (state : EncodingMonitor.State)
    (computation : OracleComp EncodingSamplingWorld α) :
    Pr[(· = true) | runRawStructural state computation] ≤
      expectedAttackerEncodingQueries computation *
          (Fintype.card Digest : ENNReal)⁻¹ +
        State.pendingRisk state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result =>
      rw [runRawStructural, OracleComp.construct_pure, probEvent_pure]
      simp
  | query_bind input next ih =>
      rw [runRawStructural, OracleComp.construct_query_bind]
      cases input with
      | inl index =>
          rw [expectedAttackerEncodingQueries_query_bind]
          have hplain := probEvent_bind_le_expected_mul_add
            (mx := (liftM (unifSpec.query index) : ProbComp _))
            (resume := fun output => runRawStructural state (next output))
            (cost := fun output => expectedAttackerEncodingQueries (next output))
            (scale := (Fintype.card Digest : ENNReal)⁻¹)
            (risk := State.pendingRisk state)
            (fun output => ih output state)
            (tsum_probOutput_eq_one' (by simp))
          simpa [runRawStructural, IsAttackerEncodingQuery, encodingSamplingWorldImpl,
            uniformWorldImpl] using hplain
      | inr address =>
          rcases address with ⟨kind, taggedEpoch, input⟩
          cases kind with
          | side =>
              change HashOutput → OracleComp EncodingSamplingWorld α at next
              change ∀ (output : HashOutput) (nextState : EncodingMonitor.State),
                Pr[(· = true) | runRawStructural nextState (next output)] ≤
                  expectedAttackerEncodingQueries (next output) *
                      (Fintype.card Digest : ENNReal)⁻¹ +
                    State.pendingRisk nextState at ih
              rw [expectedAttackerEncodingQueries_sample_query_bind]
              simp only [IsAttackerEncodingQuery, if_false, zero_add]
              unfold applyRawSampleMonitor
              have hplain := probEvent_bind_le_expected_mul_add
                (mx := uniformHashOutput)
                (resume := fun output => runRawStructural state (next output))
                (cost := fun output => expectedAttackerEncodingQueries (next output))
                (scale := (Fintype.card Digest : ENNReal)⁻¹)
                (risk := State.pendingRisk state)
                (fun output => ih output state)
                (tsum_probOutput_eq_one' (by simp [uniformHashOutput]))
              simpa [runRawStructural, applyRawSampleMonitor,
                IsAttackerEncodingQuery, encodingSamplingWorldImpl,
                encodingOutputImpl] using hplain
          | query =>
              cases taggedEpoch with
              | none =>
                  change HashOutput → OracleComp EncodingSamplingWorld α at next
                  change ∀ (output : HashOutput) (nextState : EncodingMonitor.State),
                    Pr[(· = true) | runRawStructural nextState (next output)] ≤
                      expectedAttackerEncodingQueries (next output) *
                          (Fintype.card Digest : ENNReal)⁻¹ +
                        State.pendingRisk nextState at ih
                  rw [expectedAttackerEncodingQueries_sample_query_bind]
                  simp only [IsAttackerEncodingQuery, if_false, zero_add]
                  unfold applyRawSampleMonitor
                  have hplain := probEvent_bind_le_expected_mul_add
                    (mx := uniformHashOutput)
                    (resume := fun output => runRawStructural state (next output))
                    (cost := fun output => expectedAttackerEncodingQueries (next output))
                    (scale := (Fintype.card Digest : ENNReal)⁻¹)
                    (risk := State.pendingRisk state)
                    (fun output => ih output state)
                    (tsum_probOutput_eq_one' (by simp [uniformHashOutput]))
                  simpa [runRawStructural, applyRawSampleMonitor,
                    IsAttackerEncodingQuery,
                    encodingSamplingWorldImpl,
                    encodingOutputImpl] using hplain
              | some epoch =>
                  change HashOutput → OracleComp EncodingSamplingWorld α at next
                  change ∀ (output : HashOutput) (nextState : EncodingMonitor.State),
                    Pr[(· = true) | runRawStructural nextState (next output)] ≤
                      expectedAttackerEncodingQueries (next output) *
                          (Fintype.card Digest : ENNReal)⁻¹ +
                        State.pendingRisk nextState at ih
                  rw [expectedAttackerEncodingQueries_sample_query_bind]
                  simp only [IsAttackerEncodingQuery, if_true]
                  unfold applyRawSampleMonitor
                  have hmonitor :=
                    applyProgrammedQueryMonitor_true_probability_le_expected epoch
                      (fun output nextState =>
                        runRawStructural nextState (next output))
                      (fun output => expectedAttackerEncodingQueries (next output) *
                        (Fintype.card Digest : ENNReal)⁻¹)
                      state (fun output nextState => ih output nextState)
                  calc
                    _ ≤ (Fintype.card Digest : ENNReal)⁻¹ +
                        (∑' output, Pr[= output | uniformHashOutput] *
                          (expectedAttackerEncodingQueries (next output) *
                            (Fintype.card Digest : ENNReal)⁻¹)) +
                          State.pendingRisk state := hmonitor
                    _ = _ := by
                      simp_rw [← mul_assoc]
                      rw [ENNReal.tsum_mul_right, add_mul, one_mul]
          | sign =>
              cases taggedEpoch with
              | none =>
                  change HashOutput → OracleComp EncodingSamplingWorld α at next
                  change ∀ (output : HashOutput) (nextState : EncodingMonitor.State),
                    Pr[(· = true) | runRawStructural nextState (next output)] ≤
                      expectedAttackerEncodingQueries (next output) *
                          (Fintype.card Digest : ENNReal)⁻¹ +
                        State.pendingRisk nextState at ih
                  rw [expectedAttackerEncodingQueries_sample_query_bind]
                  simp only [IsAttackerEncodingQuery, if_false, zero_add]
                  unfold applyRawSampleMonitor
                  have hplain := probEvent_bind_le_expected_mul_add
                    (mx := uniformHashOutput)
                    (resume := fun output => runRawStructural state (next output))
                    (cost := fun output => expectedAttackerEncodingQueries (next output))
                    (scale := (Fintype.card Digest : ENNReal)⁻¹)
                    (risk := State.pendingRisk state)
                    (fun output => ih output state)
                    (tsum_probOutput_eq_one' (by simp [uniformHashOutput]))
                  simpa [runRawStructural, applyRawSampleMonitor,
                    IsAttackerEncodingQuery,
                    encodingSamplingWorldImpl,
                    encodingOutputImpl] using hplain
              | some epoch =>
                  change HashOutput → OracleComp EncodingSamplingWorld α at next
                  change ∀ (output : HashOutput) (nextState : EncodingMonitor.State),
                    Pr[(· = true) | runRawStructural nextState (next output)] ≤
                      expectedAttackerEncodingQueries (next output) *
                          (Fintype.card Digest : ENNReal)⁻¹ +
                        State.pendingRisk nextState at ih
                  rw [expectedAttackerEncodingQueries_sample_query_bind]
                  simp only [IsAttackerEncodingQuery, if_false, zero_add]
                  unfold applyRawSampleMonitor
                  have hmonitor :=
                    applyProgrammedSignAttemptMonitor_true_probability_le_expected epoch
                      (fun output nextState =>
                        runRawStructural nextState (next output))
                      (fun output => expectedAttackerEncodingQueries (next output) *
                        (Fintype.card Digest : ENNReal)⁻¹)
                      state (fun output nextState => ih output nextState)
                  calc
                    _ ≤ (∑' output, Pr[= output | uniformHashOutput] *
                          (expectedAttackerEncodingQueries (next output) *
                            (Fintype.card Digest : ENNReal)⁻¹)) +
                          State.pendingRisk state := hmonitor
                    _ = _ := by
                      simp_rw [← mul_assoc]
                      rw [← ENNReal.tsum_mul_right]

theorem runRawStructural_empty_true_probability_le_expected
    (computation : OracleComp EncodingSamplingWorld α) :
    Pr[(· = true) |
      runRawStructural EncodingMonitor.State.empty computation] ≤
      expectedAttackerEncodingQueries computation *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [State.pendingRisk_empty, add_zero] using
    runRawStructural_true_probability_le_expected EncodingMonitor.State.empty
      computation

theorem encodingSamplingTrace_collision_probability_le_expected
    (computation : OracleComp EncodingSamplingWorld α) :
    Pr[fun result : α × EncodingActionTrace =>
        runObserved EncodingMonitor.State.empty result.2 = true |
      (simulateQ encodingSamplingTraceImpl computation).run] ≤
      expectedAttackerEncodingQueries computation *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  change Pr[((fun hit : Bool => hit = true) ∘ fun result =>
      runObserved EncodingMonitor.State.empty result.2) |
    (simulateQ encodingSamplingTraceImpl computation).run] ≤ _
  rw [← probEvent_map]
  exact (runTraced_probability_le_rawStructural EncodingMonitor.State.empty
    computation).trans
      (runRawStructural_empty_true_probability_le_expected computation)

theorem cappedSampledDetailedGame_externalCollision_probability_le_expected
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : (GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
          EncodingActionTrace =>
      runObserved EncodingMonitor.State.empty execution.2 = true |
      cappedSampledDetailedGameWithEncodingTrace adversary] ≤
      expectedPostKeygenEncodingQueries adversary *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  unfold cappedSampledDetailedGameWithEncodingTrace
    expectedPostKeygenEncodingQueries
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' keyResult,
        Pr[= keyResult |
          (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅] *
          (expectedSimulatedQueryCount xmssRomImpl
            (IsEncodingHashQuery keyResult.1.2.parameter)
            (cappedSourceUnloggedDetailedGameAfterKeygen adversary
              keyResult.1.1 keyResult.1.2) keyResult.2 *
                (Fintype.card Digest : ENNReal)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      apply mul_le_mul_right
      exact (encodingSamplingTrace_collision_probability_le_expected
        (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary
          keyResult.1.1 keyResult.1.2 keyResult.2)).trans
        (mul_le_mul'
          (expectedAttackerEncodingQueries_splitDetailedGameAfterKeygen_le_source
            adversary keyResult.1.1 keyResult.1.2 keyResult.2) le_rfl)
    _ = _ := by
      simp_rw [← mul_assoc]
      rw [ENNReal.tsum_mul_right]

end XmssSecurity.CappedEncodingMonitor
