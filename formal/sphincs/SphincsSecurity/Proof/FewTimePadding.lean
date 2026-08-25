import SphincsSecurity.Proof.FewTimeViewTrace
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Padding adaptive few-time view sequences

A run may make fewer than the allowed number of signing queries. Extending its view sequence with
independent unused coordinates embeds every coverage pattern into the fixed signature-limit space.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable local instance {α : Type} [Fintype α] [Nonempty α] : SampleableType α :=
  SampleableType.ofFintype α

noncomputable def uniformSnocList (α : Type) [SampleableType α] : Nat → ProbComp (List α)
  | 0 => pure []
  | count + 1 => do
      let prior ← uniformSnocList α count
      let next ← $ᵗ α
      pure (prior ++ [next])

theorem evalDist_independent_uniform_pair
    {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] :
    𝒟[(do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right))] =
      𝒟[($ᵗ (α × β) : ProbComp (α × β))] := by
  apply SPMF.ext
  intro target
  rw [show (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) = Prod.mk <$> ($ᵗ α) <*> ($ᵗ β) by
    simp [monad_norm]]
  change Pr[= target | Prod.mk <$> ($ᵗ α) <*> ($ᵗ β)] =
    Pr[= target | $ᵗ (α × β)]
  rw [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    probOutput_uniformSample, probOutput_uniformSample, Fintype.card_prod,
    Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

theorem uniformSnocList_append (α : Type) [SampleableType α]
    (firstLength secondLength : Nat) :
    (do
      let first ← uniformSnocList α firstLength
      let second ← uniformSnocList α secondLength
      pure (first ++ second)) =
      uniformSnocList α (firstLength + secondLength) := by
  induction secondLength with
  | zero => simp [uniformSnocList]
  | succ secondLength ih =>
      simp [uniformSnocList, bind_assoc, ← ih, List.append_assoc]

def finInitLastEquiv (α : Type) (count : Nat) :
    ((Fin count → α) × α) ≃ (Fin (count + 1) → α) where
  toFun pair := Fin.lastCases pair.2 pair.1
  invFun values := (fun index => values index.castSucc, values (Fin.last count))
  left_inv pair := by
    apply Prod.ext
    · funext index
      simp
    · simp
  right_inv values := by
    funext index
    cases index using Fin.lastCases <;> simp

set_option maxRecDepth 100000 in
theorem evalDist_uniformSnocList_eq_uniformFunction
    (α : Type) [Fintype α] [SampleableType α] (count : Nat) :
    𝒟[uniformSnocList α count] =
      𝒟[List.ofFn <$> ($ᵗ (Fin count → α) : ProbComp (Fin count → α))] := by
  induction count with
  | zero =>
      rw [uniformSnocList]
      symm
      rw [map_eq_bind_pure_comp]
      calc
        𝒟[($ᵗ (Fin 0 → α) : ProbComp (Fin 0 → α)) >>= fun values =>
            pure (List.ofFn values)] =
            𝒟[($ᵗ (Fin 0 → α) : ProbComp (Fin 0 → α)) >>= fun _ => pure []] := by
          apply evalDist_bind_congr
          intro values _
          have hnil : List.ofFn values = [] :=
            List.eq_nil_of_length_eq_zero (by simp)
          rw [hnil]
        _ = 𝒟[pure []] :=
          OracleComp.DeferredSampling.evalDist_bind_const_neverFails
            ($ᵗ (Fin 0 → α)) (probFailure_eq_zero' inferInstance) (pure [])
  | succ count ih =>
      rw [uniformSnocList]
      calc
        _ = 𝒟[(List.ofFn <$> ($ᵗ (Fin count → α) : ProbComp (Fin count → α))) >>=
            fun prior => ($ᵗ α) >>= fun next => pure (prior ++ [next])] := by
          rw [evalDist_bind, ih, ← evalDist_bind]
        _ = 𝒟[List.ofFn <$> (finInitLastEquiv α count <$> (do
              let prior ← $ᵗ (Fin count → α)
              let next ← $ᵗ α
              pure (prior, next)))] := by
          congr 1
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply]
          apply bind_congr
          intro prior
          apply bind_congr
          intro next
          congr 1
          rw [List.ofFn_succ']
          simp [finInitLastEquiv]
        _ = 𝒟[List.ofFn <$> (finInitLastEquiv α count <$>
              ($ᵗ ((Fin count → α) × α) : ProbComp ((Fin count → α) × α)))] := by
          rw [evalDist_map, evalDist_map, evalDist_independent_uniform_pair,
            ← evalDist_map, ← evalDist_map]
        _ = 𝒟[List.ofFn <$>
              ($ᵗ (Fin (count + 1) → α) : ProbComp (Fin (count + 1) → α))] := by
          rw [evalDist_map]
          rw [evalDist_map_bijective_uniform_cross
            (α := (Fin count → α) × α) (β := Fin (count + 1) → α)
            (finInitLastEquiv α count) (finInitLastEquiv α count).bijective]
          rw [← evalDist_map]

theorem uniformSnocList_support_length (α : Type) [SampleableType α]
    (count : Nat) (values : List α)
    (hmem : values ∈ support (uniformSnocList α count)) : values.length = count := by
  induction count generalizing values with
  | zero =>
      simp only [uniformSnocList, support_pure, Set.mem_singleton_iff] at hmem
      subst values
      rfl
  | succ count ih =>
      rw [uniformSnocList, mem_support_bind_iff] at hmem
      obtain ⟨prior, hprior, hrest⟩ := hmem
      rw [mem_support_bind_iff] at hrest
      obtain ⟨next, _, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst values
      simp [ih prior hprior]

inductive CompletesOptionViews :
    List (Option FewTimeView) → List FewTimeView → Prop
  | nil : CompletesOptionViews [] []
  | none {options views} (view : FewTimeView)
      (hrest : CompletesOptionViews options views) :
      CompletesOptionViews (none :: options) (view :: views)
  | some {options views} (view : FewTimeView)
      (hrest : CompletesOptionViews options views) :
      CompletesOptionViews (some view :: options) (view :: views)

theorem CompletesOptionViews.length_eq {options : List (Option FewTimeView)}
    {views : List FewTimeView} (hcomplete : CompletesOptionViews options views) :
    views.length = options.length := by
  induction hcomplete <;> simp_all

noncomputable def completeOptionViews :
    List (Option FewTimeView) → ProbComp (List FewTimeView)
  | [] => pure []
  | none :: options => do
      let view ← $ᵗ FewTimeView
      let views ← completeOptionViews options
      pure (view :: views)
  | some view :: options => do
      let views ← completeOptionViews options
      pure (view :: views)

theorem completeOptionViews_support (options : List (Option FewTimeView))
    (views : List FewTimeView) (hmem : views ∈ support (completeOptionViews options)) :
    CompletesOptionViews options views := by
  induction options generalizing views with
  | nil =>
      simp only [completeOptionViews, support_pure, Set.mem_singleton_iff] at hmem
      subst views
      exact .nil
  | cons option options ih =>
      cases option with
      | none =>
          rw [completeOptionViews, mem_support_bind_iff] at hmem
          obtain ⟨view, _, hrest⟩ := hmem
          rw [mem_support_bind_iff] at hrest
          obtain ⟨rest, hrest, hpure⟩ := hrest
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst views
          exact .none view (ih rest hrest)
      | some view =>
          rw [completeOptionViews, mem_support_bind_iff] at hmem
          obtain ⟨rest, hrest, hpure⟩ := hmem
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst views
          exact .some view (ih rest hrest)

theorem CompletesOptionViews.getElem?_eq_of_getElem?_eq_some
    {options : List (Option FewTimeView)} {views : List FewTimeView}
    (hcomplete : CompletesOptionViews options views) (position : Nat)
    (view : FewTimeView) (hget : options[position]? = Option.some (Option.some view)) :
    views[position]? = Option.some view := by
  induction hcomplete generalizing position with
  | nil => simp at hget
  | none head hrest ih =>
      cases position with
      | zero => simp at hget
      | succ position => exact ih position (by simpa using hget)
  | some head hrest ih =>
      cases position with
      | zero => simpa using hget
      | succ position => exact ih position (by simpa using hget)

noncomputable def completeAndPadViews (limit : Nat)
    (options : List (Option FewTimeView)) : ProbComp (List FewTimeView) := do
  let views ← completeOptionViews options
  let padding ← uniformSnocList FewTimeView (limit - options.length)
  pure (views ++ padding)

theorem completeAndPadViews_support (limit : Nat)
    (options : List (Option FewTimeView)) (values : List FewTimeView)
    (hmem : values ∈ support (completeAndPadViews limit options)) :
    ∃ views padding,
      CompletesOptionViews options views
        ∧ padding.length = limit - options.length
        ∧ values = views ++ padding := by
  rw [completeAndPadViews, mem_support_bind_iff] at hmem
  obtain ⟨views, hviews, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨padding, hpadding, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  exact ⟨views, padding, completeOptionViews_support options views hviews,
    uniformSnocList_support_length FewTimeView _ padding hpadding, hpure⟩

theorem completeAndPadViews_support_length (limit : Nat)
    (options : List (Option FewTimeView)) (hle : options.length ≤ limit)
    (values : List FewTimeView)
    (hmem : values ∈ support (completeAndPadViews limit options)) :
    values.length = limit := by
  obtain ⟨views, padding, hcomplete, hpadding, rfl⟩ :=
    completeAndPadViews_support limit options values hmem
  rw [List.length_append, hcomplete.length_eq, hpadding, Nat.add_sub_of_le hle]

theorem evalDist_bind_completeAndPadViews_eq_uniformSnocList
    (mx : ProbComp (List (Option FewTimeView))) (count limit : Nat)
    (hle : count ≤ limit)
    (hlength : ∀ options ∈ support mx, options.length = count)
    (hcomplete : 𝒟[mx >>= completeOptionViews] =
      𝒟[uniformSnocList FewTimeView count]) :
    𝒟[mx >>= completeAndPadViews limit] =
      𝒟[uniformSnocList FewTimeView limit] := by
  calc
    𝒟[mx >>= completeAndPadViews limit] =
        𝒟[(mx >>= completeOptionViews) >>= fun views =>
          uniformSnocList FewTimeView (limit - count) >>= fun padding =>
          pure (views ++ padding)] := by
      simp only [bind_assoc]
      apply evalDist_bind_congr
      intro options hoptions
      rw [completeAndPadViews]
      rw [hlength options hoptions]
    _ = 𝒟[uniformSnocList FewTimeView count >>= fun views =>
          uniformSnocList FewTimeView (limit - count) >>= fun padding =>
          pure (views ++ padding)] := by
      rw [evalDist_bind, hcomplete, ← evalDist_bind]
    _ = 𝒟[uniformSnocList FewTimeView
          (count + (limit - count))] := by
      rw [uniformSnocList_append]
    _ = 𝒟[uniformSnocList FewTimeView limit] := by
      rw [Nat.add_sub_of_le hle]

def listToFunction (count : Nat) (values : List FewTimeView) : Fin count → FewTimeView :=
  fun position => values.getD position.val default

@[simp]
theorem listToFunction_ofFn (values : Fin count → FewTimeView) :
    listToFunction count (List.ofFn values) = values := by
  funext position
  simp [listToFunction, List.getD]

theorem listToFunction_eq_get_of_length (values : List FewTimeView)
    (hlength : values.length = count) :
    listToFunction count values = fun position =>
      values.get (Fin.cast hlength.symm position) := by
  funext position
  simp [listToFunction, List.getD, hlength, position.isLt]

noncomputable def completeOptionView : Option FewTimeView → ProbComp FewTimeView
  | none => $ᵗ FewTimeView
  | some view => pure view

theorem completeOptionView_support_some (view completed : FewTimeView)
    (hmem : completed ∈ support (completeOptionView (some view))) : completed = view := by
  simpa [completeOptionView] using hmem

noncomputable def gameAfterSecretsWithPaddedViews (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ProbComp (((Digest × Forgery × Bool) × ViewedFullTraceState) ×
      ((Fin signatureLimit → FewTimeView) × FewTimeView)) := do
  let result ← gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
  let values ← completeAndPadViews signatureLimit result.2.views
  let target ← completeOptionView result.2.targetView
  pure (result, (listToFunction signatureLimit values, target))

theorem gameAfterSecretsWithPaddedViews_support
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : ((Digest × Forgery × Bool) × ViewedFullTraceState) ×
      ((Fin signatureLimit → FewTimeView) × FewTimeView))
    (hmem : result ∈ support
      (gameAfterSecretsWithPaddedViews adversary parameter otsSecret ftsSecret)) :
    ∃ values,
      result.1 ∈ support
        (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret)
        ∧ values ∈ support (completeAndPadViews signatureLimit result.1.2.views)
        ∧ result.2.1 = listToFunction signatureLimit values
        ∧ result.2.2 ∈ support (completeOptionView result.1.2.targetView) := by
  rw [gameAfterSecretsWithPaddedViews, mem_support_bind_iff] at hmem
  obtain ⟨viewedResult, hviewed, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨values, hvalues, hrest⟩ := hrest
  rw [mem_support_bind_iff] at hrest
  obtain ⟨target, htarget, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact ⟨values, hviewed, hvalues, rfl, htarget⟩

theorem evalDist_uniformPaddedSample (count : Nat) :
    𝒟[(do
      let values ← uniformSnocList FewTimeView count
      let target ← $ᵗ FewTimeView
      pure (listToFunction count values, target))] =
      𝒟[($ᵗ ((Fin count → FewTimeView) × FewTimeView) :
        ProbComp ((Fin count → FewTimeView) × FewTimeView))] := by
  calc
    _ = 𝒟[(List.ofFn <$> ($ᵗ (Fin count → FewTimeView) :
          ProbComp (Fin count → FewTimeView))) >>= fun values =>
        ($ᵗ FewTimeView) >>= fun target =>
        pure (listToFunction count values, target)] := by
      rw [evalDist_bind, evalDist_uniformSnocList_eq_uniformFunction, ← evalDist_bind]
    _ = 𝒟[(do
        let values ← $ᵗ (Fin count → FewTimeView)
        let target ← $ᵗ FewTimeView
        pure (values, target))] := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = _ := evalDist_independent_uniform_pair

noncomputable def uniformPaddedSample (count : Nat) :
    ProbComp ((Fin count → FewTimeView) × FewTimeView) := do
  let values ← uniformSnocList FewTimeView count
  let target ← $ᵗ FewTimeView
  pure (listToFunction count values, target)

theorem probEvent_someFewTimePatternHit_uniformPadded_le :
    Pr[SomeFewTimePatternHit signatureLimit |
      uniformPaddedSample signatureLimit] ≤
      1 / ((2 ^ 122 : Nat) : ℝ≥0∞) := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (show 𝒟[uniformPaddedSample signatureLimit] = _ by
      exact evalDist_uniformPaddedSample signatureLimit)]
  simpa only [one_div] using probEvent_someFewTimePatternHit_le le_rfl

def SomeFewTimePatternHitCandidates (signatures candidates : Nat)
    (sample : (Fin signatures → FewTimeView) × (Fin candidates → FewTimeView)) : Prop :=
  ∃ candidate, SomeFewTimePatternHit signatures (sample.1, sample.2 candidate)

noncomputable instance (signatures candidates : Nat) :
    DecidablePred (SomeFewTimePatternHitCandidates signatures candidates) :=
  fun sample => Classical.propDecidable
    (SomeFewTimePatternHitCandidates signatures candidates sample)

noncomputable def uniformCandidateSample (signatures candidates : Nat) :
    ProbComp ((Fin signatures → FewTimeView) × (Fin candidates → FewTimeView)) := do
  let views ← $ᵗ (Fin signatures → FewTimeView)
  let targets ← $ᵗ (Fin candidates → FewTimeView)
  pure (views, targets)

theorem evalDist_uniformCandidateFunctionEval {candidates : Nat}
    (candidate : Fin candidates) :
    𝒟[(fun targets : Fin candidates → FewTimeView => targets candidate) <$>
        ($ᵗ (Fin candidates → FewTimeView) :
          ProbComp (Fin candidates → FewTimeView))] =
      𝒟[($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  let embed : Unit → Fin candidates := fun _ => candidate
  have hembed : Function.Injective embed := by
    intro left right _
    cases left
    cases right
    rfl
  let evaluate : (Unit → FewTimeView) → FewTimeView := fun table => table ()
  have hevaluate : Function.Bijective evaluate := by
    constructor
    · intro left right heq
      funext input
      cases input
      exact heq
    · intro value
      exact ⟨fun _ => value, rfl⟩
  have hrestrict :
      𝒟[(fun table : Fin candidates → FewTimeView => table ∘ embed) <$>
          ($ᵗ (Fin candidates → FewTimeView) :
            ProbComp (Fin candidates → FewTimeView))] =
        𝒟[($ᵗ (Unit → FewTimeView) : ProbComp (Unit → FewTimeView))] := by
    simpa only [bind_pure_comp] using
      evalDist_uniformSample_map_comp_injective (R := FewTimeView) hembed
  have hmarginal :
      𝒟[evaluate <$> ((fun table : Fin candidates → FewTimeView => table ∘ embed) <$>
          ($ᵗ (Fin candidates → FewTimeView) :
            ProbComp (Fin candidates → FewTimeView)))] =
        𝒟[($ᵗ FewTimeView : ProbComp FewTimeView)] := by
    rw [evalDist_map, hrestrict, ← evalDist_map]
    exact evalDist_map_bijective_uniform_cross
      (α := Unit → FewTimeView) (β := FewTimeView) evaluate hevaluate
  simpa [map_eq_bind_pure_comp, bind_assoc, evaluate, embed] using hmarginal

theorem evalDist_uniformCandidateSample_target (signatures candidates : Nat)
    (candidate : Fin candidates) :
    𝒟[(fun sample => (sample.1, sample.2 candidate)) <$>
        uniformCandidateSample signatures candidates] =
      𝒟[($ᵗ ((Fin signatures → FewTimeView) × FewTimeView) :
        ProbComp ((Fin signatures → FewTimeView) × FewTimeView))] := by
  letI : Nonempty (Fin candidates) := ⟨candidate⟩
  calc
    _ = 𝒟[(do
        let views ← $ᵗ (Fin signatures → FewTimeView)
        let target ← $ᵗ FewTimeView
        pure (views, target))] := by
      rw [uniformCandidateSample]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      apply evalDist_bind_congr
      intro views _
      change 𝒟[(fun targets : Fin candidates → FewTimeView =>
          (views, targets candidate)) <$>
            ($ᵗ (Fin candidates → FewTimeView) :
              ProbComp (Fin candidates → FewTimeView))] =
        𝒟[(fun target : FewTimeView => (views, target)) <$>
          ($ᵗ FewTimeView : ProbComp FewTimeView)]
      calc
        _ = 𝒟[(fun target : FewTimeView => (views, target)) <$>
            ((fun targets : Fin candidates → FewTimeView => targets candidate) <$>
              ($ᵗ (Fin candidates → FewTimeView) :
                ProbComp (Fin candidates → FewTimeView)))] := by
          simp [Functor.map_map]
        _ = _ := by
          rw [evalDist_map]
          rw [evalDist_uniformCandidateFunctionEval candidate, ← evalDist_map]
    _ = _ := evalDist_independent_uniform_pair

theorem probEvent_someFewTimePatternHitCandidates_uniform_le
    (signatures candidates : Nat) (hsignatures : signatures ≤ signatureLimit) :
    Pr[SomeFewTimePatternHitCandidates signatures candidates |
        uniformCandidateSample signatures candidates] ≤
      candidates * ((2 ^ 122 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let sampler := uniformCandidateSample signatures candidates
  calc
    Pr[SomeFewTimePatternHitCandidates signatures candidates | sampler] =
        Pr[fun sample => ∃ candidate ∈ (Finset.univ : Finset (Fin candidates)),
          SomeFewTimePatternHit signatures (sample.1, sample.2 candidate) | sampler] := by
      congr 1
      funext sample
      simp [SomeFewTimePatternHitCandidates]
    _ ≤ ∑ candidate ∈ (Finset.univ : Finset (Fin candidates)),
          Pr[fun sample => SomeFewTimePatternHit signatures
            (sample.1, sample.2 candidate) | sampler] :=
      probEvent_exists_finset_le_sum Finset.univ sampler
        (fun candidate sample => SomeFewTimePatternHit signatures
          (sample.1, sample.2 candidate))
    _ = ∑ _candidate ∈ (Finset.univ : Finset (Fin candidates)),
          Pr[SomeFewTimePatternHit signatures |
            ($ᵗ ((Fin signatures → FewTimeView) × FewTimeView) :
              ProbComp ((Fin signatures → FewTimeView) × FewTimeView))] := by
      apply Finset.sum_congr rfl
      intro candidate _
      calc
        Pr[fun sample => SomeFewTimePatternHit signatures
            (sample.1, sample.2 candidate) | sampler] =
            Pr[SomeFewTimePatternHit signatures |
              (fun sample => (sample.1, sample.2 candidate)) <$> sampler] := by
          rw [probEvent_map]
          rfl
        _ = _ := probEvent_congr' (fun _ _ => Iff.rfl) (by
          simpa [sampler] using
            evalDist_uniformCandidateSample_target signatures candidates candidate)
    _ ≤ ∑ _candidate ∈ (Finset.univ : Finset (Fin candidates)),
          ((2 ^ 122 : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro candidate _
      exact probEvent_someFewTimePatternHit_le hsignatures
    _ = candidates * ((2 ^ 122 : Nat) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem completeAndPadViews_getElem?_eq_of_some
    (limit : Nat) (options : List (Option FewTimeView))
    (values : List FewTimeView)
    (hmem : values ∈ support (completeAndPadViews limit options))
    (position : Nat) (view : FewTimeView)
    (hget : options[position]? = Option.some (Option.some view)) :
    values[position]? = Option.some view := by
  obtain ⟨completed, padding, hcomplete, _, rfl⟩ :=
    completeAndPadViews_support limit options values hmem
  have hcompleted := hcomplete.getElem?_eq_of_getElem?_eq_some position view hget
  have hlt : position < completed.length := by
    rw [hcomplete.length_eq]
    exact List.getElem?_eq_some_iff.1 hget |>.1
  rw [List.getElem?_append_left hlt]
  exact hcompleted

def finCastLEEmbedding {small large : Nat} (hle : small ≤ large) : Fin small ↪ Fin large where
  toFun := Fin.castLE hle
  inj' := by
    intro left right heq
    apply Fin.ext
    exact congrArg (fun position : Fin large => position.val) heq

noncomputable def FewTimePattern.pad {small large distinct : Nat}
    (pattern : FewTimePattern small distinct) (hle : small ≤ large) :
    FewTimePattern large distinct where
  selected := pattern.selected.map (finCastLEEmbedding hle)
  card_selected := by rw [Finset.card_map, pattern.card_selected]
  assignment := fun tree =>
    ⟨finCastLEEmbedding hle (pattern.assignment tree).1,
      Finset.mem_map.2 ⟨(pattern.assignment tree).1,
        (pattern.assignment tree).2, rfl⟩⟩

theorem FewTimePattern.pad_hit {small large distinct : Nat}
    (pattern : FewTimePattern small distinct) (hle : small ≤ large)
    (smallViews : Fin small → FewTimeView) (largeViews : Fin large → FewTimeView)
    (targetView : FewTimeView)
    (hagrees : ∀ position, position ∈ pattern.selected →
      largeViews (finCastLEEmbedding hle position) = smallViews position)
    (hhit : pattern.Hit (smallViews, targetView)) :
    (pattern.pad hle).Hit (largeViews, targetView) := by
  constructor
  · intro selected
    obtain ⟨position, hposition, heq⟩ := Finset.mem_map.1 selected.2
    have hsmall := hhit.1 (⟨position, hposition⟩ : pattern.selected)
    change (largeViews selected.1).1 = targetView.1
    rw [← heq, hagrees position hposition]
    exact hsmall
  · intro tree
    change targetView.2 tree =
      (largeViews (finCastLEEmbedding hle (pattern.assignment tree).1)).2 tree
    rw [hagrees (pattern.assignment tree).1 (pattern.assignment tree).2]
    exact hhit.2 tree

def optionListViews (options : List (Option FewTimeView)) :
    Fin options.length → FewTimeView :=
  fun position => (options.get position).getD default

def FewTimePattern.HitOptions {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct)
    (options : List (Option FewTimeView)) (hlength : options.length = signatures)
    (targetView : FewTimeView) : Prop :=
  pattern.Hit
      (fun position => optionListViews options (Fin.cast hlength.symm position), targetView)
    ∧ ∀ position, position ∈ pattern.selected →
      ∃ view, options.get (Fin.cast hlength.symm position) = some view

def SomeFewTimePatternHitOptions (signatures : Nat)
    (options : List (Option FewTimeView)) (hlength : options.length = signatures)
    (targetView : FewTimeView) : Prop :=
  ∃ distinct ∈ Finset.Icc 1 14, ∃ pattern : FewTimePattern signatures distinct,
    pattern.HitOptions options hlength targetView

noncomputable instance (signatures : Nat) (options : List (Option FewTimeView))
    (hlength : options.length = signatures) :
    DecidablePred (SomeFewTimePatternHitOptions signatures options hlength) :=
  fun _ => Classical.propDecidable _

theorem SomeFewTimePatternHitOptions.completeAndPad
    (signatures : Nat) (options : List (Option FewTimeView))
    (hlength : options.length = signatures) (targetView : FewTimeView)
    (limit : Nat) (hle : signatures ≤ limit)
    (hhit : SomeFewTimePatternHitOptions signatures options hlength targetView)
    (values : List FewTimeView)
    (hmem : values ∈ support (completeAndPadViews limit options)) :
    let hpaddedLength := completeAndPadViews_support_length limit options
      (hlength.le.trans hle) values hmem
    SomeFewTimePatternHit limit
      ((fun position => values.get (Fin.cast hpaddedLength.symm position)), targetView) := by
  dsimp only
  obtain ⟨distinct, hdistinct, pattern, hpattern, hselected⟩ := hhit
  let hpaddedLength := completeAndPadViews_support_length limit options
    (hlength.le.trans hle) values hmem
  let largeViews : Fin limit → FewTimeView :=
    fun position => values.get (Fin.cast hpaddedLength.symm position)
  let smallViews : Fin signatures → FewTimeView :=
    fun position => optionListViews options (Fin.cast hlength.symm position)
  have hagrees : ∀ position, position ∈ pattern.selected →
      largeViews (finCastLEEmbedding hle position) = smallViews position := by
    intro position hposition
    obtain ⟨view, hoption⟩ := hselected position hposition
    let optionPosition : Fin options.length := Fin.cast hlength.symm position
    have hoption0 : options.get optionPosition = Option.some view := hoption
    have hoption' : options[position.val]? = Option.some (Option.some view) := by
      have hpositionLt : position.val < options.length := by
        rw [hlength]
        exact position.isLt
      rw [List.getElem?_eq_getElem hpositionLt]
      change Option.some (options.get optionPosition) = _
      exact congrArg Option.some hoption0
    have hvalue' := completeAndPadViews_getElem?_eq_of_some limit options values hmem
      position.val view hoption'
    have hvalueLt : position.val < values.length := by
      rw [hpaddedLength]
      exact lt_of_lt_of_le position.isLt hle
    rw [List.getElem?_eq_getElem hvalueLt] at hvalue'
    have hvalue : values[position.val] = view := Option.some.inj hvalue'
    change values[position.val] = (options.get optionPosition).getD default
    rw [hvalue, hoption0]
    rfl
  exact ⟨distinct, hdistinct, pattern.pad hle,
    pattern.pad_hit hle smallViews largeViews targetView hagrees hpattern⟩

theorem SomeFewTimePatternHit.pad {small large : Nat} (hle : small ≤ large)
    (smallViews : Fin small → FewTimeView) (largeViews : Fin large → FewTimeView)
    (targetView : FewTimeView)
    (hagrees : ∀ position, largeViews (finCastLEEmbedding hle position) = smallViews position)
    (hhit : SomeFewTimePatternHit small (smallViews, targetView)) :
    SomeFewTimePatternHit large (largeViews, targetView) := by
  obtain ⟨distinct, hdistinct, pattern, hpattern⟩ := hhit
  exact ⟨distinct, hdistinct, pattern.pad hle,
    pattern.pad_hit hle smallViews largeViews targetView (fun position _ => hagrees position)
      hpattern⟩

theorem gameAfterSecretsWithViewTrace_properLeak_hitOptions
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hmem : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness) = digest)
    (hproper : ProperFewTimeLeak f result.2.cache
      (⟨parameter, result.1.1, otsSecret, ftsSecret⟩ : SecretKey)
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest)) :
    SomeFewTimePatternHitOptions result.2.trace.signing.toSigningLog.length result.2.views
      (by
        rw [← (gameAfterSecretsWithViewTrace_support_validViews adversary parameter
          otsSecret ftsSecret result hmem).length_eq]
        simp [SigningCacheTrace.toSigningLog])
      (result.2.targetView.getD default) := by
  let cover := hproper.1.cover
  let hvalid := gameAfterSecretsWithViewTrace_support_validViews adversary parameter
    otsSecret ftsSecret result hmem
  have hbase : (result.1, result.2.base) ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
      support_map]
    exact ⟨result, hmem, rfl⟩
  have hinvariants := gameAfterSecretsWithFullTrace_support_invariants adversary parameter
    otsSecret ftsSecret (result.1, result.2.base) hbase
  have htarget := gameAfterSecretsWithViewTrace_targetView_eq adversary parameter otsSecret
    ftsSecret result hmem f hf digest hdigest
  have hlength : result.2.views.length = result.2.trace.signing.toSigningLog.length := by
    rw [← hvalid.length_eq]
    simp [SigningCacheTrace.toSigningLog]
  refine ⟨cover.entries.card, Finset.mem_Icc.2
    ⟨cover.entries_card_pos, cover.entries_card_le_trees⟩, cover.pattern, ?_, ?_⟩
  · have hhit := cover.viewedPatternHit result.2 rfl hvalid hinvariants.2.1 hf
    rw [htarget]
    change cover.pattern.Hit
      ((fun position => optionListViews result.2.views (Fin.cast hlength.symm position)),
        fewTimeTargetView (digestIndex digest) (digestLeaves digest))
    have hfunctions :
        (fun position => optionListViews result.2.views (Fin.cast hlength.symm position)) =
          hvalid.signingViewsForLog rfl := by
      funext position
      rfl
    rw [hfunctions]
    exact hhit
  · intro position hposition
    obtain ⟨entry, _, hentry⟩ := Finset.mem_image.1 hposition
    refine ⟨cover.entryView entry, ?_⟩
    have hoption := cover.signingOptionViews_traceIndex_eq_entryView result.2 rfl hvalid
      hinvariants.2.1 hf entry
    change hvalid.signingOptionViewsForLog rfl position = some (cover.entryView entry)
    rw [← hentry]
    change hvalid.signingOptionViews
      (cover.traceIndex result.2.trace.signing rfl entry) = some (cover.entryView entry)
    exact hoption

theorem gameAfterSecretsWithPaddedViews_properLeak_patternHit
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : ((Digest × Forgery × Bool) × ViewedFullTraceState) ×
      ((Fin signatureLimit → FewTimeView) × FewTimeView))
    (hmem : result ∈ support
      (gameAfterSecretsWithPaddedViews adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.1.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter result.1.1.1 result.1.1.2.1.message
        result.1.1.2.1.signature.randomness) = digest)
    (hvalidTranscript : SigningTranscript.Valid result.1.2.trace.signing.toSigningLog)
    (hproper : ProperFewTimeLeak f result.1.2.cache
      (⟨parameter, result.1.1.1, otsSecret, ftsSecret⟩ : SecretKey)
      result.1.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest)) :
    SomeFewTimePatternHit signatureLimit result.2 := by
  obtain ⟨values, hviewed, hvalues, hresultViews, hresultTarget⟩ :=
    gameAfterSecretsWithPaddedViews_support adversary parameter otsSecret ftsSecret result hmem
  have htarget := gameAfterSecretsWithViewTrace_targetView_eq adversary parameter otsSecret
    ftsSecret result.1 hviewed f hf digest hdigest
  have hpaddedTarget : result.2.2 =
      fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
    rw [htarget] at hresultTarget
    exact completeOptionView_support_some _ _ hresultTarget
  have hhitOptions := gameAfterSecretsWithViewTrace_properLeak_hitOptions adversary parameter
    otsSecret ftsSecret result.1 hviewed f hf digest hdigest hproper
  have htargetGetD : result.1.2.targetView.getD default =
      fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
    rw [htarget]
    rfl
  rw [htargetGetD] at hhitOptions
  have hviewLength := gameAfterSecretsWithViewTrace_support_validViews adversary parameter
    otsSecret ftsSecret result.1 hviewed |>.length_eq
  have hoptionsLength : result.1.2.views.length =
      result.1.2.trace.signing.toSigningLog.length := by
    rw [← hviewLength]
    simp [SigningCacheTrace.toSigningLog]
  have hle : result.1.2.trace.signing.toSigningLog.length ≤ signatureLimit :=
    hvalidTranscript
  have hhit := hhitOptions.completeAndPad
    result.1.2.trace.signing.toSigningLog.length result.1.2.views hoptionsLength
    (fewTimeTargetView (digestIndex digest) (digestLeaves digest)) signatureLimit hle
    values hvalues
  have hpaddedLength := completeAndPadViews_support_length signatureLimit result.1.2.views
    (hoptionsLength.le.trans hle) values hvalues
  change SomeFewTimePatternHit signatureLimit (result.2.1, result.2.2)
  rw [hresultViews, hpaddedTarget]
  rw [listToFunction_eq_get_of_length values hpaddedLength]
  exact hhit

end SphincsSecurity.Concrete
