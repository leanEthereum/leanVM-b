import SphincsSecurity.Proof.OtsProbePrivateValueFirstAccess

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private theorem probEvent_bind_return (computation : ProbComp α) (f : α → β) (event : β → Prop) :
    Pr[event | computation >>= fun value => pure (f value)] = Pr[fun value => event (f value) | computation] :=
  probEvent_bind_pure_comp computation f event

noncomputable def filteredPrivateGuess (allowed : HashOutput → Prop)
    (run : HashOutput → ProbComp (Option Digest)) : ProbComp (HashOutput × Option Digest) := do
  let output ← LazyRevealProbe.sampleHashOutput
  if allowed output then
    let candidate ← run output
    pure (output, candidate)
  else pure (output, none)

theorem probEvent_uniform_private_guess_eq (common : ProbComp (Option Digest)) :
    Pr[fun pair : HashOutput × Option Digest => pair.2 = some (truncateHash pair.1) | do
      let output ← LazyRevealProbe.sampleHashOutput
      let candidate ← common
      pure (output, candidate)] =
      Pr[fun candidate => candidate ≠ none | common] * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (OracleComp.DeferredSampling.evalDist_bind_comm _ _ _)]
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro candidate
  cases candidate with
  | none => simp
  | some digest =>
      rw [probEvent_bind_return]
      simp only [Option.some.injEq]
      congr 1
      simpa only [LazyRevealProbe.sampleHashOutput, eq_comm] using SphincsSecurity.probEvent_uniform_truncateHash_eq digest

theorem probEvent_filteredPrivateGuess_hit_le_common
    (allowed : HashOutput → Prop) (run : HashOutput → ProbComp (Option Digest)) (common : ProbComp (Option Digest))
    (hsame : ∀ output, allowed output → evalDist (run output) = evalDist common) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) | filteredPrivateGuess allowed run] ≤
      Pr[fun candidate => candidate ≠ none | common] * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [← probEvent_uniform_private_guess_eq common]
  unfold filteredPrivateGuess
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro output
  by_cases hallowed : allowed output
  · rw [if_pos hallowed, probEvent_bind_return, probEvent_bind_return]
    exact le_of_eq (congrArg (fun probability => Pr[= output | LazyRevealProbe.sampleHashOutput] * probability)
      (probEvent_congr' (fun _ _ => Iff.rfl) (hsame output hallowed)))
  · simp [hallowed]

theorem probEvent_filteredPrivateGuess_hasCandidate_eq
    (allowed : HashOutput → Prop) (run : HashOutput → ProbComp (Option Digest)) (common : ProbComp (Option Digest))
    (hsame : ∀ output, allowed output → evalDist (run output) = evalDist common) :
    Pr[fun pair => pair.2 ≠ none | filteredPrivateGuess allowed run] =
      Pr[allowed | LazyRevealProbe.sampleHashOutput] * Pr[fun candidate => candidate ≠ none | common] := by
  unfold filteredPrivateGuess
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro output
  by_cases hallowed : allowed output
  · rw [if_pos hallowed, if_pos hallowed, probEvent_bind_return]
    exact congrArg (fun probability => Pr[= output | LazyRevealProbe.sampleHashOutput] * probability)
      (probEvent_congr' (fun _ _ => Iff.rfl) (hsame output hallowed))
  · simp [hallowed]

theorem probEvent_filteredPrivateGuess_hit_le_four_thirds
    (allowed : HashOutput → Prop) (run : HashOutput → ProbComp (Option Digest)) (common : ProbComp (Option Digest))
    (hsame : ∀ output, allowed output → evalDist (run output) = evalDist common)
    (hgood : (3 / 4 : ENNReal) ≤ Pr[allowed | LazyRevealProbe.sampleHashOutput]) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) | filteredPrivateGuess allowed run] ≤
      Pr[fun pair => pair.2 ≠ none | filteredPrivateGuess allowed run] *
        ((4 / 3 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) := by
  rw [probEvent_filteredPrivateGuess_hasCandidate_eq allowed run common hsame]
  apply (probEvent_filteredPrivateGuess_hit_le_common allowed run common hsame).trans
  calc
    _ = ((3 / 4 : ENNReal) * Pr[fun candidate => candidate ≠ none | common]) *
        ((4 / 3 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) := by
      have hfactor : (3 / 4 : ENNReal) * (4 / 3) = 1 := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
      calc
        _ = ((3 / 4 : ENNReal) * (4 / 3)) *
            (Pr[fun candidate => candidate ≠ none | common] * (Fintype.card Digest : ENNReal)⁻¹) := by rw [hfactor, one_mul]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul' (mul_le_mul' hgood le_rfl) le_rfl

theorem probEvent_no_private_pendingHit_ge_three_quarters
    (context : DeferredContext) (target : Position) (hcard : context.state.pending.card ≤ 2 ^ 126) :
    (3 / 4 : ENNReal) ≤ Pr[fun output => ¬context.state.hitAt (.position target) output | LazyRevealProbe.sampleHashOutput] := by
  have hquarter : Pr[context.state.hitAt (.position target) | LazyRevealProbe.sampleHashOutput] ≤ (1 / 4 : ENNReal) := by
    apply (LazyRevealProbe.probEvent_sampleHashOutput_hitAt_le context.state (.position target)).trans
    have htargetCard : (context.state.pendingAt (.position target)).card ≤ 2 ^ 126 := by
      have := context.state.pendingAway_card_add_pendingAt_card_le (.position target)
      omega
    calc
      _ ≤ ((2 ^ 126 : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
        mul_le_mul' (Nat.cast_le.mpr htargetCard) le_rfl
      _ = _ := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, digestBits]
  have hdouble : Pr[fun output => ¬¬context.state.hitAt (.position target) output | LazyRevealProbe.sampleHashOutput] ≤
      (1 / 4 : ENNReal) := by simpa only [not_not] using hquarter
  have hgood := probEvent_one_sub_le_of_compl_le (by simp : Pr[⊥ | LazyRevealProbe.sampleHashOutput] = 0) hdouble
  have hsum : (1 : ENNReal) ≤
      Pr[fun output => ¬context.state.hitAt (.position target) output | LazyRevealProbe.sampleHashOutput] + 1 / 4 :=
    tsub_le_iff_right.mp hgood
  have hreal := (ENNReal.toReal_le_toReal (by finiteness)
    (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, by finiteness⟩)).mpr hsum
  apply (ENNReal.toReal_le_toReal (by finiteness) probEvent_ne_top).mp
  rw [ENNReal.toReal_add probEvent_ne_top (by finiteness)] at hreal
  norm_num [ENNReal.toReal_div] at hreal ⊢
  linarith

theorem sampledPrivatePositionFirstCandidate_eq_filtered
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    sampledPrivatePositionFirstCandidate target computation context fuel table =
      filteredPrivateGuess (fun output => ¬context.state.hitAt (.position target) output)
        (privatePositionFirstCandidate target computation context fuel table) := by
  unfold sampledPrivatePositionFirstCandidate filteredPrivateGuess
  apply bind_congr
  intro output
  by_cases hhit : context.state.hitAt (.position target) output <;> simp [hhit]

theorem probEvent_sampledPrivatePositionFirstCandidate_hit_le_four_thirds
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : context.state.values (.position target) = none) (hcard : context.state.pending.card ≤ 2 ^ 126) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) |
      sampledPrivatePositionFirstCandidate target computation context fuel table] ≤
      Pr[fun pair => pair.2 ≠ none | sampledPrivatePositionFirstCandidate target computation context fuel table] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  have hsmall : context.state.pending.card < Fintype.card Digest :=
    hcard.trans_lt (by norm_num [digestBits])
  obtain ⟨digest, hmiss⟩ := exists_digest_not_mem_pendingAt context.state (.position target) hsmall
  let reference := hashOutputOfDigest digest
  have hclean : ¬context.state.hitAt (.position target) reference := by
    simpa only [LazyRevealProbe.State.hitAt, reference, truncateHash_hashOutputOfDigest] using hmiss
  rw [sampledPrivatePositionFirstCandidate_eq_filtered]
  simpa only [show Fintype.card Digest = 2 ^ digestBits by simp] using
    probEvent_filteredPrivateGuess_hit_le_four_thirds
      (fun output => ¬context.state.hitAt (.position target) output)
      (privatePositionFirstCandidate target computation context fuel table)
      (privatePositionFirstCandidate target computation context fuel table reference)
      (fun output houtput => evalDist_privatePositionFirstCandidate_eq target computation context fuel table
        output reference hstate houtput hclean)
      (probEvent_no_private_pendingHit_ge_three_quarters context target hcard)

theorem probEvent_sampledPrivatePositionFirstCandidate_hit_le_of_no_pending
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : context.state.values (.position target) = none)
    (hpending : context.state.pendingAt (.position target) = ∅) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) |
      sampledPrivatePositionFirstCandidate target computation context fuel table] ≤
      Pr[fun pair => pair.2 ≠ none | sampledPrivatePositionFirstCandidate target computation context fuel table] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let allowed := fun output => ¬context.state.hitAt (.position target) output
  let run := privatePositionFirstCandidate target computation context fuel table
  have hclean (output : HashOutput) : allowed output := by
    simp [allowed, LazyRevealProbe.State.hitAt, hpending]
  have hsame : ∀ output, allowed output → evalDist (run output) = evalDist (run 0) := by
    intro output _
    exact evalDist_privatePositionFirstCandidate_eq target computation context fuel table output 0 hstate
      (hclean output) (hclean 0)
  have hgood : Pr[allowed | LazyRevealProbe.sampleHashOutput] = 1 := by
    simp [allowed, LazyRevealProbe.State.hitAt, hpending]
  have hgate := probEvent_filteredPrivateGuess_hasCandidate_eq allowed run (run 0) hsame
  rw [hgood, one_mul] at hgate
  rw [sampledPrivatePositionFirstCandidate_eq_filtered]
  change Pr[fun pair => pair.2 = some (truncateHash pair.1) | filteredPrivateGuess allowed run] ≤
    Pr[fun pair => pair.2 ≠ none | filteredPrivateGuess allowed run] * _
  rw [hgate]
  simpa only [show Fintype.card Digest = 2 ^ digestBits by simp] using
    probEvent_filteredPrivateGuess_hit_le_common allowed run (run 0) hsame

end SphincsSecurity.Concrete.OtsProbeSimulation
