import SphincsSecurity.Proof.Bytes

/-!
# One guess

A fresh oracle answer, truncated to the digest length, hits a fixed target with probability at most
`2 ^ -n`. Every per-query bound in the development is an instance of this: the adversary picks the
tweak and so the position, domain separation fixes the target, and this bounds what the answer buys.
-/

namespace SphincsSecurity

open OracleComp ENNReal

/-- Truncation loses the high half, and nothing else: two answers with the same truncation and the
same high half are the same answer. -/
theorem hashOutput_eq_of_halves {x y : HashOutput} (hlow : truncateHash x = truncateHash y)
    (hhigh : x.extractLsb' digestBits digestBits = y.extractLsb' digestBits digestBits) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < digestBits
  · have := congrArg (fun b : Digest => b.getLsbD i) hlow
    simpa [truncateHash, BitVec.getLsbD_extractLsb', hlt] using this
  · have hshift : i - digestBits < digestBits := by
      simp only [digestBits, hashOutputBits] at hi hlt ⊢
      omega
    have := congrArg (fun b : Digest => b.getLsbD (i - digestBits)) hhigh
    simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
    rwa [show digestBits + (i - digestBits) = i by omega] at this

/-- **One guess.** A uniform answer truncated to the digest length hits a fixed target with
probability at most `2 ^ -n`. -/
theorem probOutput_truncateHash_le (target : Digest) :
    Pr[= target | (truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput))]
      ≤ ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  set fiber := Finset.univ.filter fun output : HashOutput => target = truncateHash output with hfiber
  have hcard : fiber.card ≤ 2 ^ digestBits := by
    have hinj : Set.InjOn (fun output : HashOutput => output.extractLsb' digestBits digestBits)
        fiber := by
      intro x hx y hy hxy
      simp only [hfiber, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx hy
      exact hashOutput_eq_of_halves (by rw [← hx, ← hy]) hxy
    calc fiber.card ≤ (Finset.univ : Finset Digest).card :=
          Finset.card_le_card_of_injOn _ (by simp) hinj
      _ = 2 ^ digestBits := by simp
  have hexp : hashOutputBits = digestBits + digestBits := by norm_num [hashOutputBits, digestBits]
  have hsplit : ((Fintype.card HashOutput : ℝ≥0∞))
      = ((2 ^ digestBits : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
    rw [show Fintype.card HashOutput = 2 ^ hashOutputBits from card_bitVec hashOutputBits, hexp,
      pow_add]
    push_cast
    ring
  have hne : ((2 ^ digestBits : Nat) : ℝ≥0∞) ≠ 0 := by positivity
  have htop : ((2 ^ digestBits : Nat) : ℝ≥0∞) ≠ ⊤ := by simp
  rw [probOutput_map_eq_sum_fintype_ite]
  simp only [probOutput_uniformSample]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← hfiber, hsplit,
    ENNReal.mul_inv (Or.inl hne) (Or.inl htop)]
  calc (fiber.card : ℝ≥0∞) * (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
      = ((fiber.card : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
          * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by ring
    _ ≤ 1 * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
        refine mul_le_mul_left ?_ _
        calc (fiber.card : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
            ≤ ((2 ^ digestBits : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
              mul_le_mul_left (by exact_mod_cast hcard) _
          _ = 1 := ENNReal.mul_inv_cancel hne htop
    _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := one_mul _

/-! ### The same, at any width

The digest's index is the low `h` bits of an oracle answer, and the leak argument needs it to be
near-uniform. That is the fiber count above at a different width, so it is worth having once.
-/

theorem hashOutput_eq_of_extract {width : Nat} (hwidth : width ≤ hashOutputBits) {x y : HashOutput}
    (hlow : x.extractLsb' 0 width = y.extractLsb' 0 width)
    (hhigh : x.extractLsb' width (hashOutputBits - width)
      = y.extractLsb' width (hashOutputBits - width)) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < width
  · have := congrArg (fun b : BitVec width => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hlt] using this
  · have hshift : i - width < hashOutputBits - width := by omega
    have := congrArg (fun b : BitVec (hashOutputBits - width) => b.getLsbD (i - width)) hhigh
    simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
    rwa [show width + (i - width) = i by omega] at this

/-- **One guess, at any width.** A uniform answer's low `width` bits hit a fixed target with
probability at most `2 ^ -width`. -/
theorem probOutput_extract_le {width : Nat} (hwidth : width ≤ hashOutputBits)
    (target : BitVec width) :
    Pr[= target | ((fun output : HashOutput => output.extractLsb' 0 width)
        <$> ($ᵗ HashOutput : ProbComp HashOutput))]
      ≤ ((2 ^ width : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  set fiber := Finset.univ.filter fun output : HashOutput => target = output.extractLsb' 0 width
    with hfiber
  have hcard : fiber.card ≤ 2 ^ (hashOutputBits - width) := by
    have hinj : Set.InjOn
        (fun output : HashOutput => output.extractLsb' width (hashOutputBits - width)) fiber := by
      intro x hx y hy hxy
      simp only [hfiber, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx hy
      exact hashOutput_eq_of_extract hwidth (by rw [← hx, ← hy]) hxy
    calc fiber.card ≤ (Finset.univ : Finset (BitVec (hashOutputBits - width))).card :=
          Finset.card_le_card_of_injOn _ (by simp) hinj
      _ = 2 ^ (hashOutputBits - width) := by simp
  obtain ⟨rest, hrest⟩ : ∃ rest, hashOutputBits = width + rest := ⟨hashOutputBits - width, by omega⟩
  have hrest' : hashOutputBits - width = rest := by omega
  rw [hrest'] at hcard
  have hsplit : ((Fintype.card HashOutput : ℝ≥0∞))
      = ((2 ^ width : Nat) : ℝ≥0∞) * ((2 ^ rest : Nat) : ℝ≥0∞) := by
    rw [show Fintype.card HashOutput = 2 ^ hashOutputBits from card_bitVec hashOutputBits, hrest,
      pow_add]
    push_cast
    ring
  have hne : ((2 ^ width : Nat) : ℝ≥0∞) ≠ 0 := by positivity
  have htop : ((2 ^ width : Nat) : ℝ≥0∞) ≠ ⊤ := by simp
  have hne' : ((2 ^ rest : Nat) : ℝ≥0∞) ≠ 0 := by positivity
  have htop' : ((2 ^ rest : Nat) : ℝ≥0∞) ≠ ⊤ := by simp
  rw [probOutput_map_eq_sum_fintype_ite]
  simp only [probOutput_uniformSample]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← hfiber, hsplit,
    ENNReal.mul_inv (Or.inl hne) (Or.inl htop)]
  calc (fiber.card : ℝ≥0∞)
        * (((2 ^ width : Nat) : ℝ≥0∞)⁻¹ * ((2 ^ rest : Nat) : ℝ≥0∞)⁻¹)
      = ((fiber.card : ℝ≥0∞) * ((2 ^ rest : Nat) : ℝ≥0∞)⁻¹)
          * ((2 ^ width : Nat) : ℝ≥0∞)⁻¹ := by ring
    _ ≤ 1 * ((2 ^ width : Nat) : ℝ≥0∞)⁻¹ := by
        refine mul_le_mul_left ?_ _
        calc (fiber.card : ℝ≥0∞) * ((2 ^ rest : Nat) : ℝ≥0∞)⁻¹
            ≤ ((2 ^ rest : Nat) : ℝ≥0∞)
                * ((2 ^ rest : Nat) : ℝ≥0∞)⁻¹ :=
              mul_le_mul_left (by exact_mod_cast hcard) _
          _ = 1 := ENNReal.mul_inv_cancel hne' htop'
    _ = ((2 ^ width : Nat) : ℝ≥0∞)⁻¹ := one_mul _

/-- The digest's index is the low `h` bits of the answer, the truncation to `h + k * a` bits having
kept them. -/
theorem digestIndex_truncate (output : HashOutput) :
    Concrete.digestIndex (truncateMessageDigest output)
      = (output.extractLsb' 0 totalHeight).toFin := by
  rw [Concrete.digestIndex, truncateMessageDigest]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hlt : i < messageDigestBits := by
    have h1 : totalHeight = 26 := rfl
    have h2 : messageDigestBits = 176 := rfl
    omega
  simp [BitVec.getLsbD_extractLsb', hlt]

/-- **The index a fresh digest selects.** It hits a fixed index with probability at most `2^-h`,
which is what the few-time leak is counted against. -/
theorem probOutput_digestIndex_le (target : Index) :
    Pr[= target | ((fun output : HashOutput => Concrete.digestIndex (truncateMessageDigest output))
        <$> ($ᵗ HashOutput : ProbComp HashOutput))]
      ≤ ((2 ^ totalHeight : Nat) : ℝ≥0∞)⁻¹ := by
  have hwidth : totalHeight ≤ hashOutputBits := by decide
  have hmap : ((fun output : HashOutput => Concrete.digestIndex (truncateMessageDigest output))
      <$> ($ᵗ HashOutput : ProbComp HashOutput))
      = (fun output : HashOutput => (output.extractLsb' 0 totalHeight).toFin)
        <$> ($ᵗ HashOutput : ProbComp HashOutput) := by
    congr 1
    funext output
    exact digestIndex_truncate output
  have hevent : ∀ x : BitVec totalHeight, (x.toFin = target) ↔ (x = BitVec.ofFin target) := by
    intro x
    constructor
    · intro h; rw [show x = BitVec.ofFin x.toFin from rfl, h]
    · intro h; rw [h]
  rw [hmap, probOutput_map,
    show (fun output : HashOutput => (output.extractLsb' 0 totalHeight).toFin = target)
      = (fun output : HashOutput => output.extractLsb' 0 totalHeight = BitVec.ofFin target) from by
        funext output
        simp only [eq_iff_iff]
        exact hevent _,
    ← probOutput_map]
  exact probOutput_extract_le hwidth (BitVec.ofFin target)

end SphincsSecurity
