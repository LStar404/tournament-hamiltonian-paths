import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace TournamentHamiltonian

open scoped BigOperators

def compressedDegreeSequences (j b : ℕ) : Finset (Fin b → ℕ) :=
  (Finset.Nat.antidiagonalTuple b (2 * (b + j))).filter (fun d => ∀ i, 3 ≤ d i)

theorem mem_compressedDegreeSequences {j b : ℕ} {d : Fin b → ℕ} :
    d ∈ compressedDegreeSequences j b ↔ (∑ i, d i) = 2 * (b + j) ∧ ∀ i, 3 ≤ d i := by
  simp [compressedDegreeSequences, Finset.Nat.mem_antidiagonalTuple]

def compressedDegreeComposition {j b : ℕ} (d : compressedDegreeSequences j b) :
    Composition (2 * j) where
  blocks := List.ofFn (fun i => d.val i - 2)
  blocks_pos := by
    intro k hk
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
    have h := (mem_compressedDegreeSequences.mp d.property).2 i
    omega
  blocks_sum := by
    rw [List.sum_ofFn]
    rw [Finset.sum_tsub_distrib _ (fun i _ =>
      (show 2 ≤ d.val i from (by have h := (mem_compressedDegreeSequences.mp d.property).2 i; omega)))]
    rw [(mem_compressedDegreeSequences.mp d.property).1]
    simp
    omega

theorem compressedDegreeComposition_injective (j b : ℕ) :
    Function.Injective (compressedDegreeComposition (j := j) (b := b)) := by
  intro d e h
  have hblocks := congrArg Composition.blocks h
  have hf := List.ofFn_injective hblocks
  apply Subtype.ext
  funext i
  have hd := (mem_compressedDegreeSequences.mp d.property).2 i
  have he := (mem_compressedDegreeSequences.mp e.property).2 i
  have hi := congrFun hf i
  omega

theorem compressedDegreeSequences_card_le (j b : ℕ) :
    (compressedDegreeSequences j b).card ≤ 4 ^ j := by
  have hc := Fintype.card_le_of_injective _ (compressedDegreeComposition_injective j b)
  rw [Fintype.card_coe, composition_card] at hc
  calc
    _ ≤ 2 ^ (2 * j - 1) := hc
    _ ≤ 2 ^ (2 * j) := Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    _ = 4 ^ j := by rw [pow_mul]; norm_num

noncomputable def compressedDegreeCompensation (j b : ℕ) : ℝ :=
  (2 : ℝ) ^ b / (b.factorial : ℝ) *
    ((2 * (b + j)).factorial : ℝ) / ((2 : ℝ) ^ (b + j) * ((b + j).factorial : ℝ)) *
      ∑ d ∈ compressedDegreeSequences j b, ∏ i, (d i : ℝ)⁻¹

noncomputable def compressedActivityMajorant (j : ℕ) (W : ℝ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 (2 * j), compressedDegreeCompensation j b * W ^ (b + j)

def pairingProduct (e : ℕ) : ℕ := ∏ i ∈ Finset.range e, (2 * i + 1)

theorem pairingProduct_factorial (e : ℕ) :
    (2 * e).factorial = 2 ^ e * e.factorial * pairingProduct e := by
  induction e with
  | zero => simp [pairingProduct]
  | succ e ih =>
    rw [show 2 * (e + 1) = 2 * e + 1 + 1 by omega, Nat.factorial_succ,
      Nat.factorial_succ, ih, Nat.factorial_succ, pow_succ]
    simp only [pairingProduct, Finset.prod_range_succ]
    ring

theorem pairing_factorial_ratio_eq (e : ℕ) :
    ((2 * e).factorial : ℝ) / ((2 : ℝ) ^ e * (e.factorial : ℝ)) = pairingProduct e := by
  rw [pairingProduct_factorial]
  push_cast
  have hf : (e.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hf]

theorem pairingProduct_le (j b : ℕ) (hb : b ≤ 2 * j) :
    pairingProduct (b + j) ≤ (6 * j) ^ (b + j) := by
  unfold pairingProduct
  calc
    _ ≤ ∏ _i ∈ Finset.range (b + j), (6 * j) := by
      apply Finset.prod_le_prod
      intro i hi
      have h := Finset.mem_range.mp hi
      omega
    _ = _ := by simp

theorem compressed_degree_inverse_sum_le (j b : ℕ) :
    (∑ d ∈ compressedDegreeSequences j b, ∏ i, (d i : ℝ)⁻¹) ≤
      (4 : ℝ) ^ j * (3 : ℝ)⁻¹ ^ b := by
  have hentry (d : Fin b → ℕ) (hd : d ∈ compressedDegreeSequences j b) :
      (∏ i, (d i : ℝ)⁻¹) ≤ (3 : ℝ)⁻¹ ^ b := by
    calc
      _ ≤ ∏ _i : Fin b, (3 : ℝ)⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro i _; positivity
        · intro i _
          have h : (3 : ℝ) ≤ d i := by exact_mod_cast (mem_compressedDegreeSequences.mp hd).2 i
          exact inv_le_inv₀ (by positivity) (by linarith) |>.mpr h
      _ = _ := by simp
  have h := Finset.sum_le_sum hentry
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  have hc : ((compressedDegreeSequences j b).card : ℝ) ≤ (4 : ℝ) ^ j := by
    exact_mod_cast compressedDegreeSequences_card_le j b
  exact h.trans (mul_le_mul_of_nonneg_right hc (by positivity))

theorem compressedDegreeCompensation_nonneg (j b : ℕ) :
    0 ≤ compressedDegreeCompensation j b := by
  unfold compressedDegreeCompensation
  positivity

theorem compressedDegreeCompensation_le (j b : ℕ) (hb : b ≤ 2 * j) :
    compressedDegreeCompensation j b ≤ (24 * (j : ℝ)) ^ j *
      (4 * (j : ℝ)) ^ b / (b.factorial : ℝ) := by
  have hp : (pairingProduct (b + j) : ℝ) ≤ (6 * (j : ℝ)) ^ (b + j) := by
    exact_mod_cast pairingProduct_le j b hb
  have hd := compressed_degree_inverse_sum_le j b
  have heq : compressedDegreeCompensation j b =
      ((2 : ℝ) ^ b / (b.factorial : ℝ)) * (pairingProduct (b + j) : ℝ) *
        ∑ d ∈ compressedDegreeSequences j b, ∏ i, (d i : ℝ)⁻¹ := by
    unfold compressedDegreeCompensation
    rw [← pairing_factorial_ratio_eq]
    ring
  rw [heq]
  have hmul := mul_le_mul hp hd (by positivity : 0 ≤ ∑ d ∈ compressedDegreeSequences j b,
    ∏ i, (d i : ℝ)⁻¹) (by positivity : 0 ≤ (6 * (j : ℝ)) ^ (b + j))
  have h := mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ (2 : ℝ) ^ b / (b.factorial : ℝ))
  have h' : ((2 : ℝ) ^ b / (b.factorial : ℝ)) * (pairingProduct (b + j) : ℝ) *
      (∑ d ∈ compressedDegreeSequences j b, ∏ i, (d i : ℝ)⁻¹) ≤
        ((2 : ℝ) ^ b / (b.factorial : ℝ)) * (6 * (j : ℝ)) ^ (b + j) *
          ((4 : ℝ) ^ j * (3 : ℝ)⁻¹ ^ b) := by simpa only [mul_assoc] using h
  apply h'.trans_eq
  rw [pow_add, mul_pow, mul_pow, mul_pow]
  have hf : (b.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hf]
  have hbpow : (3 : ℝ)⁻¹ ^ b * 2 ^ b * 6 ^ b = (4 : ℝ) ^ b := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  have hjpow : (4 : ℝ) ^ j * 6 ^ j = (24 : ℝ) ^ j := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (j : ℝ) ^ b * ((3 : ℝ)⁻¹ ^ b * 2 ^ b * 6 ^ b) * (4 ^ j * 6 ^ j) := by ring
    _ = _ := by rw [hbpow, hjpow]; ring

theorem scaled_finite_exponential_sum_le (M : ℕ) (a x : ℝ)
    (ha : 1 ≤ a) (hx : 0 ≤ x) :
    (∑ b ∈ Finset.Icc 1 M, (a * x) ^ b / (b.factorial : ℝ)) ≤
      a ^ M * Real.exp x := by
  calc
    _ ≤ ∑ b ∈ Finset.Icc 1 M, a ^ M * (x ^ b / (b.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro b hb
      have hbM := (Finset.mem_Icc.mp hb).2
      calc
        _ = a ^ b * (x ^ b / (b.factorial : ℝ)) := by rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ha hbM) (by positivity)
    _ = a ^ M * ∑ b ∈ Finset.Icc 1 M, x ^ b / (b.factorial : ℝ) := by rw [Finset.mul_sum]
    _ ≤ a ^ M * ∑ b ∈ Finset.range (M + 1), x ^ b / (b.factorial : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro b hb
        simp only [Finset.mem_Icc, Finset.mem_range] at hb ⊢
        omega
      · intro b _ _; positivity
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx _) (by positivity)

theorem compressedActivityMajorant_le (j : ℕ) (W : ℝ) (hW : 1 ≤ W) :
    compressedActivityMajorant j W ≤ (710 * W ^ 3 * (j : ℝ)) ^ j := by
  have hW0 : 0 ≤ W := by linarith
  have hsum : compressedActivityMajorant j W ≤
      (24 * (j : ℝ) * W) ^ j *
        ∑ b ∈ Finset.Icc 1 (2 * j), (4 * (j : ℝ) * W) ^ b / (b.factorial : ℝ) := by
    unfold compressedActivityMajorant
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hu := mul_le_mul_of_nonneg_right
      (compressedDegreeCompensation_le j b (Finset.mem_Icc.mp hb).2) (pow_nonneg hW0 (b + j))
    apply hu.trans_eq
    rw [pow_add, mul_pow, mul_pow]
    ring
  have haux := scaled_finite_exponential_sum_le (2 * j) (2 * W) (2 * (j : ℝ))
    (by linarith) (by positivity)
  have heq : (2 * W) * (2 * (j : ℝ)) = 4 * (j : ℝ) * W := by ring
  rw [heq] at haux
  have hm := mul_le_mul_of_nonneg_left haux (by positivity : 0 ≤ (24 * (j : ℝ) * W) ^ j)
  have htotal := hsum.trans hm
  have he : Real.exp 1 ≤ 87 / 32 := by
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hnum : 96 * Real.exp 1 ^ 2 ≤ (710 : ℝ) := by
    nlinarith [Real.exp_pos 1]
  have hbase : 96 * Real.exp 1 ^ 2 * W ^ 3 * (j : ℝ) ≤ 710 * W ^ 3 * (j : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnum (by positivity)) (by positivity)
  have hnorm : (24 * (j : ℝ) * W) ^ j * ((2 * W) ^ (2 * j) * Real.exp (2 * (j : ℝ))) =
      (96 * Real.exp 1 ^ 2 * W ^ 3 * (j : ℝ)) ^ j := by
    have hexp : Real.exp (2 * (j : ℝ)) = Real.exp 1 ^ (2 * j) := by
      rw [← Real.exp_nat_mul]
      push_cast
      congr 1
      ring
    rw [hexp, pow_mul, pow_mul, ← mul_pow, ← mul_pow]
    congr 1
    ring
  exact htotal.trans (hnorm.le.trans (pow_le_pow_left₀ (by positivity) hbase j))

theorem compressedDegreeCompensation_one_one : compressedDegreeCompensation 1 1 = 3 / 2 := by
  have hd : compressedDegreeSequences 1 1 = {![4]} := by decide
  norm_num [compressedDegreeCompensation, hd, Fin.prod_univ_one]

theorem compressedDegreeCompensation_one_two : compressedDegreeCompensation 1 2 = 10 / 3 := by
  have hd : compressedDegreeSequences 1 2 = {![3, 3]} := by decide
  norm_num [compressedDegreeCompensation, hd, Fin.prod_univ_two]

theorem compressedActivityMajorant_one (W : ℝ) :
    compressedActivityMajorant 1 W = (3 / 2) * W ^ 2 + (10 / 3) * W ^ 3 := by
  have hi : Finset.Icc 1 (2 * 1) = ({1, 2} : Finset ℕ) := by decide
  simp only [compressedActivityMajorant, hi, Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, Nat.reduceEqDiff, not_false_eq_true,
    compressedDegreeCompensation_one_one, compressedDegreeCompensation_one_two]

end TournamentHamiltonian
