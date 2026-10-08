import TournamentHamiltonian.PreconditioningMarginals

/-! Total displacement of the actual paired score weights. -/
namespace TournamentHamiltonian
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem sum_abs_le_sqrt_card_mul_sq (b : ι → ℝ) :
    (∑ i, |b i|) ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, b i ^ 2) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ => (1 : ℝ)) (fun i => |b i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sq_abs] at hc
  have h := Real.sqrt_le_sqrt hc
  rw [Real.sqrt_sq (Finset.sum_nonneg (fun i _ => abs_nonneg _))] at h
  exact h

theorem pairedLeft_total_displacement_le (a : ι → ℝ) (a0 : ℝ) (h1 : a0 < 1)
    (ha : ∀ i, |a i| ≤ a0) :
    (∑ i, |pairedLeft (a i) - 1|) ≤
      Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, a i ^ 2) / (1 - a0) := by
  have hg : 0 < 1 - a0 := by linarith
  apply (sum_abs_le_sqrt_card_mul_sq (fun i => pairedLeft (a i) - 1)).trans
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => pairedLeft_sub_one_sq_le (a i) a0 h1 (ha i))
  rw [← Finset.sum_div] at hs
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (Fintype.card ι : ℝ))
  have hh := Real.sqrt_le_sqrt hm
  convert hh using 1
  rw [← mul_div_assoc, Real.sqrt_div (by positivity), Real.sqrt_sq hg.le]

theorem pairedRight_total_displacement_le (a : ι → ℝ) (a0 : ℝ) (h1 : a0 < 1)
    (ha : ∀ i, |a i| ≤ a0) :
    (∑ i, |pairedRight (a i) - 1|) ≤
      Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, a i ^ 2) / (1 - a0) := by
  have hg : 0 < 1 - a0 := by linarith
  apply (sum_abs_le_sqrt_card_mul_sq (fun i => pairedRight (a i) - 1)).trans
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => pairedRight_sub_one_sq_le (a i) a0 h1 (ha i))
  rw [← Finset.sum_div] at hs
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (Fintype.card ι : ℝ))
  have hh := Real.sqrt_le_sqrt hm
  convert hh using 1
  rw [← mul_div_assoc, Real.sqrt_div (by positivity), Real.sqrt_sq hg.le]

omit [Fintype ι] in
theorem sqrt_mul_eq_mul_sqrt_div (N tau : ℝ) (hN : 0 ≤ N) (ht : 0 ≤ tau) :
    Real.sqrt (N * tau) = N * Real.sqrt (tau / N) := by
  by_cases hN0 : N = 0
  · simp [hN0]
  have hp : 0 < N := lt_of_le_of_ne hN (Ne.symm hN0)
  rw [Real.sqrt_div ht, Real.sqrt_mul hN]
  have hs := Real.sq_sqrt hN
  have hs0 : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  field_simp
  linear_combination Real.sqrt tau * hs

end TournamentHamiltonian
