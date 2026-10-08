import TournamentHamiltonian.PermanentApproximationFromActivities

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

theorem exp_negative_linear_le_inverse (x : ℝ) (hx : 0 < x) :
    Real.exp (-x) ≤ x⁻¹ := by
  have he : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le hx he

/-- Completing the square absorbs the square-root growth in the actual
circle majorant, giving an explicit dimension-independent inverse bound. -/
theorem exp_sqrt_sub_linear_le_inverse (β b x : ℝ) (hb : 0 < b) (hx : 0 < x) :
    Real.exp (β * Real.sqrt x - b * x) ≤
      (2 / b * Real.exp (β ^ 2 / (2 * b))) / x := by
  have hsq := Real.sq_sqrt hx.le
  have hidentity : (β - b * Real.sqrt x) ^ 2 =
      β ^ 2 - 2 * β * b * Real.sqrt x + b ^ 2 * x := by
    rw [sub_sq, mul_pow, hsq]
    ring
  have hnonneg : 0 ≤ β ^ 2 - 2 * β * b * Real.sqrt x + b ^ 2 * x := by
    rw [← hidentity]
    exact sq_nonneg _
  have hy : β * Real.sqrt x - b * x ≤ β ^ 2 / (2 * b) - b * x / 2 := by
    have hcancel : (β ^ 2 / (2 * b)) * (2 * b) = β ^ 2 := by field_simp
    nlinarith
  calc
    _ ≤ Real.exp (β ^ 2 / (2 * b) - b * x / 2) := Real.exp_le_exp.mpr hy
    _ = Real.exp (β ^ 2 / (2 * b)) * Real.exp (-(b * x / 2)) := by
      rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
    _ ≤ Real.exp (β ^ 2 / (2 * b)) * (b * x / 2)⁻¹ :=
      mul_le_mul_of_nonneg_left (exp_negative_linear_le_inverse _ (by positivity)) (Real.exp_pos _).le
    _ = _ := by field_simp

theorem exp_constant_sub_linear_le_inverse (A b x : ℝ) (hb : 0 < b) (hx : 0 < x) :
    Real.exp (A - b * x) ≤ (Real.exp A / b) / x := by
  calc
    _ = Real.exp A * Real.exp (-(b * x)) := by
      rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
    _ ≤ Real.exp A * (b * x)⁻¹ :=
      mul_le_mul_of_nonneg_left (exp_negative_linear_le_inverse _ (mul_pos hb hx)) (Real.exp_pos _).le
    _ = _ := by ring

noncomputable def permanentApproximationUniformConstant (C q σ R D T₁ α : ℝ) : ℝ :=
  Real.exp ((R * C) ^ 2 / (2 * (1 - (R * q) ^ 2))) * (T₁ + 8 * D ^ 2) +
    gaussianFactorialRecoveryBudget C q σ R +
      R / (R - 1) * (2 / (α * Real.log R) *
        Real.exp ((R * C / (1 - R * q)) ^ 2 / (2 * (α * Real.log R)))) +
          Real.exp ((σ * C) ^ 2 / (2 * (1 - (σ * q) ^ 2))) / (α * Real.log σ)

theorem permanentApproximationActivityBudget_le_inverse (n : ℕ) (hn : 0 < n)
    (C q σ R D T₁ α : ℝ) (hσ : 1 < σ) (hR : 1 < R) (hα : 0 < α) :
    permanentApproximationActivityBudget n C q σ R D T₁ α ≤
      permanentApproximationUniformConstant C q σ R D T₁ α / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnSq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hD : 8 * D ^ 2 / (n : ℝ) ^ 2 ≤ 8 * D ^ 2 / n :=
    div_le_div_of_nonneg_left (by positivity) hnR hnSq
  have hcore := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (T₁ / n)) hD)
      (Real.exp_pos ((R * C) ^ 2 / (2 * (1 - (R * q) ^ 2)))).le
  have hcircle := mul_le_mul_of_nonneg_left
    (exp_sqrt_sub_linear_le_inverse (R * C / (1 - R * q)) (α * Real.log R)
      n (mul_pos hα (Real.log_pos hR)) hnR) (show 0 ≤ R / (R - 1) by positivity)
  have hgaussian := exp_constant_sub_linear_le_inverse
    ((σ * C) ^ 2 / (2 * (1 - (σ * q) ^ 2))) (α * Real.log σ)
      n (mul_pos hα (Real.log_pos hσ)) hnR
  have hecircle : R * C / (1 - R * q) * Real.sqrt n - (α * Real.log R) * n =
      R * C / (1 - R * q) * Real.sqrt n - α * n * Real.log R := by ring
  rw [hecircle] at hcircle
  have hegaussian : (σ * C) ^ 2 / (2 * (1 - (σ * q) ^ 2)) - (α * Real.log σ) * n =
      (σ * C) ^ 2 / (2 * (1 - (σ * q) ^ 2)) - α * n * Real.log σ := by ring
  rw [hegaussian] at hgaussian
  unfold permanentApproximationActivityBudget permanentApproximationUniformConstant
  have h := add_le_add (add_le_add (add_le_add hcore
    (le_refl (gaussianFactorialRecoveryBudget C q σ R / n))) hcircle) hgaussian
  convert h using 1
  ring

end TournamentHamiltonian
