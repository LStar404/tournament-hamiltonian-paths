import TournamentHamiltonian.PermanentApproximationWindow
import TournamentHamiltonian.PolynomialSeriesComparison
import TournamentHamiltonian.GaussianTailBudget

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def permanentApproximationActivityBudget
    (n : ℕ) (C q σ R D T₁ α : ℝ) : ℝ :=
  Real.exp ((R * C) ^ 2 / (2 * (1 - (R * q) ^ 2))) *
    (T₁ / n + 8 * D ^ 2 / (n : ℝ) ^ 2) +
      gaussianFactorialRecoveryBudget C q σ R / n +
        R / (R - 1) * Real.exp
          (R * C / (1 - R * q) * Real.sqrt n - α * n * Real.log R) +
            Real.exp ((σ * C) ^ 2 / (2 * (1 - (σ * q) ^ 2)) - α * n * Real.log σ)

variable {ι : Type*} [Fintype ι]

/-- A complete analytic approximation for the actual permanent. Only the
two explicitly displayed core activity estimates remain graph-counting
premises; all coefficient normalization, recovery and tails are proved. -/
theorem actual_permanent_approximation_of_core_activities (B : Matrix ι ι ℝ)
    (hB : DoublyCentered B) (hp : 0 < Fintype.card ι)
    (C q σ R D T₁ α : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hσ : 1 < σ) (hσR : σ < R) (hRq : R * q < 1)
    (hZ : ‖B‖ ≤ q) (hF : realFrobeniusNorm B ≤ C)
    (hD : 0 ≤ D) (hT : 0 ≤ T₁) (hα : 0 ≤ α) (hαquarter : α ≤ 1 / 4)
    (hαD : 16 * D * α ≤ 1) (hαlog : α ≤ Real.log σ)
    (hfirst : (∑ k ∈ Finset.range (Nat.floor (α * Fintype.card ι) + 1),
      |actualCoreExcessCoefficient B 1 k| * R ^ k) ≤ T₁ / Fintype.card ι)
    (hexcess : ∀ j ∈ Finset.Icc 2 (Nat.floor (α * Fintype.card ι)),
      (∑ k ∈ Finset.range (Nat.floor (α * Fintype.card ι) + 1),
        |actualCoreExcessCoefficient B j k| * R ^ k) ≤ excessWindowTerm D (Fintype.card ι) j) :
    |(Matrix.permanent (fun i j => 1 + (Fintype.card ι : ℝ) * B i j)) /
        ((Fintype.card ι).factorial : ℝ) - gramGaussian B| ≤
      permanentApproximationActivityBudget (Fintype.card ι) C q σ R D T₁ α := by
  let n := Fintype.card ι
  let M := Nat.floor (α * n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hp
  have hR : 1 < R := hσ.trans hσR
  have hRp : 0 < R := by linarith
  have hgap : R * ‖B‖ < 1 :=
    (mul_le_mul_of_nonneg_left hZ hRp.le).trans_lt hRq
  have hfloor : (M : ℝ) ≤ α * n := Nat.floor_le (mul_nonneg hα hnR.le)
  have hwindow : ∀ k ∈ Finset.range (M + 1),
      2 * k ≤ n ∧ (k : ℝ) / n ≤ Real.log σ := by
    intro k hk
    have hkM : k ≤ M := by have h := Finset.mem_range.mp hk; omega
    have hkR : (k : ℝ) ≤ α * n := (Nat.cast_le.mpr hkM).trans hfloor
    constructor
    · have ha := mul_le_mul_of_nonneg_right hαquarter hnR.le
      have hh : 2 * (k : ℝ) ≤ n := by nlinarith
      exact_mod_cast hh
    · apply (div_le_iff₀ hnR).mpr
      exact hkR.trans (mul_le_mul_of_nonneg_right hαlog hnR.le)
  have hM : 16 * D * (M : ℝ) ≤ n := by
    have hf := mul_le_mul_of_nonneg_left hfloor (by positivity : 0 ≤ 16 * D)
    have ha := mul_le_mul_of_nonneg_right hαD hnR.le
    nlinarith
  have hcore := actual_core_finite_excess_window_le B n M D T₁ R hp hD hRp.le hM hfirst hexcess
  have hfinite := actual_normalized_permanent_finite_window_error_le B hB hp M C q σ R
    (T₁ / n + 8 * D ^ 2 / (n : ℝ) ^ 2) hC hq hσ hσR hRq hZ hF hcore hwindow
  have hZR : ‖R • B‖ ≤ R * q := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRp]
    exact mul_le_mul_of_nonneg_left hZ hRp.le
  have hFR : realFrobeniusNorm (R • B) ≤ R * C := by
    rw [realFrobeniusNorm_smul, abs_of_pos hRp]
    exact mul_le_mul_of_nonneg_left hF hRp.le
  have hG := gramGaussian_le_exp_frobenius_budget (R • B) (R * C) (R * q)
    (mul_nonneg hRp.le hC) (mul_nonneg hRp.le hq) hRq hZR hFR
  have hK : 0 ≤ T₁ / n + 8 * D ^ 2 / (n : ℝ) ^ 2 := by positivity
  have hfinite' := hfinite.trans (add_le_add
    (mul_le_mul_of_nonneg_right hG hK) le_rfl)
  have hnorm : ‖B‖ < 1 := by
    have hm := mul_nonneg (sub_nonneg.mpr hR.le) (norm_nonneg B)
    nlinarith
  have hs : HasSum (bilinearGaussianCoefficient B) (gramGaussian B) := by
    simpa only [one_pow, mul_one, one_smul] using
      bilinearGaussianCoefficient_hasSum B 1 (by simpa using hnorm)
  have hσq : σ * q < 1 :=
    (mul_le_mul_of_nonneg_right hσR.le hq).trans_lt hRq
  have happrox := polynomial_nonnegative_series_comparison
    (normalizedPermanentPolynomial ((n : ℝ) • B)) (bilinearGaussianCoefficient B)
    (gramGaussian B) _ _ _ (bilinearGaussianCoefficient_nonneg B) hs M hfinite'
    (real_normalized_permanent_floor_tail_bound B hB hp R q C α hR hZ hC hF hRq)
    (bilinearGaussianCoefficient_floor_tail_exp_budget B σ (α * n) C q hσ hC hq hσq hZ hF)
  rw [normalizedPermanentPolynomial_eval] at happrox
  simpa only [one_mul, Matrix.smul_apply, smul_eq_mul,
    permanentApproximationActivityBudget, n, M] using happrox

end TournamentHamiltonian
