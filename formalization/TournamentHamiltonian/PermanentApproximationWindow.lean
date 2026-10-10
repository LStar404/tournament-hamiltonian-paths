import TournamentHamiltonian.FiniteGaussianCoreWindow
import TournamentHamiltonian.GaussianFactorialRecovery
import TournamentHamiltonian.RealPermanentAnalyticTail

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem actual_normalized_coefficient_recovery (B : Matrix ι ι ℝ) (k : ℕ) :
    (normalizedPermanentPolynomial ((Fintype.card ι : ℝ) • B)).coeff k =
      factorialRecoveryRatio (Fintype.card ι) k *
        (distinctCoordinateSum B k / (k.factorial : ℝ)) := by
  rw [normalizedPermanentPolynomial_coeff]
  change permanentMinorSum (fun i j => (Fintype.card ι : ℝ) * B i j) k / _ = _
  rw [permanentMinorSum_scale, permanentMinorSum_eq_distinctCoordinateSum_div_factorial]
  unfold factorialRecoveryRatio
  ring

theorem actual_normalized_coefficient_window_error_le (B : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (k : ℕ) (σ R : ℝ) (hσ : 1 < σ) (hσR : σ ≤ R)
    (hk : 2 * k ≤ Fintype.card ι) (hwindow : (k : ℝ) / Fintype.card ι ≤ Real.log σ) :
    |(normalizedPermanentPolynomial ((Fintype.card ι : ℝ) • B)).coeff k -
        bilinearGaussianCoefficient B k| ≤
      |distinctCoordinateSum B k / (k.factorial : ℝ) - bilinearGaussianCoefficient B k| * R ^ k +
        (factorialRecoveryRatio (Fintype.card ι) k - 1) * bilinearGaussianCoefficient B k := by
  let r := factorialRecoveryRatio (Fintype.card ι) k
  let F := distinctCoordinateSum B k / (k.factorial : ℝ)
  let g := bilinearGaussianCoefficient B k
  have hr := (factorialRecoveryRatio_pos _ k hp (by omega)).le
  have hr1 := sub_nonneg.mpr (factorialRecoveryRatio_one_le _ k hp (by omega))
  have hratio : r ≤ R ^ k :=
    (factorialRecoveryRatio_le_pow _ k hp hk σ hσ hwindow).trans
      (pow_le_pow_left₀ (by linarith) hσR k)
  rw [actual_normalized_coefficient_recovery]
  change |r * F - g| ≤ |F - g| * R ^ k + (r - 1) * g
  calc
    _ = |r * (F - g) + (r - 1) * g| := by congr 1; ring
    _ ≤ |r * (F - g)| + |(r - 1) * g| := abs_add_le _ _
    _ = |F - g| * r + (r - 1) * g := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg hr1,
        abs_of_nonneg (bilinearGaussianCoefficient_nonneg B k), mul_comm r]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hratio (abs_nonneg _)) le_rfl

theorem actual_normalized_permanent_finite_window_error_le (B : Matrix ι ι ℝ)
    (hB : DoublyCentered B) (hp : 0 < Fintype.card ι)
    (M : ℕ) (C q σ R K : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hσ : 1 < σ) (hσR : σ < R) (hRq : R * q < 1)
    (hZ : ‖B‖ ≤ q) (hF : realFrobeniusNorm B ≤ C)
    (hcore : (∑ k ∈ Finset.range (M + 1), coreExcessAbsCoefficient B k * R ^ k) ≤ K)
    (hwindow : ∀ k ∈ Finset.range (M + 1),
      2 * k ≤ Fintype.card ι ∧ (k : ℝ) / Fintype.card ι ≤ Real.log σ) :
    (∑ k ∈ Finset.range (M + 1),
      |(normalizedPermanentPolynomial ((Fintype.card ι : ℝ) • B)).coeff k -
        bilinearGaussianCoefficient B k|) ≤
      gramGaussian (R • B) * K +
        gaussianFactorialRecoveryBudget C q σ R / Fintype.card ι := by
  have hR : 0 < R := by linarith
  have hgap : R * ‖B‖ < 1 :=
    (mul_le_mul_of_nonneg_left hZ hR.le).trans_lt hRq
  have hsum := Finset.sum_le_sum (s := Finset.range (M + 1)) (fun k hk =>
    actual_normalized_coefficient_window_error_le B hp k σ R hσ hσR.le
      (hwindow k hk).1 (hwindow k hk).2)
  rw [Finset.sum_add_distrib] at hsum
  exact hsum.trans (add_le_add
    (actual_finite_gaussian_core_error_le B hB.1 hB.2 M R K hR.le hgap hcore)
    (gaussian_factorial_recovery_le _ hp B C q σ R hC hq hσ hσR hRq hZ hF _ hwindow))

end TournamentHamiltonian
