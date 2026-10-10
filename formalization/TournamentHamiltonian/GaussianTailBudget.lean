import TournamentHamiltonian.GaussianAnalyticTail
import TournamentHamiltonian.GaussianFactorialRecovery

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ]

theorem bilinearGaussianCoefficient_floor_tail_exp_budget (Z : Matrix ι ρ ℝ)
    (σ a C q : ℝ) (hσ : 1 < σ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hσq : σ * q < 1) (hZ : ‖Z‖ ≤ q) (hF : realFrobeniusNorm Z ≤ C) :
    (∑' k, bilinearGaussianCoefficient Z (k + (Nat.floor a + 1))) ≤
      Real.exp ((σ * C) ^ 2 / (2 * (1 - (σ * q) ^ 2)) - a * Real.log σ) := by
  have hσp : 0 < σ := by linarith
  have hgap : σ * ‖Z‖ < 1 :=
    (mul_le_mul_of_nonneg_left hZ hσp.le).trans_lt hσq
  have hnorm : ‖σ • Z‖ ≤ σ * q := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσp]
    exact mul_le_mul_of_nonneg_left hZ hσp.le
  have hfrob : realFrobeniusNorm (σ • Z) ≤ σ * C := by
    rw [realFrobeniusNorm_smul, abs_of_pos hσp]
    exact mul_le_mul_of_nonneg_left hF hσp.le
  have hG := gramGaussian_le_exp_frobenius_budget (σ • Z) (σ * C) (σ * q)
    (mul_nonneg hσp.le hC) (mul_nonneg hσp.le hq) hσq hnorm hfrob
  calc
    _ ≤ gramGaussian (σ • Z) * Real.exp (-a * Real.log σ) :=
      bilinearGaussianCoefficient_floor_tail_bound Z σ a hσ hgap
    _ ≤ Real.exp ((σ * C) ^ 2 / (2 * (1 - (σ * q) ^ 2))) *
        Real.exp (-a * Real.log σ) := mul_le_mul_of_nonneg_right hG (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end TournamentHamiltonian
