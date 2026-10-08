import TournamentHamiltonian.PairedPermanentErrorBudget

/-! Complete coarse control of the actual paired permanent error, including
every retained-mass term, by a logarithmic rate tending to zero. -/
namespace TournamentHamiltonian
open Filter
open scoped Topology

theorem pairedPermanentErrorBudget_le_sqrt {n t : ℕ} (hn : 1 ≤ n) (tau : ℝ) (htau : 0 ≤ tau) :
    pairedPermanentErrorBudget n t tau ≤ 2 * (tau + t + 1) ^ 2 / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : (0 : ℝ) ≤ t := by positivity
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs : Real.sqrt n ≤ n := by nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg (n : ℝ)]
  have hroot : Real.sqrt tau ≤ tau + (t : ℝ) + 1 := by
    nlinarith [Real.sq_sqrt htau, Real.sqrt_nonneg tau, sq_nonneg (tau - 1)]
  have hnum : (t : ℝ) + 1 + tau + tau ^ 2 + t ^ 2 ≤ (tau + t + 1) ^ 2 := by
    nlinarith [mul_nonneg htau ht]
  have hrate := (div_le_div_of_nonneg_right hnum hn0.le).trans
    (div_le_div_of_nonneg_left (sq_nonneg (tau + t + 1)) hs0 hs)
  have hrootrate : (tau + (t : ℝ) + 1) * Real.sqrt (tau / n) ≤
      (tau + t + 1) ^ 2 / Real.sqrt n := by
    rw [Real.sqrt_div htau]
    have h := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ tau + (t : ℝ) + 1)) hs0.le
    convert h using 1 <;> ring
  unfold pairedPermanentErrorBudget
  convert add_le_add hrate hrootrate using 1 <;> ring

noncomputable def exceptionalMinorError (K : ℝ) (n : ℕ) : ℝ :=
  4 * K * (1000 * Real.log (n : ℝ) + 1) ^ 2 / Real.sqrt n

theorem exceptionalMinorError_tendsto_zero (K : ℝ) : Tendsto (exceptionalMinorError K) atTop (𝓝 0) := by
  have h2 := (log_pow_div_sqrt_nat_tendsto_zero 2).const_mul (4000000 * K)
  have h1 := (log_pow_div_sqrt_nat_tendsto_zero 1).const_mul (8000 * K)
  have h0 := (log_pow_div_sqrt_nat_tendsto_zero 0).const_mul (4 * K)
  have h := (h2.add h1).add h0
  simp only [mul_zero, add_zero] at h
  convert h using 1
  ext n
  dsimp [exceptionalMinorError]
  simp only [pow_zero, pow_one]
  ring

theorem pairedPermanentErrorBudget_deleted_log_le {n N t : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hNhalf : (n : ℝ) / 2 ≤ N) (tau K : ℝ) (htau : 0 ≤ tau) (hK : 0 ≤ K)
    (htauA : tau ≤ 600 * Real.log (n : ℝ)) (htA : (t : ℝ) ≤ 400 * Real.log (n : ℝ)) :
    K * pairedPermanentErrorBudget N t tau ≤ exceptionalMinorError K n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hroot : Real.sqrt n ≤ 2 * Real.sqrt N := by
    nlinarith [Real.sq_sqrt hn0.le, Real.sq_sqrt hN0.le, Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (N : ℝ)]
  have hx : tau + (t : ℝ) + 1 ≤ 1000 * Real.log (n : ℝ) + 1 := by linarith
  have hxsq := (sq_le_sq₀ (by positivity : 0 ≤ tau + (t : ℝ) + 1) (by positivity)).mpr hx
  have hcoarse := mul_le_mul_of_nonneg_left (pairedPermanentErrorBudget_le_sqrt (t := t) hN tau htau) hK
  calc
    _ ≤ K * (2 * (tau + t + 1) ^ 2 / Real.sqrt N) := hcoarse
    _ ≤ K * (2 * (1000 * Real.log (n : ℝ) + 1) ^ 2 / Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxsq (by norm_num)) (Real.sqrt_nonneg _)) hK
    _ ≤ exceptionalMinorError K n := by
      dsimp [exceptionalMinorError]
      apply (le_div_iff₀ (Real.sqrt_pos.mpr hn0)).mpr
      have heq : (K * (2 * (1000 * Real.log (n : ℝ) + 1) ^ 2 / Real.sqrt N)) * Real.sqrt n =
          (2 * K * (1000 * Real.log (n : ℝ) + 1) ^ 2) * (Real.sqrt n / Real.sqrt N) := by ring
      rw [heq]
      have hr : Real.sqrt n / Real.sqrt N ≤ 2 := (div_le_iff₀ (Real.sqrt_pos.mpr hN0)).mpr hroot
      have hm := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * K * (1000 * Real.log (n : ℝ) + 1) ^ 2)
      nlinarith

end TournamentHamiltonian
