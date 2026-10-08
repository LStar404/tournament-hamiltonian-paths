import TournamentHamiltonian.CrossFactorialNormalization

/-! Falling-factorial errors in the actual normalized subset convolution. -/
namespace TournamentHamiltonian
open scoped Classical

theorem factorial_deletion_ratio_le_exp (n k : ℕ) (hn : 0 < n) (hk : 2 * k ≤ n) :
    (n : ℝ) ^ k * ((n - k).factorial : ℝ) / (n.factorial : ℝ) ≤
      Real.exp (2 * (k : ℝ) ^ 2 / n) := by
  have hkn : k ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : 2 * (k : ℝ) ≤ n := by exact_mod_cast hk
  have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by rw [Nat.cast_sub hkn]
  have hfac : (n.factorial : ℝ) = ((n - k).factorial : ℝ) *
      ∏ i : Fin k, ((n : ℝ) - (k : ℝ) + (i.val : ℝ) + 1) := by
    have h := factorial_add_eq_prod_fin (n - k) k
    rw [hcast, Nat.sub_add_cancel hkn] at h
    exact h
  have hapos (i : Fin k) : 0 < (n : ℝ) - (k : ℝ) + (i.val : ℝ) + 1 := by
    have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
    positivity
  have hlogfac : Real.log (n.factorial : ℝ) = Real.log ((n - k).factorial : ℝ) +
      ∑ i : Fin k, Real.log ((n : ℝ) - (k : ℝ) + (i.val : ℝ) + 1) := by
    rw [hfac, Real.log_mul (by positivity) (Finset.prod_ne_zero_iff.mpr (fun i _ => (hapos i).ne')),
      Real.log_prod (fun i _ => (hapos i).ne')]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin k) _ =>
    log_ratio_le_two_mul (n : ℝ) (k : ℝ) ((n : ℝ) - (k : ℝ) + (i.val : ℝ) + 1)
      hn0 (by positivity) hkR (by linarith [show (0 : ℝ) ≤ (i.val : ℝ) by positivity]))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hp : 0 < (n : ℝ) ^ k * ((n - k).factorial : ℝ) / (n.factorial : ℝ) := by positivity
  rw [← Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, hlogfac]
  linear_combination hsum

theorem convolution_factorial_ratio_le (n k : ℕ) (hn : 0 < n) (hk : 2 * k ≤ n) :
    (((n - k).factorial : ℝ) / (2 : ℝ) ^ (n - k)) /
      ((n.factorial : ℝ) / (2 : ℝ) ^ n) ≤
        Real.exp (2 * (k : ℝ) ^ 2 / n) * (2 / (n : ℝ)) ^ k := by
  have hkn : k ≤ n := by omega
  have hp : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - k) * (2 : ℝ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have h := mul_le_mul_of_nonneg_right (factorial_deletion_ratio_le_exp n k hn hk)
    (by positivity : 0 ≤ (2 / (n : ℝ)) ^ k)
  convert h using 1
  rw [hp, div_pow]
  field_simp

end TournamentHamiltonian
