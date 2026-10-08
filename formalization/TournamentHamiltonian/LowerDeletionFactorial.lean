import TournamentHamiltonian.DeletionFactorial

namespace TournamentHamiltonian

theorem factorial_deletion_ratio_one_le (n k : ℕ) (hk : k≤n) :
    1≤(n : ℝ)^k*((n-k).factorial : ℝ)/(n.factorial : ℝ) := by
  have hfac : n.factorial≤n^k*(n-k).factorial := by
    have h := Nat.mul_le_mul_right ((n-k).factorial) (Nat.descFactorial_le_pow n k)
    rw [Nat.mul_comm (n.descFactorial k),Nat.factorial_mul_descFactorial hk] at h
    exact h
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<n.factorial)).mpr
  norm_cast
  simpa only [one_mul] using hfac

theorem convolution_factorial_ratio_ge (n k : ℕ) (hn : 0<n) (hk : k≤n) :
    (2/(n : ℝ))^k≤(((n-k).factorial : ℝ)/(2 : ℝ)^(n-k))/
      ((n.factorial : ℝ)/(2 : ℝ)^n) := by
  have hp : (2 : ℝ)^n=(2 : ℝ)^(n-k)*(2 : ℝ)^k := by
    rw [←pow_add,Nat.sub_add_cancel hk]
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have h := mul_le_mul_of_nonneg_right (factorial_deletion_ratio_one_le n k hk)
    (by positivity : 0≤(2/(n : ℝ))^k)
  simp only [one_mul] at h
  convert h using 1
  rw [hp,div_pow]
  field_simp

end TournamentHamiltonian
