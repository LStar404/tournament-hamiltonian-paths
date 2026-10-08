import TournamentHamiltonian.CrossPermanentBounds

/-! Exact factorial normalization and uniform errors for the four-block sum. -/

namespace TournamentHamiltonian

open scoped Classical

theorem factorial_add_eq_prod_fin (a r : ℕ) :
    ((a + r).factorial : ℝ) = (a.factorial : ℝ) *
      ∏ i : Fin r, ((a : ℝ) + (i.val : ℝ) + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.prod_univ_castSucc, Nat.add_succ, Nat.factorial_succ, Nat.cast_mul, ih]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    ring

theorem log_ratio_le_two_mul (N f a : ℝ) (hN : 0 < N) (hf : 0 ≤ f)
    (hfN : 2 * f ≤ N) (ha : N - f ≤ a) :
    Real.log N - Real.log a ≤ 2 * f / N := by
  have ha0 : 0 < a := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hN ha0)
  rw [Real.log_div hN.ne' ha0.ne'] at hlog
  have hfac := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ N + 2 * f)
  have hsq : N * N ≤ (N + 2 * f) * a := by nlinarith [mul_nonneg hf (show 0 ≤ N - 2 * f by linarith)]
  have he : N / a ≤ 1 + 2 * f / N := by
    apply (div_le_iff₀ ha0).mpr
    apply le_of_mul_le_mul_left (a := N)
    · calc
        N * N ≤ (N + 2 * f) * a := hsq
        _ = N * ((1 + 2 * f / N) * a) := by field_simp
    · exact hN
  linarith

theorem factorial_ratio_le_exp (N f t : ℕ) (hN : 0 < N) (hfN : 2 * f ≤ N) (ht : t ≤ f) :
    (N : ℝ) ^ (f + t) * ((N - t).factorial : ℝ) / ((N + f).factorial : ℝ) ≤
      Real.exp (4 * (f : ℝ) ^ 2 / (N : ℝ)) := by
  have htN : t ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hf0 : (0 : ℝ) ≤ f := by positivity
  have hfNR : 2 * (f : ℝ) ≤ N := by exact_mod_cast hfN
  have htR : (t : ℝ) ≤ f := by exact_mod_cast ht
  have hcast : ((N - t : ℕ) : ℝ) = (N : ℝ) - t := by rw [Nat.cast_sub htN]
  have hfac : ((N + f).factorial : ℝ) = ((N - t).factorial : ℝ) *
      ∏ i : Fin (f + t), ((N : ℝ) - (t : ℝ) + (i.val : ℝ) + 1) := by
    have h := factorial_add_eq_prod_fin (N - t) (f + t)
    rw [hcast] at h
    simpa only [show N - t + (f + t) = N + f by omega] using h
  have hapos (i : Fin (f + t)) : 0 < (N : ℝ) - (t : ℝ) + (i.val : ℝ) + 1 := by
    have hNt : (t : ℝ) ≤ N := by exact_mod_cast htN
    positivity
  have hlogfac : Real.log ((N + f).factorial : ℝ) = Real.log ((N - t).factorial : ℝ) +
      ∑ i : Fin (f + t), Real.log ((N : ℝ) - (t : ℝ) + (i.val : ℝ) + 1) := by
    rw [hfac, Real.log_mul (by positivity) (Finset.prod_ne_zero_iff.mpr (fun i _ => (hapos i).ne')),
      Real.log_prod (fun i _ => (hapos i).ne')]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin (f + t)) _ =>
    log_ratio_le_two_mul (N : ℝ) (f : ℝ) ((N : ℝ) - (t : ℝ) + (i.val : ℝ) + 1)
      hN0 hf0 hfNR (by linarith [show (0 : ℝ) ≤ (i.val : ℝ) by positivity]))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add] at hsum
  have hprod := mul_le_mul_of_nonneg_right (show (f : ℝ) + t ≤ 2 * f by linarith)
    (by positivity : 0 ≤ 2 * (f : ℝ) / N)
  have hratio : 0 < (N : ℝ) ^ (f + t) * ((N - t).factorial : ℝ) / ((N + f).factorial : ℝ) := by positivity
  rw [← Real.exp_log hratio]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, hlogfac]
  push_cast
  linear_combination hsum + hprod

theorem fourBlock_cross_normalization (N f s : ℕ) (hN : f ≤ N) (hs : s ≤ f) :
    (((N : ℝ) ^ (2 * (f - s)) / (2 : ℝ) ^ (2 * (f - s))) *
      (((N - (f - s)).factorial : ℝ) / (2 : ℝ) ^ (N - (f - s)))) /
        (((N + f).factorial : ℝ) / (2 : ℝ) ^ (N + f)) =
      (2 : ℝ) ^ s * (N : ℝ) ^ (2 * (f - s)) *
        ((N - (f - s)).factorial : ℝ) / ((N + f).factorial : ℝ) := by
  have hp : (2 : ℝ) ^ (N + f) = (2 : ℝ) ^ (2 * (f - s)) *
      (2 : ℝ) ^ (N - (f - s)) * (2 : ℝ) ^ s := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hp]
  field_simp

theorem fourBlock_factorial_normalization_le (N f s : ℕ) (hN : 0 < N)
    (hfN : 2 * f ≤ N) (hs : s ≤ f) :
    (2 : ℝ) ^ s * (N : ℝ) ^ (2 * (f - s)) * ((N - (f - s)).factorial : ℝ) /
      ((N + f).factorial : ℝ) ≤
        (2 / (N : ℝ)) ^ s * Real.exp (4 * (f : ℝ) ^ 2 / (N : ℝ)) := by
  have h := factorial_ratio_le_exp N f (f - s) hN hfN (Nat.sub_le _ _)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hp : (N : ℝ) ^ (f + (f - s)) = (N : ℝ) ^ s * (N : ℝ) ^ (2 * (f - s)) := by
    rw [← pow_add]
    congr 1
    omega
  have hm := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (2 / (N : ℝ)) ^ s)
  convert hm using 1
  rw [div_pow, hp]
  field_simp

theorem choose_square_mul_factorial_le (f s : ℕ) :
    (f.choose s : ℝ) ^ 2 * (s.factorial : ℝ) ≤ (f : ℝ) ^ (2 * s) / (s.factorial : ℝ) := by
  have hNat := Nat.descFactorial_le_pow f s
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hNat
  have h : (s.factorial : ℝ) * (f.choose s : ℝ) ≤ (f : ℝ) ^ s := by exact_mod_cast hNat
  have hs : (0 : ℝ) < s.factorial := by exact_mod_cast s.factorial_pos
  apply (le_div_iff₀ hs).mpr
  have hsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr h
  rw [show 2 * s = s * 2 by omega, pow_mul]
  nlinarith

end TournamentHamiltonian
