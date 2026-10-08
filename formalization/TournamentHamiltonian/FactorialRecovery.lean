import TournamentHamiltonian.GaussianSeries

namespace TournamentHamiltonian

noncomputable def factorialRecoveryRatio (n k : ℕ) : ℝ :=
  (n : ℝ) ^ k / (n.descFactorial k : ℝ)

theorem factorialRecoveryRatio_pos (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    0 < factorialRecoveryRatio n k := by
  unfold factorialRecoveryRatio
  exact div_pos (pow_pos (Nat.cast_pos.mpr hn) _) (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hk))

theorem factorialRecoveryRatio_one_le (n k : ℕ) (_hn : 0 < n) (hk : k ≤ n) :
    1 ≤ factorialRecoveryRatio n k := by
  unfold factorialRecoveryRatio
  apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hk))).mpr
  simp only [one_mul]
  exact_mod_cast Nat.descFactorial_le_pow n k

theorem factorialRecoveryRatio_succ (n k : ℕ) (_hn : 0 < n) (hk : k < n) :
    factorialRecoveryRatio n (k + 1) = (n : ℝ) / (n - k : ℝ) * factorialRecoveryRatio n k := by
  simp only [factorialRecoveryRatio, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hk.le, pow_succ]
  field_simp

theorem recovery_step_log_le (n k : ℕ) (hn : 0 < n) (hk : 2 * k ≤ n) :
    Real.log ((n : ℝ) / (n - k : ℝ)) ≤ 2 * (k : ℝ) / n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hkR : 2 * (k : ℝ) ≤ n := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd : 0 < (n - k : ℝ) := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hnR hd)
  have heq : (n : ℝ) / (n - k : ℝ) - 1 = (k : ℝ) / (n - k : ℝ) := by
    field_simp [hd.ne']
    ring
  rw [heq] at h
  apply h.trans
  apply (div_le_div_iff₀ hd hnR).mpr
  nlinarith

theorem factorialRecoveryRatio_log_le (n k : ℕ) (hn : 0 < n) (hk : 2 * k ≤ n) :
    Real.log (factorialRecoveryRatio n k) ≤ (k : ℝ) ^ 2 / n := by
  induction k with
  | zero => simp [factorialRecoveryRatio]
  | succ k ih =>
    have hkprev : 2 * k ≤ n := by omega
    have hkn : k < n := by omega
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hd : (0 : ℝ) < n - k := by
      have h : (k : ℝ) < n := by exact_mod_cast hkn
      linarith
    rw [factorialRecoveryRatio_succ n k hn hkn,
      Real.log_mul (div_pos hnR hd).ne' (factorialRecoveryRatio_pos n k hn hkn.le).ne']
    calc
      _ ≤ 2 * (k : ℝ) / n + (k : ℝ) ^ 2 / n :=
        add_le_add (recovery_step_log_le n k hn hkprev) (ih hkprev)
      _ ≤ ((k + 1 : ℕ) : ℝ) ^ 2 / n := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ hnR.le
        push_cast
        nlinarith

theorem factorialRecoveryRatio_le_exp (n k : ℕ) (hn : 0 < n) (hk : 2 * k ≤ n) :
    factorialRecoveryRatio n k ≤ Real.exp ((k : ℝ) ^ 2 / n) := by
  have hpos := factorialRecoveryRatio_pos n k hn (by omega)
  nth_rw 1 [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr (factorialRecoveryRatio_log_le n k hn hk)

theorem factorialRecoveryRatio_le_pow (n k : ℕ) (hn : 0 < n) (hk : 2 * k ≤ n)
    (sigma : ℝ) (hs : 1 < sigma) (hwindow : (k : ℝ) / n ≤ Real.log sigma) :
    factorialRecoveryRatio n k ≤ sigma ^ k := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlog : (k : ℝ) ^ 2 / n ≤ (k : ℝ) * Real.log sigma := by
    have h := mul_le_mul_of_nonneg_left hwindow hk0
    exact (show (k : ℝ) ^ 2 / n = (k : ℝ) * ((k : ℝ) / n) by ring).le.trans h
  apply (factorialRecoveryRatio_le_exp n k hn hk).trans
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < sigma)] at h
  exact h

theorem factorialRecoveryRatio_sub_one_bound (n k : ℕ) (hn : 0 < n) (hk : 2 * k ≤ n)
    (sigma : ℝ) (hs : 1 < sigma) (hwindow : (k : ℝ) / n ≤ Real.log sigma) :
    0 ≤ factorialRecoveryRatio n k - 1 ∧
      factorialRecoveryRatio n k - 1 ≤ ((k : ℝ) ^ 2 / n) * sigma ^ k := by
  have hk' : k ≤ n := by omega
  have hp := factorialRecoveryRatio_pos n k hn hk'
  have h1 := factorialRecoveryRatio_one_le n k hn hk'
  have hlog0 := Real.log_nonneg h1
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hp.ne'] at h
  have hprod := mul_le_mul (factorialRecoveryRatio_le_pow n k hn hk sigma hs hwindow)
    (factorialRecoveryRatio_log_le n k hn hk) hlog0 (pow_nonneg (by linarith : 0 ≤ sigma) k)
  exact ⟨by linarith, h.trans (hprod.trans_eq (mul_comm _ _))⟩

end TournamentHamiltonian
