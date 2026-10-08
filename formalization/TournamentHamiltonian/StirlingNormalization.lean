import TournamentHamiltonian.DegreeVariance

/-! Uniform Stirling normalization of the balanced Brégman factor. -/

namespace TournamentHamiltonian

open scoped Classical

/-- A global upper Stirling bound with absolute additive log error one. -/
theorem log_factorial_stirling_upper (k : ℕ) (hk : 1 ≤ k) :
    Real.log (k.factorial : ℝ) ≤
      (k : ℝ) * Real.log (k : ℝ) - k + Real.log (k : ℝ) / 2 + 1 := by
  have h := Stirling.log_stirlingSeq'_antitone (show 0 ≤ k - 1 by omega)
  change Real.log (Stirling.stirlingSeq ((k - 1) + 1)) ≤
    Real.log (Stirling.stirlingSeq 1) at h
  rw [Nat.sub_add_cancel hk, Stirling.log_stirlingSeq_formula,
    Stirling.log_stirlingSeq_formula] at h
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  simp only [Nat.factorial_one, Nat.cast_one, Real.log_one, mul_one,
    Real.log_div hkR.ne' (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hkR.ne',
    Real.log_div one_ne_zero (Real.exp_pos 1).ne'] at h
  nlinarith

theorem logFactorialMean_le_stirling_upper (k : ℕ) (hk : 1 ≤ k) :
    logFactorialMean k ≤ Real.log (k : ℝ) - 1 + Real.log (k : ℝ) / (2 * (k : ℝ)) + 1 / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold logFactorialMean
  apply (div_le_iff₀ hkR).mpr
  have he : (Real.log (k : ℝ) - 1 + Real.log (k : ℝ) / (2 * (k : ℝ)) + 1 / (k : ℝ)) * k =
      (k : ℝ) * Real.log (k : ℝ) - k + Real.log (k : ℝ) / 2 + 1 := by
    field_simp
  rw [he]
  exact log_factorial_stirling_upper k hk

theorem logFactorialMean_le_common_upper (a b k : ℕ) (ha : 1 ≤ a)
    (hak : a ≤ k) (hkb : k ≤ b) :
    logFactorialMean k ≤ Real.log (b : ℝ) - 1 + Real.log (b : ℝ) / (2 * (a : ℝ)) + 1 / (a : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkaR : (a : ℝ) ≤ k := by exact_mod_cast hak
  have hkbR : (k : ℝ) ≤ b := by exact_mod_cast hkb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hl := Real.log_le_log hkR hkbR
  have hlb : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hb1
  have hfrac : Real.log (k : ℝ) / (2 * (k : ℝ)) ≤ Real.log (b : ℝ) / (2 * (a : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have h := (mul_le_mul_of_nonneg_left hl haR.le).trans
      (mul_le_mul_of_nonneg_right hkaR hlb)
    nlinarith
  have hi := one_div_le_one_div_of_le haR hkaR
  have hf := logFactorialMean_le_stirling_upper k (by omega)
  linarith

/-- A uniform logarithmic normalization, including both parities of the
balanced mean, with the explicit universal constant six. -/
theorem balancedLogFactorialMean_stirling_le (m : ℕ) (hm : 3 ≤ m) :
    (m : ℝ) * balancedLogFactorialMean m ≤ Real.log (m.factorial : ℝ) -
      (m : ℝ) * Real.log 2 + Real.log ((m : ℝ) + 1) / 2 + 6 := by
  let a : ℕ := (m - 1) / 2
  let b : ℕ := a + 1
  let θ : ℝ := ((m : ℝ) - 1) / 2 - (a : ℝ)
  let B : ℝ := Real.log (b : ℝ) - 1 + Real.log (b : ℝ) / (2 * (a : ℝ)) + 1 / (a : ℝ)
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hNat : 2 * a + 1 ≤ m ∧ m ≤ 2 * a + 2 := by dsimp [a]; omega
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have ha1R : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hR1 : 2 * (a : ℝ) + 1 ≤ m := by exact_mod_cast hNat.1
  have hR2 : (m : ℝ) ≤ 2 * (a : ℝ) + 2 := by exact_mod_cast hNat.2
  have hbR : (b : ℝ) = (a : ℝ) + 1 := by dsimp [b]; push_cast; rfl
  have hbpos : (0 : ℝ) < b := by rw [hbR]; positivity
  have hθ : 0 ≤ θ ∧ θ ≤ 1 := by dsimp [θ]; constructor <;> linarith
  have hfa : logFactorialMean a ≤ B := logFactorialMean_le_common_upper a b a ha le_rfl (by dsimp [b]; omega)
  have hfb : logFactorialMean b ≤ B := logFactorialMean_le_common_upper a b b ha (by dsimp [b]; omega) le_rfl
  have hbal : balancedLogFactorialMean m ≤ B := by
    change logFactorialMean a + θ * (logFactorialMean b - logFactorialMean a) ≤ B
    have h1 := mul_le_mul_of_nonneg_left hfa (by linarith : 0 ≤ 1 - θ)
    have h2 := mul_le_mul_of_nonneg_left hfb hθ.1
    nlinarith
  have hbalm := mul_le_mul_of_nonneg_left hbal hmR.le
  have hlogb : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by rw [hbR]; linarith)
  have hlogb_a : Real.log (b : ℝ) ≤ a := by
    have h := Real.log_le_sub_one_of_pos hbpos
    linarith
  have hr : (m : ℝ) * (Real.log (b : ℝ) - Real.log (m : ℝ) + Real.log 2) ≤ 1 := by
    have hlog : Real.log (2 * (b : ℝ) / m) = Real.log 2 + Real.log (b : ℝ) - Real.log (m : ℝ) := by
      rw [Real.log_div (by positivity) hmR.ne', Real.log_mul (by norm_num) hbpos.ne']
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * (b : ℝ) / m)) hmR.le
    have he : (m : ℝ) * (2 * (b : ℝ) / m - 1) = 2 * (b : ℝ) - m := by field_simp
    rw [hlog, he] at h
    nlinarith
  have hlogm := Real.log_le_log hbpos (show (b : ℝ) ≤ m by rw [hbR]; linarith)
  have hlogm1 := Real.log_le_log hbpos (show (b : ℝ) ≤ (m : ℝ) + 1 by rw [hbR]; linarith)
  have hδ : (m : ℝ) * Real.log (b : ℝ) / (2 * (a : ℝ)) - Real.log (b : ℝ) ≤ Real.log (b : ℝ) / a := by
    have hp : (2 * (a : ℝ)) * ((m : ℝ) * Real.log (b : ℝ) / (2 * (a : ℝ)) - Real.log (b : ℝ)) ≤
        (2 * (a : ℝ)) * (Real.log (b : ℝ) / a) := by
      field_simp
      nlinarith
    exact le_of_mul_le_mul_left hp (by positivity)
  have hδ1 : Real.log (b : ℝ) / a ≤ 1 := (div_le_iff₀ haR).mpr (by simpa using hlogb_a)
  have hδ' : (m : ℝ) * Real.log (b : ℝ) / (2 * (a : ℝ)) -
      Real.log (m : ℝ) / 2 - Real.log ((m : ℝ) + 1) / 2 ≤ 1 := by linarith
  have hconst : (m : ℝ) / a ≤ 4 := (div_le_iff₀ haR).mpr (by nlinarith)
  have hSt := Stirling.le_log_factorial_stirling (show m ≠ 0 by omega)
  have hPi : 0 ≤ Real.log (2 * Real.pi) / 2 := by
    have h := Real.log_nonneg (show 1 ≤ 2 * Real.pi by nlinarith [Real.pi_gt_three])
    linarith
  have hB : (m : ℝ) * B ≤ Real.log (m.factorial : ℝ) -
      (m : ℝ) * Real.log 2 + Real.log ((m : ℝ) + 1) / 2 + 6 := by
    dsimp [B]
    linear_combination hr + hδ' + hconst + hSt + hPi
  exact hbalm.trans hB

theorem exp_balancedLogFactorialMean_le (m : ℕ) (hm : 3 ≤ m) :
    Real.exp ((m : ℝ) * balancedLogFactorialMean m) ≤
      Real.exp 6 * Real.sqrt ((m : ℝ) + 1) * (m.factorial : ℝ) / (2 : ℝ) ^ m := by
  have h := Real.exp_le_exp.mpr (balancedLogFactorialMean_stirling_le m hm)
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hs : Real.exp (Real.log ((m : ℝ) + 1) / 2) = Real.sqrt ((m : ℝ) + 1) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  have hpow : Real.exp ((m : ℝ) * Real.log 2) = (2 : ℝ) ^ m := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [Real.exp_add, Real.exp_add, Real.exp_sub, Real.exp_log hfac,
    hpow, hs] at h
  convert h using 1
  ring

/-- Actual adjacency permanent with a uniform Stirling prefactor and the
quantitative degree-variance penalty. -/
theorem adjacency_permanent_le_stirling_variance {n : ℕ} (T : Tournament n) (hn : 3 ≤ n) :
    (adjacency T).permanent ≤
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n *
        Real.exp (-degreeVariance T / (8 * (n : ℝ) ^ 2)) := by
  have h := adjacency_permanent_le_balanced_variance T hn
  have hnorm := exp_balancedLogFactorialMean_le n hn
  have hcorr : 1 / (32 * (n : ℝ)) ≤ 1 := by
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have he := Real.exp_le_exp.mpr hcorr
  have hmul := mul_le_mul hnorm he (Real.exp_pos _).le (by positivity)
  have hpen : 0 ≤ Real.exp (-degreeVariance T / (8 * (n : ℝ) ^ 2)) := (Real.exp_pos _).le
  have hmul' := mul_le_mul_of_nonneg_right hmul hpen
  have hEq : Real.exp ((n : ℝ) * balancedLogFactorialMean n -
      degreeVariance T / (8 * (n : ℝ) ^ 2) + 1 / (32 * (n : ℝ))) =
      Real.exp ((n : ℝ) * balancedLogFactorialMean n) * Real.exp (1 / (32 * (n : ℝ))) *
        Real.exp (-degreeVariance T / (8 * (n : ℝ) ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hEq] at h
  have h7 : Real.exp 6 * Real.exp 1 = Real.exp 7 := by rw [← Real.exp_add]; norm_num
  calc
    _ ≤ _ := h.trans hmul'
    _ = _ := by rw [← h7]; ring

theorem degreeVariance_nonneg {n : ℕ} (T : Tournament n) : 0 ≤ degreeVariance T :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem adjacency_permanent_le_stirling {n : ℕ} (T : Tournament n) (hn : 3 ≤ n) :
    (adjacency T).permanent ≤
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n := by
  have hp : Real.exp (-degreeVariance T / (8 * (n : ℝ) ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (degreeVariance_nonneg T)) (by positivity)
  exact (adjacency_permanent_le_stirling_variance T hn).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (by positivity :
      0 ≤ Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n))

theorem adjacency_permanent_eq_zero_of_small_order {n : ℕ} (T : Tournament n)
    (hn : 1 ≤ n) (hn' : n ≤ 2) : (adjacency T).permanent = 0 := by
  have hnonneg : 0 ≤ (adjacency T).permanent := by
    change 0 ≤ (boolMatrix T.val).permanent
    rw [← matching_card_eq_permanent T.val]
    positivity
  apply le_antisymm _ hnonneg
  by_contra hp
  have hp' : 0 < (adjacency T).permanent := by linarith
  have hd : ∀ i : Fin n, (1 : ℝ) ≤ rowDegree T.val i := by
    intro i
    have hpos : 1 ≤ rowDegree T.val i := by
      by_contra h
      have he := boolMatrix_permanent_eq_zero_of_rowDegree_zero T.val i (by omega)
      change (adjacency T).permanent = 0 at he
      rw [he] at hp'
      exact (lt_irrefl 0 hp')
    exact_mod_cast hpos
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hd i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  rw [rowDegree_sum T] at hs
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) ≤ 2 := by exact_mod_cast hn'
  nlinarith

/-- A single Brégman--Stirling bound for all orders, including orders zero,
one and two. This is usable for every actual principal submatrix. -/
theorem adjacency_permanent_le_stirling_all {n : ℕ} (T : Tournament n) :
    (adjacency T).permanent ≤
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n := by
  by_cases hn : 3 ≤ n
  · exact adjacency_permanent_le_stirling T hn
  · by_cases hz : n = 0
    · subst n
      simp only [Matrix.permanent_isEmpty, Nat.cast_zero, zero_add, Real.sqrt_one,
        Nat.factorial_zero, Nat.cast_one, mul_one, pow_zero, div_one]
      exact Real.one_le_exp (by norm_num)
    · rw [adjacency_permanent_eq_zero_of_small_order T (by omega) (by omega)]
      positivity

end TournamentHamiltonian


