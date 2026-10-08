import TournamentHamiltonian.Hadamard
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling

open Filter
open scoped Topology

namespace TournamentHamiltonian

/-- Algebraically equivalent to `2^k h_k / k!`; the square-root expression
keeps the ratio estimate free of fractional exponents. -/
noncomputable def subsetWeight (k : ℕ) : ℝ :=
  Real.sqrt (2 ^ k * (k + 1 : ℝ) ^ k) / Nat.factorial k

theorem subsetWeight_nonneg (k : ℕ) : 0 ≤ subsetWeight k := by
  unfold subsetWeight
  positivity

theorem subsetWeight_pos (k : ℕ) : 0 < subsetWeight k := by
  unfold subsetWeight
  positivity

theorem subsetWeight_sq (k : ℕ) :
    subsetWeight k ^ 2 = (2 : ℝ) ^ k * (k + 1 : ℝ) ^ k / (Nat.factorial k : ℝ) ^ 2 := by
  rw [subsetWeight, div_pow, Real.sq_sqrt (by positivity)]

theorem subsetWeight_eq (k : ℕ) :
    subsetWeight k = 2 ^ k * ((k + 1 : ℝ) / 2) ^ ((k : ℝ) / 2) / Nat.factorial k := by
  have hroot : Real.sqrt (2 ^ k * (k + 1 : ℝ) ^ k) =
      2 ^ k * Real.sqrt (((k + 1 : ℝ) / 2) ^ k) := by
    have h1 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 ^ k * (k + 1 : ℝ) ^ k)
    have h2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((k + 1 : ℝ) / 2) ^ k)
    have heq : ((2 : ℝ) ^ k) ^ 2 * (((k + 1 : ℝ) / 2) ^ k) =
        (2 : ℝ) ^ k * (k + 1 : ℝ) ^ k := by
      rw [div_pow]
      field_simp
    have hn : 0 ≤ 2 ^ k * Real.sqrt (((k + 1 : ℝ) / 2) ^ k) := by positivity
    have h2' := congrArg (fun x : ℝ => ((2 : ℝ) ^ k) ^ 2 * x) h2
    rw [heq] at h2'
    nlinarith [Real.sqrt_nonneg (2 ^ k * (k + 1 : ℝ) ^ k)]
  rw [subsetWeight, hroot, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast ((k + 1 : ℝ) / 2) k,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (k + 1 : ℝ) / 2)]
  simp only [mul_one_div]

private theorem binomial_ratio_le_three (k : ℕ) :
    (((k + 2 : ℝ) / (k + 1 : ℝ)) ^ k) ≤ 3 := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have he : (k + 2 : ℝ) / (k + 1 : ℝ) ≤ Real.exp (1 / (k + 1 : ℝ)) := by
    have h := Real.add_one_le_exp (1 / (k + 1 : ℝ))
    have hid : (k + 2 : ℝ) / (k + 1 : ℝ) = 1 / (k + 1 : ℝ) + 1 := by field_simp; ring
    rwa [← hid] at h
  have hpow := pow_le_pow_left₀ (by positivity) he k
  rw [← Real.exp_nat_mul] at hpow
  have hexp : Real.exp ((k : ℝ) * (1 / (k + 1 : ℝ))) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    rw [mul_one_div, div_le_iff₀ hk]
    linarith
  exact hpow.trans (hexp.trans Real.exp_one_lt_three.le)

/-- A uniform ratio bound that tends to zero, proved without Stirling. -/
theorem subsetWeight_succ_sq_le (k : ℕ) :
    subsetWeight (k + 1) ^ 2 ≤ (12 / (k + 1 : ℝ)) * subsetWeight k ^ 2 := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hfact : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have heq : subsetWeight (k + 1) ^ 2 =
      (2 * (k + 2 : ℝ) / (k + 1 : ℝ) ^ 2) *
        (((k + 2 : ℝ) / (k + 1 : ℝ)) ^ k) * subsetWeight k ^ 2 := by
    simp only [subsetWeight_sq, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [pow_succ, pow_succ, div_pow]
    field_simp
    ring
  have hcoeff : 2 * (k + 2 : ℝ) / (k + 1 : ℝ) ^ 2 * 3 ≤ 12 / (k + 1 : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hk)).mpr
    field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  rw [heq]
  calc
    _ ≤ (2 * (k + 2 : ℝ) / (k + 1 : ℝ) ^ 2) * 3 * subsetWeight k ^ 2 := by
      gcongr
      exact binomial_ratio_le_three k
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)

noncomputable def subsetMoment (c : ℝ) (r k : ℕ) : ℝ :=
  (k : ℝ) ^ r * c ^ k * subsetWeight k

theorem subsetMoment_nonneg {c : ℝ} (hc : 0 ≤ c) (r k : ℕ) :
    0 ≤ subsetMoment c r k :=
  mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hc _))
    (subsetWeight_nonneg _)

theorem subsetMoment_succ_sq_le {c : ℝ} (_hc : 0 ≤ c) (r k : ℕ) (hk : 1 ≤ k) :
    subsetMoment c r (k + 1) ^ 2 ≤
      (12 * ((2 : ℝ) ^ r) ^ 2 * c ^ 2 / (k + 1 : ℝ)) * subsetMoment c r k ^ 2 := by
  have hdegree : (k + 1 : ℝ) ^ r ≤ (2 : ℝ) ^ r * (k : ℝ) ^ r := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hkR : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
    linarith
  calc
    _ = ((k + 1 : ℝ) ^ r) ^ 2 * (c ^ (k + 1)) ^ 2 * subsetWeight (k + 1) ^ 2 := by
      simp only [subsetMoment, Nat.cast_add, Nat.cast_one, mul_pow]
    _ ≤ ((2 ^ r * (k : ℝ) ^ r) ^ 2) * (c ^ (k + 1)) ^ 2 *
        ((12 / (k + 1 : ℝ)) * subsetWeight k ^ 2) := by
      gcongr
      exact subsetWeight_succ_sq_le k
    _ = _ := by
      simp only [subsetMoment, pow_succ, mul_pow]
      ring

/-- An explicit sufficient cutoff for geometric decay of any fixed moment. -/
theorem subsetMoment_succ_le_half {c : ℝ} (hc : 0 ≤ c) (r k : ℕ) (hk : 1 ≤ k)
    (hcut : 48 * ((2 : ℝ) ^ r) ^ 2 * c ^ 2 ≤ (k + 1 : ℝ)) :
    subsetMoment c r (k + 1) ≤ (1 / 2 : ℝ) * subsetMoment c r k := by
  have hcoeff : 12 * ((2 : ℝ) ^ r) ^ 2 * c ^ 2 / (k + 1 : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < k + 1)).mpr
    nlinarith
  apply (sq_le_sq₀ (subsetMoment_nonneg hc _ _)
    (mul_nonneg (by norm_num) (subsetMoment_nonneg hc _ _))).mp
  calc
    _ ≤ _ := subsetMoment_succ_sq_le hc r k hk
    _ ≤ (1 / 4 : ℝ) * subsetMoment c r k ^ 2 :=
      mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
    _ = _ := by ring

/-- Every fixed exponential/polynomial moment of the manuscript's `w_k`
is summable. This is an all-order ratio proof, not a finite tail test. -/
theorem subsetMoment_summable {c : ℝ} (hc : 0 ≤ c) (r : ℕ) :
    Summable (subsetMoment c r) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (48 * ((2 : ℝ) ^ r) ^ 2 * c ^ 2)
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  apply eventually_atTop.mpr
  refine ⟨N + 1, fun k hk => ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (subsetMoment_nonneg hc _ _),
    abs_of_nonneg (subsetMoment_nonneg hc _ _)]
  apply subsetMoment_succ_le_half hc r k (by omega)
  have hNk : N ≤ k + 1 := by omega
  exact hN.trans (by exact_mod_cast hNk)

theorem subsetMoment_add_le_geometric {c : ℝ} (hc : 0 ≤ c) (r N m : ℕ) (hN : 1 ≤ N)
    (hcut : 48 * ((2 : ℝ) ^ r) ^ 2 * c ^ 2 ≤ (N + 1 : ℝ)) :
    subsetMoment c r (N + m) ≤ subsetMoment c r N * (1 / 2 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep := subsetMoment_succ_le_half hc r (N + m) (by omega)
      (hcut.trans (by exact_mod_cast (show N + 1 ≤ (N + m) + 1 by omega)))
    calc
      _ ≤ (1 / 2 : ℝ) * subsetMoment c r (N + m) := by simpa [Nat.add_assoc] using hstep
      _ ≤ (1 / 2 : ℝ) * (subsetMoment c r N * (1 / 2 : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- A concrete tail certificate after the stated moment-dependent cutoff. -/
theorem subsetMoment_tail_le {c : ℝ} (hc : 0 ≤ c) (r N : ℕ) (hN : 1 ≤ N)
    (hcut : 48 * ((2 : ℝ) ^ r) ^ 2 * c ^ 2 ≤ (N + 1 : ℝ)) :
    (∑' m, subsetMoment c r (N + m)) ≤ 2 * subsetMoment c r N := by
  have hf : Summable (fun m => subsetMoment c r (N + m)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).mpr (subsetMoment_summable hc r)
  have hg : HasSum (fun m : ℕ => subsetMoment c r N * (1 / 2 : ℝ) ^ m)
      (2 * subsetMoment c r N) := by
    have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (subsetMoment c r N)
    convert h using 1
    ring
  exact (hf.tsum_le_tsum (fun m => subsetMoment_add_le_geometric hc r N m hN hcut)
    hg.summable).trans_eq hg.tsum_eq

/-- An explicit superexponential majorant valid at every order. -/
theorem subsetWeight_sq_le_factorial (k : ℕ) :
    subsetWeight k ^ 2 ≤ (12 : ℝ) ^ k / Nat.factorial k := by
  induction k with
  | zero => norm_num [subsetWeight]
  | succ k ih =>
    calc
      _ ≤ (12 / (k + 1 : ℝ)) * subsetWeight k ^ 2 := subsetWeight_succ_sq_le k
      _ ≤ (12 / (k + 1 : ℝ)) * ((12 : ℝ) ^ k / Nat.factorial k) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        rw [div_mul_div_comm]
        ring

/-- The `-(k/2) log k + O(k)` estimate used in the manuscript, with an
explicit absolute linear coefficient. -/
theorem subsetWeight_log_le (k : ℕ) (hk : 1 ≤ k) :
    Real.log (subsetWeight k) ≤
      (k : ℝ) / 2 * (Real.log 12 + 1 - Real.log k) := by
  have h := Real.log_le_log (sq_pos_of_pos (subsetWeight_pos k)) (subsetWeight_sq_le_factorial k)
  rw [Real.log_pow, Real.log_div (by positivity) (by positivity), Real.log_pow] at h
  norm_num only at h
  have hStirling := Stirling.le_log_factorial_stirling (show k ≠ 0 by omega)
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hk)
  have hlogpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  nlinarith

theorem subsetWeight_le_exp (k : ℕ) (hk : 1 ≤ k) :
    subsetWeight k ≤ Real.exp ((k : ℝ) / 2 * (Real.log 12 + 1 - Real.log k)) := by
  rw [← Real.exp_log (subsetWeight_pos k)]
  exact Real.exp_le_exp.mpr (subsetWeight_log_le k hk)

theorem subsetWeight_exp_tail_le {c : ℝ} (hc : 0 ≤ c) (N : ℕ) (hN : 1 ≤ N)
    (hcut : 48 * c ^ 2 ≤ (N + 1 : ℝ)) :
    (∑' m, c ^ (N + m) * subsetWeight (N + m)) ≤
      2 * c ^ N * Real.exp ((N : ℝ) / 2 * (Real.log 12 + 1 - Real.log N)) := by
  have h := subsetMoment_tail_le hc 0 N hN (by simpa using hcut)
  simp only [subsetMoment, pow_zero, one_mul] at h
  calc
    _ ≤ 2 * (c ^ N * subsetWeight N) := h
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (subsetWeight_le_exp N hN) (by positivity)

end TournamentHamiltonian
