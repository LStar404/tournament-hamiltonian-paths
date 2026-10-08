import TournamentHamiltonian.FactorialRecovery
import TournamentHamiltonian.GramLipschitz
import TournamentHamiltonian.FrobeniusGeometry
import Mathlib.Analysis.SpecificLimits.Normed

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def geometricSecondMoment (r : ℝ) : ℝ := r * (1 + r) / (1 - r) ^ 3

omit [DecidableEq ι] in
theorem bilinearGaussianCoefficient_weighted_second_moment_le (Z : Matrix ι κ ℝ)
    (sigma R : ℝ) (hs : 1 < sigma) (hsR : sigma < R) (hgap : R * ‖Z‖ < 1) (s : Finset ℕ) :
    (∑ k ∈ s, (k : ℝ) ^ 2 * bilinearGaussianCoefficient Z k * sigma ^ k) ≤
      geometricSecondMoment (sigma / R) * gramGaussian (R • Z) := by
  have hR : 0 < R := by linarith
  have hr0 : 0 ≤ sigma / R := div_nonneg (by linarith) hR.le
  have hr1 : sigma / R < 1 := (div_lt_one hR).mpr hsR
  have hrnorm : ‖sigma / R‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hseries := hasSum_sq_mul_geometric_of_norm_lt_one hrnorm
  have hsum := sum_le_hasSum s (fun k _ => mul_nonneg (sq_nonneg (k : ℝ)) (pow_nonneg hr0 k)) hseries
  have hpoint (k : ℕ) : (k : ℝ) ^ 2 * bilinearGaussianCoefficient Z k * sigma ^ k ≤
      ((k : ℝ) ^ 2 * (sigma / R) ^ k) * gramGaussian (R • Z) := by
    have hc := bilinearGaussianCoefficient_finite_sum_le Z R hR.le hgap {k}
    have hdec : (Classical.decEq κ : DecidableEq κ) = (inferInstance : DecidableEq κ) := Subsingleton.elim _ _
    rw [hdec] at hc
    simp only [Finset.sum_singleton] at hc
    have h := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ (k : ℝ) ^ 2 * (sigma / R) ^ k by positivity)
    have hp : (sigma / R) ^ k * R ^ k = sigma ^ k := by
      rw [← mul_pow, div_mul_cancel₀ _ hR.ne']
    have heq : ((k : ℝ) ^ 2 * (sigma / R) ^ k) * (bilinearGaussianCoefficient Z k * R ^ k) =
        (k : ℝ) ^ 2 * bilinearGaussianCoefficient Z k * sigma ^ k := by
      calc
        _ = (k : ℝ) ^ 2 * bilinearGaussianCoefficient Z k * ((sigma / R) ^ k * R ^ k) := by ring
        _ = _ := by rw [hp]
    exact heq.symm.le.trans h
  have hG : 0 ≤ gramGaussian (R • Z) := by unfold gramGaussian; positivity
  have h := Finset.sum_le_sum (s := s) (fun k _ => hpoint k)
  rw [← Finset.sum_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_right hsum hG)

omit [DecidableEq ι] in
theorem gramGaussian_le_exp_frobenius_budget (Z : Matrix ι κ ℝ) (C q : ℝ)
    (_hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) (hF : realFrobeniusNorm Z ≤ C) :
    gramGaussian Z ≤ Real.exp (C ^ 2 / (2 * (1 - q ^ 2))) := by
  have hgram := gram_complement_posDef Z q hq hq1 hZ
  have hG : 0 < gramGaussian Z := by
    unfold gramGaussian
    exact inv_pos.mpr (Real.sqrt_pos.mpr hgram.det_pos)
  have hzero : gramGaussian (0 : Matrix ι κ ℝ) = 1 := by simp [gramGaussian]
  have hfzero : realFrobeniusNorm (0 : Matrix ι κ ℝ) = 0 := by simp [realFrobeniusNorm]
  have h := gramGaussian_log_lipschitz Z 0 q hq hq1 hZ (by simpa using hq)
  rw [hzero, Real.log_one, sub_zero, hfzero, add_zero, sub_zero] at h
  have hpow := pow_le_pow_left₀ (realFrobeniusNorm_nonneg Z) hF 2
  have hg : 0 < 2 * (1 - q ^ 2) := by nlinarith
  have hlog : Real.log (gramGaussian Z) ≤ C ^ 2 / (2 * (1 - q ^ 2)) := by
    apply (le_abs_self _).trans
    apply h.trans
    simpa only [pow_two] using div_le_div_of_nonneg_right hpow hg.le
  nth_rw 1 [← Real.exp_log hG]
  exact Real.exp_le_exp.mpr hlog

noncomputable def gaussianFactorialRecoveryBudget (C q sigma R : ℝ) : ℝ :=
  geometricSecondMoment (sigma / R) *
    Real.exp ((R * C) ^ 2 / (2 * (1 - (R * q) ^ 2)))

omit [DecidableEq ι] in
theorem gaussian_factorial_recovery_le (n : ℕ) (hn : 0 < n) (Z : Matrix ι κ ℝ)
    (C q sigma R : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hs : 1 < sigma) (hsR : sigma < R)
    (hRq : R * q < 1) (hZ : ‖Z‖ ≤ q) (hF : realFrobeniusNorm Z ≤ C) (s : Finset ℕ)
    (hwindow : ∀ k ∈ s, 2 * k ≤ n ∧ (k : ℝ) / n ≤ Real.log sigma) :
    (∑ k ∈ s, (factorialRecoveryRatio n k - 1) * bilinearGaussianCoefficient Z k) ≤
      gaussianFactorialRecoveryBudget C q sigma R / n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hR : 0 < R := by linarith
  have hgap : R * ‖Z‖ < 1 :=
    (mul_le_mul_of_nonneg_left hZ hR.le).trans_lt hRq
  have hZR : ‖R • Z‖ ≤ R * q := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact mul_le_mul_of_nonneg_left hZ hR.le
  have hFR : realFrobeniusNorm (R • Z) ≤ R * C := by
    rw [realFrobeniusNorm_smul, abs_of_pos hR]
    exact mul_le_mul_of_nonneg_left hF hR.le
  have hG := gramGaussian_le_exp_frobenius_budget (R • Z) (R * C) (R * q)
    (by positivity) (by positivity) hRq hZR hFR
  have hr0 : 0 ≤ sigma / R := by positivity
  have hr1 : sigma / R < 1 := (div_lt_one hR).mpr hsR
  have hH : 0 ≤ geometricSecondMoment (sigma / R) := by
    unfold geometricSecondMoment
    positivity
  have hmoment := (bilinearGaussianCoefficient_weighted_second_moment_le Z sigma R hs hsR hgap s).trans
    (mul_le_mul_of_nonneg_left hG hH)
  have hpoint (k : ℕ) (hk : k ∈ s) :
      (factorialRecoveryRatio n k - 1) * bilinearGaussianCoefficient Z k ≤
        ((k : ℝ) ^ 2 * bilinearGaussianCoefficient Z k * sigma ^ k) / n := by
    have hb := (factorialRecoveryRatio_sub_one_bound n k hn (hwindow k hk).1 sigma hs (hwindow k hk).2).2
    have h := mul_le_mul_of_nonneg_right hb (bilinearGaussianCoefficient_nonneg Z k)
    exact h.trans_eq (by ring)
  calc
    _ ≤ ∑ k ∈ s, ((k : ℝ) ^ 2 * bilinearGaussianCoefficient Z k * sigma ^ k) / n :=
      Finset.sum_le_sum (fun k hk => hpoint k hk)
    _ = (∑ k ∈ s, (k : ℝ) ^ 2 * bilinearGaussianCoefficient Z k * sigma ^ k) / n := by rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right hmoment hnR.le

end TournamentHamiltonian
