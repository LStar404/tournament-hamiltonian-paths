import TournamentHamiltonian.GeneralSmallScorePaths

namespace TournamentHamiltonian
open Filter
open scoped Topology Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem small_score_logarithmic_budget_tendsto_zero (d : ℕ → ℝ)
    (hd : Tendsto (fun n => d n / Real.sqrt n) atTop (𝓝 0)) (c : ℝ) :
    Tendsto (fun n : ℕ => c * (d n + Real.log n + 1) ^ 2 / n) atTop (𝓝 0) := by
  have hlog := log_pow_div_sqrt_nat_tendsto_zero 1
  have hunit := log_pow_div_sqrt_nat_tendsto_zero 0
  simp only [pow_one] at hlog
  simp only [pow_zero] at hunit
  have h := (((hd.add hlog).add hunit).pow 2).const_mul c
  simp only [zero_add, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at h
  convert h using 1
  ext n
  rw [show d n / Real.sqrt n + Real.log n / Real.sqrt n + 1 / Real.sqrt n =
    (d n + Real.log n + 1) / Real.sqrt n by ring, div_pow,
    Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

theorem small_score_quadratic_budget_tendsto_zero (d : ℕ → ℝ)
    (hd : Tendsto (fun n => d n / Real.sqrt n) atTop (𝓝 0)) (c : ℝ) :
    Tendsto (fun n : ℕ => c * (d n + 1) ^ 2 / n) atTop (𝓝 0) := by
  have hunit := log_pow_div_sqrt_nat_tendsto_zero 0
  simp only [pow_zero] at hunit
  have h := ((hd.add hunit).pow 2).const_mul c
  simp only [zero_add, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at h
  convert h using 1
  ext n
  rw [show d n / Real.sqrt n + 1 / Real.sqrt n = (d n + 1) / Real.sqrt n by ring,
    div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

/-- Every nonnegative score envelope of order o(sqrt n) supplies the actual
variance and original short-minor error conditions under one threshold. -/
theorem small_score_path_hypotheses_eventually (d : ℕ → ℝ) (hd0 : ∀ n, 0 ≤ d n)
    (hd : Tendsto (fun n => d n / Real.sqrt n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      smallScoreUniformPermanentConstant * (d n + (subsetCutoff n : ℝ) + 1) ^ 2 / n ≤ 1 ∧
      ∀ T : Tournament n, (∀ i, |score T i| ≤ d n) → scoreVariance T ≤ 1 := by
  have hlog := (small_score_logarithmic_budget_tendsto_zero d hd
    smallScoreUniformPermanentConstant).eventually_le_const (by norm_num : (0 : ℝ) < 1)
  have hquad := (small_score_quadratic_budget_tendsto_zero d hd 4).eventually_le_const
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hlog, hquad, short_cutoff_eventually_small] with n hnlog hnquad hcut
  have hdN := hd0 n
  have hsq : (d n + (subsetCutoff n : ℝ) + 1) ^ 2 ≤ (d n + Real.log n + 1) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by linarith [hd0 n, Nat.cast_nonneg (α := ℝ) (subsetCutoff n)])).mpr
    linarith [hcut.2.1]
  refine ⟨(div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq
    smallScoreUniformPermanentConstant_pos.le) (Nat.cast_nonneg n)).trans hnlog, ?_⟩
  intro T hs
  have hn2 : 2 ≤ n := by omega
  apply (scoreVariance_le_score_budget T hn2 (d n) (hd0 n) hs).trans
  apply le_trans _ hnquad
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  nlinarith [hd0 n]

/-- The paper's whole-path approximation for every actual tournament whose
scores lie under an arbitrary o(sqrt n) envelope. No minor, activity, scaling,
Gaussian, variance or logarithmic-window assumptions remain. -/
theorem small_score_pathCount_spectral_approximation_eventually
    (d : ℕ → ℝ) (hd0 : ∀ n, 0 ≤ d n)
    (hd : Tendsto (fun n => d n / Real.sqrt n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n, (∀ i, |score T i| ≤ d n) →
      |(pathCount T : ℝ) / meanPaths n - spectralRatio T| ≤
        unitScorePathApproximationConstant * (d n + 1) ^ 2 / n := by
  obtain ⟨N, _hN, hN⟩ := score_pathCount_spectral_approximation_uniform
  filter_upwards [eventually_ge_atTop N, small_score_path_hypotheses_eventually d hd0 hd]
    with n hn hbudget T hs
  exact hN n hn T (d n) (hd0 n) hs (hbudget.2 T hs) hbudget.1

/-- In particular the whole-path spectral approximation has uniformly
vanishing error over every such score envelope. -/
theorem small_score_pathCount_spectral_error_eventually_small
    (d : ℕ → ℝ) (hd0 : ∀ n, 0 ≤ d n)
    (hd : Tendsto (fun n => d n / Real.sqrt n) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n, (∀ i, |score T i| ≤ d n) →
      |(pathCount T : ℝ) / meanPaths n - spectralRatio T| ≤ ε := by
  filter_upwards [small_score_pathCount_spectral_approximation_eventually d hd0 hd,
    (small_score_quadratic_budget_tendsto_zero d hd unitScorePathApproximationConstant).eventually_le_const hε]
    with n hn herror T hs
  exact (hn T hs).trans herror

end TournamentHamiltonian
