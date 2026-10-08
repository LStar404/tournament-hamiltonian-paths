import TournamentHamiltonian.UniformSmallScoreMinor
import TournamentHamiltonian.HighVariance

open Filter
open scoped BigOperators Topology

namespace TournamentHamiltonian

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem smallScoreUniformLogConstant_le_permanentConstant :
    smallScoreUniformLogConstant ≤ smallScoreUniformPermanentConstant := by
  have hP := uniformPermanentActivityConstant_nonneg 65 (19 / 20) (by norm_num) (by norm_num)
  have hL := smallScoreUniformLogConstant_pos
  unfold smallScoreUniformPermanentConstant
  linarith

theorem logarithmic_unit_score_budget_tendsto_zero (c : ℝ) :
    Tendsto (fun n : ℕ => c * (Real.log (n : ℝ) + 2) ^ 2 / n) atTop (𝓝 0) := by
  have h1 := log_pow_div_sqrt_nat_tendsto_zero 1
  have h0 := (log_pow_div_sqrt_nat_tendsto_zero 0).const_mul (2 : ℝ)
  simp only [pow_one] at h1
  simp only [pow_zero, mul_zero] at h0
  have h := ((h1.add h0).pow 2).const_mul c
  simp only [zero_add, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at h
  convert h using 1
  ext n
  rw [show Real.log (n : ℝ) / Real.sqrt n + 2 * (1 / Real.sqrt n) =
    (Real.log (n : ℝ) + 2) / Real.sqrt n by ring, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

theorem unit_score_cutoff_budget_eventually_small (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, k ≤ subsetCutoff n → c * ((k : ℝ) + 2) ^ 2 / n ≤ 1 := by
  filter_upwards [(logarithmic_unit_score_budget_tendsto_zero c).eventually_le_const
    (by norm_num : (0 : ℝ) < 1), short_cutoff_eventually_small] with n hn hcut k hk
  have hkR : (k : ℝ) + 2 ≤ Real.log n + 2 := by
    have hkc : (k : ℝ) ≤ subsetCutoff n := by exact_mod_cast hk
    linarith [hcut.2.1]
  have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2)
    (by linarith [Nat.cast_nonneg (α := ℝ) k] : (0 : ℝ) ≤ Real.log n + 2)).mpr hkR
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc)
    (Nat.cast_nonneg n)).trans hn

theorem rectangularPermanent_principal_deleted {n : ℕ} (T : Tournament n) (U : Finset (Fin n)) :
    rectangularPermanent (nonprincipalSubmatrix (adjacency T) U U)
      (deletedComplementEquiv U U rfl) =
        ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent := by
  rw [rectangularPermanent_independent _ _ (Equiv.refl _)]
  rfl

/-- A single threshold supplies the actual principal short-minor lower and
absolute approximation bounds for every tournament with unit score bound. -/
theorem unit_score_principal_minors_uniform :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ T : Tournament n,
      (∀ i, |score T i| ≤ 1) →
      scoreVariance T ≤ 1 ∧ ∀ U : Finset (Fin n), U.card < subsetCutoff n →
        smallScoreUniformPermanentConstant * ((U.card : ℝ) + 2) ^ 2 / n ≤ 1 ∧
        |((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent -
          Real.exp (-1) * gaussianFactor T * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))| ≤
            Real.exp (-1) * gaussianFactor T * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
              (smallScoreUniformPermanentConstant * ((U.card : ℝ) + 2) ^ 2 / n) ∧
        Real.exp (-1) * gaussianFactor T * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
          (1 - smallScoreUniformPermanentConstant * ((U.card : ℝ) + 2) ^ 2 / n) ≤
            ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent := by
  obtain ⟨Ns, hNs, hs⟩ := adjacency_nonprincipal_small_score_uniform (by norm_num : (0 : ℝ) ≤ 1)
  have hevent : ∀ᶠ n : ℕ in atTop, 20 ≤ n ∧ ∀ T : Tournament n, (∀ i, |score T i| ≤ 1) →
      scoreVariance T ≤ 1 ∧ ∀ U : Finset (Fin n), U.card < subsetCutoff n →
        smallScoreUniformPermanentConstant * ((U.card : ℝ) + 2) ^ 2 / n ≤ 1 ∧
        |((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent -
          Real.exp (-1) * gaussianFactor T * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))| ≤
            Real.exp (-1) * gaussianFactor T * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
              (smallScoreUniformPermanentConstant * ((U.card : ℝ) + 2) ^ 2 / n) ∧
        Real.exp (-1) * gaussianFactor T * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
          (1 - smallScoreUniformPermanentConstant * ((U.card : ℝ) + 2) ^ 2 / n) ≤
            ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent := by
    filter_upwards [unit_score_cutoff_budget_eventually_small smallScoreUniformPermanentConstant
      smallScoreUniformPermanentConstant_pos.le, short_cutoff_eventually_small, eventually_ge_atTop Ns]
      with n hbudget hcut hn
    have hn20 : 20 ≤ n := hNs.trans hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    refine ⟨hn20, ?_⟩
    intro T hscore
    have htau : scoreVariance T ≤ 1 := by
      have hv := scoreVariance_le_score_budget T (by omega) 1 (by norm_num) hscore
      have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
      have hdiv : (4 : ℝ) / n ≤ 1 := (div_le_one hnR).mpr hn4
      norm_num only [one_pow, mul_one] at hv
      exact hv.trans hdiv
    refine ⟨htau, ?_⟩
    intro U hU
    have hsmall := hbudget U.card hU.le
    have hk : (U.card : ℝ) ≤ (1 : ℝ) * Real.log n := by
      have hkc : (U.card : ℝ) ≤ subsetCutoff n := by exact_mod_cast hU.le
      simpa only [one_mul] using hkc.trans hcut.2.1
    have hlogsmall : smallScoreUniformLogConstant * ((U.card : ℝ) + 2) ^ 2 / n ≤ 1 :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        smallScoreUniformLogConstant_le_permanentConstant (sq_nonneg _)) hnR.le).trans hsmall
    have herror := hs n U.card hn T 1 (by norm_num) hscore htau hk
      (by simpa only [show (1 : ℝ) + (U.card : ℝ) + 1 = U.card + 2 by ring] using hlogsmall)
      U U rfl rfl
    rw [rectangularPermanent_principal_deleted] at herror
    simp only [show (1 : ℝ) + (U.card : ℝ) + 1 = U.card + 2 by ring] at herror
    refine ⟨hsmall, herror, ?_⟩
    have hlower := (abs_le.mp herror).1
    nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨max N 20, le_max_right _ _, ?_⟩
  intro n hn
  exact (hN n ((le_max_left N 20).trans hn)).2

end TournamentHamiltonian
