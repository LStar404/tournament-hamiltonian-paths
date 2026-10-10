import TournamentHamiltonian.SmallScoreActualLogBudget
import TournamentHamiltonian.UniformRetainedMassHalf
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped BigOperators Matrix.Norms.L2Operator

namespace TournamentHamiltonian

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable def smallScoreUniformLogConstant : ℝ := smallScoreRestorationConstant 35 (9 / 10)

noncomputable def smallScoreUniformPermanentConstant : ℝ :=
  6 * uniformPermanentActivityConstant 65 (19 / 20) + 2 * smallScoreUniformLogConstant

theorem smallScoreUniformLogConstant_pos : 0 < smallScoreUniformLogConstant :=
  smallScoreRestorationConstant_pos _ _

theorem smallScoreUniformPermanentConstant_pos : 0 < smallScoreUniformPermanentConstant := by
  have hP := uniformPermanentActivityConstant_nonneg 65 (19 / 20) (by norm_num) (by norm_num)
  have hL := smallScoreUniformLogConstant_pos
  unfold smallScoreUniformPermanentConstant
  positivity

theorem small_score_budget_implies_quarter (N d t K : ℝ) (hn : 0 < N)
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hK : 3008 ≤ K)
    (hsmall : K * (d + t + 1) ^ 2 / N ≤ 1) : 4 * d ≤ N := by
  have hS : 1 ≤ d + t + 1 := by linarith
  have hs2 : d + t + 1 ≤ (d + t + 1) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hK (sq_nonneg (d + t + 1))
  have hbudget := (div_le_one hn).mp hsmall
  nlinarith

theorem preconditionedDeletedMarginalBudget_small_score {n t : ℕ} (T : Tournament n)
    (hn : 2 ≤ n) (d : ℝ) (hd : 0 ≤ d) (hs : ∀ i, |score T i| ≤ d) :
    preconditionedDeletedMarginalBudget n t (scoreVariance T) (1 / 2) ≤
      64 * (d + (t : ℝ) + 1) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hroot := mul_le_mul_of_nonneg_left (score_sqrt_le_score_budget T hn d hd hs)
    (by norm_num : (0 : ℝ) ≤ 32)
  unfold preconditionedDeletedMarginalBudget
  norm_num only
  calc
    _ ≤ 32 * (2 * d / n) + 32 * (t : ℝ) / n + 4 * (1 + 4 * t) / n :=
      add_le_add (add_le_add hroot le_rfl) le_rfl
    _ = (64 * d + 48 * (t : ℝ) + 4) / n := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) t]) hnR.le

/-- The actual small-score short-minor approximation. All mass, balancing,
Gaussian and core-activity inputs are proved internally under one threshold. -/
theorem adjacency_nonprincipal_small_score_uniform {B : ℝ} (hB : 0 ≤ B) :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, ∀ d : ℝ, 0 ≤ d → (∀ i, |score T i| ≤ d) →
        scoreVariance T ≤ 1 → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        smallScoreUniformLogConstant * (d + (t : ℝ) + 1) ^ 2 / n ≤ 1 →
        ∀ I J : Finset (Fin n), ∀ hI : I.card = t, ∀ hJ : J.card = t,
          |rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J)
              (deletedComplementEquiv I J (hI.trans hJ.symm)) -
            Real.exp (-1) * gaussianFactor T * (((n - t).factorial : ℝ) / (2 : ℝ) ^ (n - t))| ≤
              Real.exp (-1) * gaussianFactor T * (((n - t).factorial : ℝ) / (2 : ℝ) ^ (n - t)) *
                (smallScoreUniformPermanentConstant * (d + (t : ℝ) + 1) ^ 2 / n) := by
  obtain ⟨Ng, hNg, hg⟩ := exists_preconditioned_scaling_gaussian_cost_uniform_log
    (by norm_num : (0 : ℝ) ≤ 1) hB (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨Nh, _hNh, hh⟩ := preconditioned_normalization_masses_uniform_half_log
    (by norm_num : (0 : ℝ) ≤ 1) hB (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨Nr, _hNr, hmarg⟩ := preconditioned_deleted_marginal_budget_uniform_log
    (by norm_num : (0 : ℝ) ≤ 1) hB (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨max Ng (max Nh Nr), hNg.trans (le_max_left _ _), ?_⟩
  intro n t hn T d hd hs htau hlog hsmall I J hI hJ
  have hnNg : Ng ≤ n := by omega
  have hnNh : Nh ≤ n := by omega
  have hnNr : Nr ≤ n := by omega
  have hn20 : 20 ≤ n := hNg.trans hnNg
  have hn2 : 2 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd4 := small_score_budget_implies_quarter n d t smallScoreUniformLogConstant hnR hd
    (Nat.cast_nonneg _) (smallScoreRestorationConstant_lower _ _) hsmall
  have hdn : d ≤ n := by linarith
  have ha (i : Fin n) : |tournamentScorePotential T i| ≤ 1 / 2 := by
    apply (tournamentScorePotential_le_score_budget T hn2 d hd hs i).trans
    exact (div_le_iff₀ hnR).mpr (by linarith)
  have hlog1 : (1 : ℝ) ≤ Real.log n := by
    have hthree : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.le.trans hthree)
  have hvar : scoreVariance T ≤ (1 : ℝ) * Real.log n := by simpa only [one_mul] using htau.trans hlog1
  obtain ⟨ht2, ht, hMhalf, hQhalf⟩ := hh n t hnNh T ha hvar hlog I J hI hJ
  rw [Nat.cast_sub ht.le] at hQhalf
  have hmR : (0 : ℝ) < n - t := by
    have htn : (t : ℝ) < n := by exact_mod_cast ht
    linarith
  have hmNatPos : (0 : ℝ) < (n - t : ℕ) := by rw [Nat.cast_sub ht.le]; exact hmR
  have hM : 0 < matrixEntryMass (preconditionedTournamentDensity T) := by linarith
  have hQ : 0 < matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) := by linarith
  obtain ⟨x, y, hxy, hcost⟩ := hg n t hnNg T ha hvar hlog I J hI hJ
  obtain ⟨hr, hc, _hdisp⟩ := hmarg n t hnNr T ha hvar hlog I J hI hJ
  have hr' i := (hr i).trans (preconditionedDeletedMarginalBudget_small_score T hn2 d hd hs)
  have hc' j := (hc j).trans (preconditionedDeletedMarginalBudget_small_score T hn2 d hd hs)
  norm_num only [preconditioningScalingDensity, preconditioningScalingCenteredDensity] at hxy
  have hlogbudget := nonprincipalRestorationLog_small_score T hn2 ht d hd hdn hs ha htau
    I J hI hJ ht2 hMhalf hQhalf 32 35 (9 / 10) (preconditioningScalingEpsilon (1 / 2))
    x y hxy hr' hc' hcost
  let X := normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J
  let Y := rectangularExpScaling X x y
  let e := deletedComplementEquiv I J (hI.trans hJ.symm)
  have hcard : Fintype.card (Iᶜ : Finset (Fin n)) = n - t := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
  have hcardpos : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by rw [hcard]; omega
  have hgapq : ‖Y - rectangularAverageMatrix _ _‖ ≤ (19 / 20 : ℝ) := by
    convert hxy.gap using 1
    norm_num
  have hentry i j : |Y i j| ≤ (64 : ℝ) / Fintype.card (Iᶜ : Finset (Fin n)) := by
    simpa only [show (2 : ℝ) * 32 = 64 by norm_num] using hxy.density i j
  have herror := rectangularPermanent_approximation_from_matrix_bounds Y e hcardpos 64 (19 / 20)
    (by norm_num) (by norm_num) (by norm_num) hxy.row_sum hxy.column_sum hentry hgapq
  have hGdec : @gramGaussian _ _ _ _ (Classical.decEq _) (Y - rectangularAverageMatrix _ _) =
      gramGaussian (Y - rectangularAverageMatrix _ _) := by congr 1
  have hPdec : @rectangularPermanent _ _ _ (Classical.decEq _) Y e = rectangularPermanent Y e := by congr 1
  rw [hGdec, hPdec, hcard, show (64 : ℝ) + 1 = 65 by norm_num] at herror
  have hp := uniformPermanentActivityConstant_nonneg 65 (19 / 20) (by norm_num) (by norm_num)
  have hD := (gaussianFactor_bounds T (by omega)).1
  have ha1 (i : Fin n) : -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1 := by
    have hi := abs_le.mp (ha i)
    constructor <;> linarith
  have hrestore := adjacency_nonprincipal_gaussian_error_from_actual_budgets T hn2 I J hI hJ ht
    ha1 hM hQ x y (smallScoreUniformLogConstant * (d + (t : ℝ) + 1) ^ 2 / n)
    (uniformPermanentActivityConstant 65 (19 / 20) / ((n - t : ℕ) : ℝ))
    (by positivity) hsmall (hgapq.trans_lt (by norm_num)) herror hlogbudget
  apply hrestore.trans
  apply mul_le_mul_of_nonneg_left
  · have hper : uniformPermanentActivityConstant 65 (19 / 20) / ((n - t : ℕ) : ℝ) ≤
        2 * uniformPermanentActivityConstant 65 (19 / 20) / n := by
      rw [Nat.cast_sub ht.le]
      have hhR : (n : ℝ) / 2 ≤ n - t := by
        have htR : 2 * (t : ℝ) ≤ n := by exact_mod_cast ht2
        linarith
      have h := div_le_div_of_nonneg_left hp (by positivity : (0 : ℝ) < n / 2) hhR
      exact h.trans_eq (by ring)
    have hS : 1 ≤ (d + (t : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) t]
    have hmul := mul_le_mul_of_nonneg_left hS (show 0 ≤ 6 * uniformPermanentActivityConstant 65 (19 / 20) / n by positivity)
    unfold smallScoreUniformPermanentConstant
    have hcore : 3 * (uniformPermanentActivityConstant 65 (19 / 20) / ((n - t : ℕ) : ℝ)) ≤
        6 * uniformPermanentActivityConstant 65 (19 / 20) * (d + (t : ℝ) + 1) ^ 2 / n := by
      calc
        _ ≤ 3 * (2 * uniformPermanentActivityConstant 65 (19 / 20) / n) :=
          mul_le_mul_of_nonneg_left hper (by norm_num)
        _ = 6 * uniformPermanentActivityConstant 65 (19 / 20) / n := by ring
        _ ≤ (6 * uniformPermanentActivityConstant 65 (19 / 20) / n) * (d + (t : ℝ) + 1) ^ 2 := by
          simpa only [mul_one] using hmul
        _ = _ := by ring
    convert add_le_add hcore (le_refl (2 * (smallScoreUniformLogConstant * (d + (t : ℝ) + 1) ^ 2 / n))) using 1
    ring
  · positivity

end TournamentHamiltonian
