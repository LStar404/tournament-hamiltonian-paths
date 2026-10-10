import TournamentHamiltonian.PairedPermanentGaussian
import TournamentHamiltonian.PairedPermanentErrorBudget
import TournamentHamiltonian.RectangularPermanentUnconditional

namespace TournamentHamiltonian

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Uniform paired/nonprincipal estimate, with no assumed scaling witness,
no assumed Gaussian comparison and no assumed core-activity bound. -/
theorem adjacency_nonprincipal_gaussian_uniform_log {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 20 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), ∀ hI : I.card = t, ∀ hJ : J.card = t,
          rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J)
            (deletedComplementEquiv I J (hI.trans hJ.symm)) ≤
            pairedScoreProduct T * (∏ i ∈ I, pairedLeft (tournamentScorePotential T i)) *
              (∏ j ∈ J, pairedRight (tournamentScorePotential T j)) *
                ((n - t).factorial : ℝ) / (2 : ℝ) ^ (n - t) * gaussianFactor T *
                  Real.exp (-1 + K * pairedPermanentErrorBudget n t (scoreVariance T)) := by
  obtain ⟨Ng, hNg, hg⟩ := exists_preconditioned_scaling_gaussian_cost_uniform_log hA hB h0 h1
  obtain ⟨Np, _hNp, hp⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  obtain ⟨Nm, _hNm, hm⟩ := preconditioned_mass_uniform_lower_log hA h0 h1
  refine ⟨pairedPermanentErrorConstant a0, pairedPermanentErrorConstant_pos a0,
    max Ng (max Np Nm), hNg.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNg : Ng ≤ n := by omega
  have hnNp : Np ≤ n := by omega
  have hnNm : Nm ≤ n := by omega
  have hn20 : 20 ≤ n := hNg.trans hnNg
  obtain ⟨ht2, ht, hM, hQ, _hη⟩ := hp n t hnNp T ha hvar hlog I J hI hJ
  have hMhalf := hm n hnNm T ha hvar
  obtain ⟨x, y, hxy, hcost⟩ := hg n t hnNg T ha hvar hlog I J hI hJ
  let X := normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J
  let e := deletedComplementEquiv I J (hI.trans hJ.symm)
  let K := preconditioningScalingDensity a0
  let C := preconditioningScalingCenteredDensity a0
  let eps := preconditioningScalingEpsilon a0
  have hK : 0 ≤ K := by dsimp [K, preconditioningScalingDensity]; positivity
  have hcard : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  have hdi : (Classical.decEq (Iᶜ : Finset (Fin n))) =
      (fun a b => a.instDecidableEq b) := Subsingleton.elim _ _
  have hdj : (Classical.decEq (Jᶜ : Finset (Fin n))) =
      (fun a b => a.instDecidableEq b) := Subsingleton.elim _ _
  have hxyc : @RectangularScalingWitness _ _ _ _ (Classical.decEq _) (Classical.decEq _)
      X e K C (9 / 10) eps x y := by rw [hdi, hdj]; exact hxy
  have hactivity := rectangularScaling_actualCoreActivities X e hcard K C (9 / 10) eps
    hK (by norm_num) (by norm_num) x y hxyc
  have ha1 (i : Fin n) : -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1 := by
    have hi := abs_le.mp (ha i)
    constructor <;> linarith
  have hupper := adjacency_nonprincipal_gaussian_upper_of_activities T (by omega) I J hI hJ ht
    ha1 hM hQ K C (9 / 10) eps hK (by norm_num) (by norm_num) x y hxy hactivity
    (preconditioningGaussianCostConstant a0 *
      (Real.sqrt (scoreVariance T / n) + ((t : ℝ) + 1) / n)) hcost
  rw [show (1 + (9 / 10 : ℝ)) / 2 = 19 / 20 by norm_num] at hupper
  have herror := paired_permanent_error_exponent_le T (by omega) a0 h0 h1 ha hMhalf I J hI hJ ht2
  have hscore := paired_restoration_factor_nonneg T I J ha1
  have hD := (gaussianFactor_bounds T (by omega)).1
  apply hupper.trans
  apply mul_le_mul_of_nonneg_left
  · exact Real.exp_le_exp.mpr (by dsimp only [K]; linarith [herror])
  · positivity

end TournamentHamiltonian
