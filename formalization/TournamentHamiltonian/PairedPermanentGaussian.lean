import TournamentHamiltonian.ScaledPermanentGaussian
import TournamentHamiltonian.RetainedMassPower

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

theorem paired_restoration_factor_nonneg {n : ℕ} (T : Tournament n) (I J : Finset (Fin n))
    (ha : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1) :
    0 ≤ pairedScoreProduct T * (∏ i ∈ I, pairedLeft (tournamentScorePotential T i)) *
      (∏ j ∈ J, pairedRight (tournamentScorePotential T j)) := by
  have hscore : 0 ≤ pairedScoreProduct T := by
    unfold pairedScoreProduct
    apply Finset.prod_nonneg
    intro i _
    have h1 : 0 < 1 + tournamentScorePotential T i := by linarith [(ha i).1]
    have h2 : 0 < 1 - tournamentScorePotential T i := by linarith [(ha i).2]
    nlinarith [mul_pos h1 h2]
  have hl : 0 ≤ ∏ i ∈ I, pairedLeft (tournamentScorePotential T i) := by
    apply Finset.prod_nonneg
    intro i _
    exact inv_nonneg.mpr (by linarith [(ha i).1])
  have hr : 0 ≤ ∏ j ∈ J, pairedRight (tournamentScorePotential T j) := by
    apply Finset.prod_nonneg
    intro j _
    exact inv_nonneg.mpr (by linarith [(ha j).2])
  positivity

/-- Finite paired/nonprincipal permanent upper bound. The same genuine x,y
witness supplies balancing, the actual Gaussian log cost and restoration.
The displayed activity premise is on that actual scaled centered matrix. -/
theorem adjacency_nonprincipal_gaussian_upper_of_activities {n t : ℕ} (T : Tournament n)
    (hn : 2 ≤ n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t) (ht : t < n)
    (ha : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1)
    (hM : 0 < matrixEntryMass (preconditionedTournamentDensity T))
    (hQ : 0 < matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J))
    (K C q eps : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (x : (Iᶜ : Finset (Fin n)) → ℝ) (y : (Jᶜ : Finset (Fin n)) → ℝ)
    (hxy : RectangularScalingWitness
      (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J)
      (deletedComplementEquiv I J (hI.trans hJ.symm)) K C q eps x y)
    (hactivity : ActualCoreActivities (rectangularPermanentKernel
      (rectangularExpScaling (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y)
      (deletedComplementEquiv I J (hI.trans hJ.symm))) (2 * K + 1) ((1 + q) / 2))
    (δ : ℝ) (hcost : |Real.log (gramGaussian
      (rectangularExpScaling (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y -
        rectangularAverageMatrix _ _)) - Real.log (gaussianFactor T)| ≤ δ) :
    rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J)
      (deletedComplementEquiv I J (hI.trans hJ.symm)) ≤
        pairedScoreProduct T * (∏ i ∈ I, pairedLeft (tournamentScorePotential T i)) *
          (∏ j ∈ J, pairedRight (tournamentScorePotential T j)) *
            ((n - t).factorial : ℝ) / (2 : ℝ) ^ (n - t) * gaussianFactor T * Real.exp
              (-1 + (t : ℝ) / n + |matrixEntryMass (preconditionedTournamentDensity T) - n| +
                |matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) -
                  (n - t : ℝ)| + δ + uniformPermanentActivityConstant (2 * K + 1) ((1 + q) / 2) / (n - t)) := by
  let e := deletedComplementEquiv I J (hI.trans hJ.symm)
  let X := normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J
  let Y := rectangularExpScaling X x y
  let S := pairedScoreProduct T * (∏ i ∈ I, pairedLeft (tournamentScorePotential T i)) *
    (∏ j ∈ J, pairedRight (tournamentScorePotential T j))
  let η := preconditioningDeletionEta (t := t) T I J
  let c := uniformPermanentActivityConstant (2 * K + 1) ((1 + q) / 2) / ((n - t : ℕ) : ℝ)
  have hc : Fintype.card (Iᶜ : Finset (Fin n)) = n - t := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
  have hp : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by rw [hc]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmR : (0 : ℝ) < (n - t : ℕ) := by exact_mod_cast (show 0 < n - t by omega)
  have hη : 0 < η := by dsimp [η, preconditioningDeletionEta]; positivity
  have hS : 0 ≤ S := paired_restoration_factor_nonneg T I J ha
  have hbase : 0 ≤ (n - 1 : ℝ) / (2 * η) := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (by linarith) (by positivity)
  have hD : 0 < gaussianFactor T := (gaussianFactor_bounds T (by omega)).1
  have hrestore := adjacency_nonprincipal_true_scaling_upper T hn I J hI hJ ht ha hM hQ
    K C q eps x y hxy
  have hdi : (Classical.decEq (Iᶜ : Finset (Fin n))) =
      (fun a b => a.instDecidableEq b) := Subsingleton.elim _ _
  have hdj : (Classical.decEq (Jᶜ : Finset (Fin n))) =
      (fun a b => a.instDecidableEq b) := Subsingleton.elim _ _
  rw [← hdi, ← hdj] at hxy
  change @RectangularScalingWitness _ _ _ _ (Classical.decEq _) (Classical.decEq _)
    X e K C q eps x y at hxy
  change ActualCoreActivities (rectangularPermanentKernel (rectangularExpScaling X x y) e)
    (2 * K + 1) ((1 + q) / 2) at hactivity
  change |Real.log (gramGaussian (rectangularExpScaling X x y - rectangularAverageMatrix _ _)) -
    Real.log (gaussianFactor T)| ≤ δ at hcost
  have hGdec : @gramGaussian _ _ _ _ (Classical.decEq _) (rectangularExpScaling X x y -
      rectangularAverageMatrix _ _) = gramGaussian (rectangularExpScaling X x y -
      rectangularAverageMatrix _ _) := by
    congr 1
  have hcost' : |Real.log (@gramGaussian _ _ _ _ (Classical.decEq _)
      (rectangularExpScaling X x y - rectangularAverageMatrix _ _)) -
        Real.log (gaussianFactor T)| ≤ δ := by rw [hGdec]; exact hcost
  have hper := rectangularScaling_permanent_upper_from_log_cost X e hp K C q eps
    hK hq hq1 x y hxy hactivity (gaussianFactor T) δ hD hcost'
  rw [hc] at hper
  have hPdec : @rectangularPermanent _ _ _ (Classical.decEq _) Y e =
      rectangularPermanent Y e := by congr 1
  have hper' : rectangularPermanent Y e ≤
      ((n - t).factorial : ℝ) / ((n - t : ℕ) : ℝ) ^ (n - t) * gaussianFactor T *
        Real.exp (δ + c) := by rw [← hPdec]; exact hper
  change rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J) e ≤
    S * ((n - 1 : ℝ) / (2 * η)) ^ (n - t) * rectangularPermanent Y e at hrestore
  have h := hrestore.trans (mul_le_mul_of_nonneg_left hper'
    (mul_nonneg hS (pow_nonneg hbase (n - t))))
  change rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J) e ≤
    S * ((n - 1 : ℝ) / (2 * η)) ^ (n - t) *
      (((n - t).factorial : ℝ) / ((n - t : ℕ) : ℝ) ^ (n - t) * gaussianFactor T *
        Real.exp (δ + c)) at h
  have hpow : ((n - 1 : ℝ) / (2 * η)) ^ (n - t) *
      (((n - t).factorial : ℝ) / ((n - t : ℕ) : ℝ) ^ (n - t)) =
        ((n - t).factorial : ℝ) / (2 : ℝ) ^ (n - t) *
          ((n - 1 : ℝ) / (((n - t : ℕ) : ℝ) * η)) ^ (n - t) := by
    rw [div_pow, div_pow, mul_pow, mul_pow]
    ring
  have hm := preconditioning_mass_power_le T hn ht I J hM hQ
  rw [← Nat.cast_sub ht.le] at hm
  have hmul := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ S * (((n - t).factorial : ℝ) / (2 : ℝ) ^ (n - t)) * gaussianFactor T *
      Real.exp (δ + c) by positivity)
  apply h.trans
  calc
    _ = S * (((n - t).factorial : ℝ) / (2 : ℝ) ^ (n - t)) *
        ((n - 1 : ℝ) / (((n - t : ℕ) : ℝ) * η)) ^ (n - t) *
          gaussianFactor T * Real.exp (δ + c) := by
      calc
        _ = S * (((n - 1 : ℝ) / (2 * η)) ^ (n - t) *
            (((n - t).factorial : ℝ) / ((n - t : ℕ) : ℝ) ^ (n - t))) *
              gaussianFactor T * Real.exp (δ + c) := by ring
        _ = _ := by rw [hpow]; ring
    _ ≤ S * (((n - t).factorial : ℝ) / (2 : ℝ) ^ (n - t)) * gaussianFactor T *
        Real.exp (δ + c) * Real.exp
          (-1 + (t : ℝ) / n + |matrixEntryMass (preconditionedTournamentDensity T) - n| +
            |matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) -
              ((n - t : ℕ) : ℝ)|) := by
      convert hmul using 1
      ring
    _ = _ := by
      simp only [mul_assoc, ← Real.exp_add]
      have hexp : δ + c + (-1 + (t : ℝ) / n +
          |matrixEntryMass (preconditionedTournamentDensity T) - n| +
          |matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) -
            ((n - t : ℕ) : ℝ)|) =
          -1 + (t : ℝ) / n + |matrixEntryMass (preconditionedTournamentDensity T) - n| +
          |matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) -
            (n - t : ℝ)| + δ + uniformPermanentActivityConstant (2 * K + 1) ((1 + q) / 2) / (n - t) := by
        dsimp [c]
        rw [Nat.cast_sub ht.le]
        ring
      rw [hexp]
      dsimp [S, e, c]
      ring

end TournamentHamiltonian
