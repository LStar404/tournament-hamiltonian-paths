import TournamentHamiltonian.UniformDeletedMarginals
import TournamentHamiltonian.GramLipschitz

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

theorem preconditioningCenteredDisplacementBudget_uniform_eventually_small {A B a0 eps : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) (heps : 0 < eps) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), I.card = t → J.card = t →
          preconditioningCenteredDisplacementBudget (t := t) T a0 I J ≤ eps := by
  obtain ⟨Ne, hNe, he⟩ := preconditioningDeletionEta_uniform_eventually_small hA hB h0 h1
    (show 0 < min 1 (eps / 8) by positivity)
  obtain ⟨Ns, hNs, hs⟩ := score_sqrt_budget_uniform_eventually_small A
    (16 / (1 - a0) ^ 2) (eps / 4) hA (by positivity) (by positivity)
  refine ⟨max Ne Ns, hNe.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNe : Ne ≤ n := by omega
  have hnNs : Ns ≤ n := by omega
  have heta := he n t hnNe T ha hvar hlog I J hI hJ
  have heta1 := heta.trans (min_le_left _ _)
  have hetaE := heta.trans (min_le_right _ _)
  have heabs : |preconditioningDeletionEta (t := t) T I J| ≤ 2 := by
    have h := abs_add_le (preconditioningDeletionEta (t := t) T I J - 1) 1
    simp only [sub_add_cancel, abs_one] at h
    linarith
  have hf := hs n hnNs (scoreVariance T) (scoreVariance_nonneg T) hvar
  have hf0 : 0 ≤ 16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) := by positivity
  have hprod := mul_le_mul heabs hf hf0 (show (0 : ℝ) ≤ 2 by norm_num)
  have heq : preconditioningCenteredDisplacementBudget (t := t) T a0 I J =
      2 * |preconditioningDeletionEta (t := t) T I J - 1| +
        |preconditioningDeletionEta (t := t) T I J| *
          (16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n)) := by
    unfold preconditioningCenteredDisplacementBudget
    ring
  rw [heq]
  linarith

theorem centeredDeletedSkewKernel_frobenius_le_two {n t : ℕ} (T : Tournament n)
    (hn : 1 < n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t) (ht : t < n) :
    realFrobeniusNorm (centeredDeletedSkewKernel T I J) ≤ 2 := by
  have hp : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  have hq : 0 < Fintype.card (Jᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hJ]
    omega
  exact (centeredMatrix_frobenius_le (deletedShiftedSkewKernel T I J) hp hq).trans
    ((realFrobeniusNorm_submatrix_le (shiftedSkewKernel T) Iᶜ Jᶜ).trans
      (shiftedSkewKernel_frobenius_le_two T hn))

theorem normalizedDeletedPreconditioned_gaussian_finite_comparison {n t : ℕ}
    (T : Tournament n) (hn : 20 ≤ n) (I J : Finset (Fin n))
    (hI : I.card = t) (hJ : J.card = t) (ht : 2 * t ≤ n)
    (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hM : matrixEntryMass (preconditionedTournamentDensity T) ≠ 0)
    (hX : matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) ≠ 0)
    (hW : ‖centeringProjection (Iᶜ : Finset (Fin n)) *
      normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J *
        centeringProjection (Jᶜ : Finset (Fin n))‖ ≤ 9 / 10)
    (hD : preconditioningCenteredDisplacementBudget (t := t) T a0 I J ≤ 1) :
    |Real.log (gramGaussian (centeringProjection (Iᶜ : Finset (Fin n)) *
      normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J *
        centeringProjection (Jᶜ : Finset (Fin n)))) - Real.log (gaussianFactor T)| ≤
          (250 / 19) * preconditioningCenteredDisplacementBudget (t := t) T a0 I J +
            (24 * (t : ℝ) + 18 * scoreVariance T + 11) / n := by
  have htn : t < n := by omega
  have hp : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  have hq : 0 < Fintype.card (Jᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hJ]
    omega
  let W := centeringProjection (Iᶜ : Finset (Fin n)) *
    normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J *
      centeringProjection (Jᶜ : Finset (Fin n))
  let Z := centeredDeletedSkewKernel T I J
  let D := preconditioningCenteredDisplacementBudget (t := t) T a0 I J
  have hdisp : realFrobeniusNorm (W - Z) ≤ D :=
    normalizedDeletedPreconditioned_centered_frobenius_displacement T (by omega)
      I J hI hJ htn a0 h0 h1 ha hM hX
  have hZf : realFrobeniusNorm Z ≤ 2 := centeredDeletedSkewKernel_frobenius_le_two T
    (by omega) I J hI hJ htn
  have hWf : realFrobeniusNorm W ≤ 3 := by
    have heq : W = (W - Z) + Z := by abel
    have h := realFrobeniusNorm_add_le (W - Z) Z
    rw [← heq] at h
    dsimp [D] at hdisp
    linarith
  have hZq : ‖Z‖ ≤ (9 / 10 : ℝ) := by
    have h := (centeredMatrix_opNorm_le (deletedShiftedSkewKernel T I J) hp hq).trans
      ((submatrix_opNorm_le (shiftedSkewKernel T) Iᶜ Jᶜ).trans
        (shiftedSkewKernel_opNorm_le T (by omega)))
    exact h.trans ((shiftedSkewNormBudget_sqrt_le_three_quarters n hn).trans (by norm_num))
  have hLip := gramGaussian_log_lipschitz W Z (9 / 10) (by norm_num) (by norm_num) hW hZq
  have hprod := mul_le_mul (show realFrobeniusNorm W + realFrobeniusNorm Z ≤ 5 by linarith)
    hdisp (realFrobeniusNorm_nonneg _) (by norm_num : (0 : ℝ) ≤ 5)
  have hcompare : |Real.log (gramGaussian W) - Real.log (gramGaussian Z)| ≤ (250 / 19) * D := by
    have h := div_le_div_of_nonneg_right hprod
      (by norm_num : (0 : ℝ) ≤ 2 * (1 - (9 / 10 : ℝ) ^ 2))
    exact hLip.trans (h.trans_eq (by ring))
  have hdel := tournament_gaussian_deletion_loss T (by omega) I J hI hJ ht
  have htriangle := abs_sub_le (Real.log (gramGaussian W)) (Real.log (gramGaussian Z))
    (Real.log (gaussianFactor T))
  exact htriangle.trans (add_le_add hcompare hdel)

theorem normalizedDeletedPreconditioned_gaussian_comparison_uniform_log {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), I.card = t → J.card = t →
          |Real.log (gramGaussian (centeringProjection (Iᶜ : Finset (Fin n)) *
            normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J *
              centeringProjection (Jᶜ : Finset (Fin n)))) - Real.log (gaussianFactor T)| ≤
                (250 / 19) * preconditioningCenteredDisplacementBudget (t := t) T a0 I J +
                  (24 * (t : ℝ) + 18 * scoreVariance T + 11) / n := by
  obtain ⟨Np, hNp, hp⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  obtain ⟨Ng, hNg, hg⟩ := normalizedDeletedPreconditioned_centered_gap_uniform_log hA hB h0 h1
  obtain ⟨Nd, hNd, hd⟩ := preconditioningCenteredDisplacementBudget_uniform_eventually_small
    hA hB h0 h1 (by norm_num : (0 : ℝ) < 1)
  refine ⟨max Ng (max Np Nd), hNg.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNp : Np ≤ n := by omega
  have hnNg : Ng ≤ n := by omega
  have hnNd : Nd ≤ n := by omega
  have hn20 : 20 ≤ n := hNg.trans hnNg
  obtain ⟨h2t, _htn, hM, hX, _⟩ := hp n t hnNp T ha hvar hlog I J hI hJ
  exact normalizedDeletedPreconditioned_gaussian_finite_comparison T hn20 I J hI hJ h2t
    a0 h0 h1 ha hM.ne' hX.ne' (hg n t hnNg T ha hvar hlog I J hI hJ)
      (hd n t hnNd T ha hvar hlog I J hI hJ)

end TournamentHamiltonian
