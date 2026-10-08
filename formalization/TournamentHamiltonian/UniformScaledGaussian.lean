import TournamentHamiltonian.UniformScalingDisplacement

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

theorem exists_preconditioned_scaling_gaussian_uniform_log {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), ∀ hI : I.card = t, ∀ hJ : J.card = t,
          ∃ x : (Iᶜ : Finset (Fin n)) → ℝ, ∃ y : (Jᶜ : Finset (Fin n)) → ℝ,
            let X := normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J
            let BX := rectangularExpScaling X x y
            RectangularScalingWitness X (deletedComplementEquiv I J (hI.trans hJ.symm))
              (preconditioningScalingDensity a0) (preconditioningScalingCenteredDensity a0)
              (9 / 10) (preconditioningScalingEpsilon a0) x y ∧
            |Real.log (gramGaussian (BX - rectangularAverageMatrix _ _)) - Real.log (gaussianFactor T)| ≤
              (1400 / 39) * realFrobeniusNorm (BX - X) +
                (250 / 19) * preconditioningCenteredDisplacementBudget (t := t) T a0 I J +
                  (24 * (t : ℝ) + 18 * scoreVariance T + 11) / n := by
  obtain ⟨Nw, hNw, hw⟩ := exists_preconditioned_nonprincipal_scaling_uniform_log hA hB h0 h1
  obtain ⟨Ng, hNg, hg⟩ := normalizedDeletedPreconditioned_centered_gap_uniform_log hA hB h0 h1
  obtain ⟨Np, hNp, hp⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  obtain ⟨Nd, hNd, hd⟩ := preconditioningCenteredDisplacementBudget_uniform_eventually_small
    hA hB h0 h1 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Nb, hNb, hb⟩ := preconditioned_scaling_displacement_uniform_eventually_small
    hA hB h0 h1 (by norm_num : (0 : ℝ) < 1)
  refine ⟨max Nw (max Ng (max Np (max Nd Nb))), hNw.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNw : Nw ≤ n := by omega
  have hnNg : Ng ≤ n := by omega
  have hnNp : Np ≤ n := by omega
  have hnNd : Nd ≤ n := by omega
  have hnNb : Nb ≤ n := by omega
  have hn20 : 20 ≤ n := hNw.trans hnNw
  obtain ⟨x, y, hxy⟩ := hw n t hnNw T ha hvar hlog I J hI hJ
  obtain ⟨h2t, htn, hM, hX, _⟩ := hp n t hnNp T ha hvar hlog I J hI hJ
  have hgap := hg n t hnNg T ha hvar hlog I J hI hJ
  have hD := hd n t hnNd T ha hvar hlog I J hI hJ
  have hBdisp := hb n t hnNb T ha hvar hlog I J hI hJ x y hxy
  let X := normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J
  let BX := rectangularExpScaling X x y
  let W := centeringProjection (Iᶜ : Finset (Fin n)) * X * centeringProjection (Jᶜ : Finset (Fin n))
  let Z := centeredDeletedSkewKernel T I J
  have hcardpos : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  have hWf : realFrobeniusNorm W ≤ 3 := by
    have hdisp := normalizedDeletedPreconditioned_centered_frobenius_displacement T (by omega)
      I J hI hJ htn a0 h0 h1 ha hM.ne' hX.ne'
    have hZf := centeredDeletedSkewKernel_frobenius_le_two T (by omega) I J hI hJ htn
    change realFrobeniusNorm (W - Z) ≤ _ at hdisp
    change realFrobeniusNorm Z ≤ 2 at hZf
    have heq : W = (W - Z) + Z := by abel
    have h := realFrobeniusNorm_add_le (W - Z) Z
    rw [← heq] at h
    linarith
  have hscaled := rectangularScaling_gaussian_finite_comparison X
    (deletedComplementEquiv I J (hI.trans hJ.symm)) hcardpos
      (preconditioningScalingDensity a0) (preconditioningScalingCenteredDensity a0)
      (preconditioningScalingEpsilon a0) x y hxy hgap hWf hBdisp
  have hpre := normalizedDeletedPreconditioned_gaussian_finite_comparison T hn20 I J hI hJ h2t
    a0 h0 h1 ha hM.ne' hX.ne' hgap hD
  refine ⟨x, y, hxy, ?_⟩
  have htriangle := abs_sub_le (Real.log (gramGaussian (BX - rectangularAverageMatrix _ _)))
    (Real.log (gramGaussian W)) (Real.log (gaussianFactor T))
  have h := htriangle.trans (add_le_add hscaled hpre)
  exact h.trans_eq (by ring)

end TournamentHamiltonian
