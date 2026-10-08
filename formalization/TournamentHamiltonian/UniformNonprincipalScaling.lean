import TournamentHamiltonian.UniformDeletedMarginals
import TournamentHamiltonian.NonprincipalScaling
import TournamentHamiltonian.RectangularKernelBridge

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

noncomputable def preconditioningScalingDensity (a0 : ℝ) : ℝ := 8 / (1 - a0) ^ 2

noncomputable def preconditioningScalingCenteredDensity (a0 : ℝ) : ℝ :=
  preconditioningScalingDensity a0 + 3

noncomputable def preconditioningScalingEpsilon (a0 : ℝ) : ℝ :=
  let L := localScalingInverseBudget (preconditioningScalingCenteredDensity a0) (9 / 10)
  min 1 (min (1 / (256 * L ^ 2)) ((1 - 9 / 10) / (2 * (32 * L + 2))))

theorem preconditioningScalingEpsilon_pos (a0 : ℝ) : 0 < preconditioningScalingEpsilon a0 := by
  have hK : 0 ≤ preconditioningScalingDensity a0 := by unfold preconditioningScalingDensity; positivity
  have hC : 0 ≤ preconditioningScalingCenteredDensity a0 := by unfold preconditioningScalingCenteredDensity; linarith
  have hL : 0 < localScalingInverseBudget (preconditioningScalingCenteredDensity a0) (9 / 10) := by
    have hterm : 0 ≤ preconditioningScalingCenteredDensity a0 ^ 2 / (1 - 9 / 10) := by positivity
    unfold localScalingInverseBudget
    linarith
  unfold preconditioningScalingEpsilon
  positivity

theorem exists_preconditioned_nonprincipal_scaling_uniform_log {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), ∀ hI : I.card = t, ∀ hJ : J.card = t,
          ∃ x : (Iᶜ : Finset (Fin n)) → ℝ, ∃ y : (Jᶜ : Finset (Fin n)) → ℝ,
            RectangularScalingWitness
              (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J)
              (deletedComplementEquiv I J (hI.trans hJ.symm))
              (preconditioningScalingDensity a0) (preconditioningScalingCenteredDensity a0)
              (9 / 10) (preconditioningScalingEpsilon a0) x y := by
  let K := preconditioningScalingDensity a0
  let C := preconditioningScalingCenteredDensity a0
  let eps := preconditioningScalingEpsilon a0
  have hK : 0 ≤ K := by dsimp [K, preconditioningScalingDensity]; positivity
  have hC : 0 ≤ C := by dsimp [C, preconditioningScalingCenteredDensity]; linarith
  have heps : 0 < eps := preconditioningScalingEpsilon_pos a0
  have heps1 : eps ≤ 1 := min_le_left _ _
  have hepssmall : eps ≤ 1 / (256 * localScalingInverseBudget C (9 / 10) ^ 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hepsgap : eps ≤ (1 - 9 / 10) / (2 * (32 * localScalingInverseBudget C (9 / 10) + 2)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Np, hNp, hp⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  obtain ⟨Nd, hNd, hd⟩ := normalizedDeletedPreconditioned_density_uniform_log hA hB h0 h1
  obtain ⟨Nm, hNm, hm⟩ := normalizedDeletedPreconditioned_marginal_error_uniform_log hA hB h0 h1 heps
  obtain ⟨Ng, hNg, hg⟩ := normalizedDeletedPreconditioned_centered_gap_uniform_log hA hB h0 h1
  refine ⟨max Ng (max Np (max Nd Nm)), hNg.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNg : Ng ≤ n := by omega
  have hnNp : Np ≤ n := by omega
  have hnNd : Nd ≤ n := by omega
  have hnNm : Nm ≤ n := by omega
  obtain ⟨_h2t, htn, _hM, _hX, _⟩ := hp n t hnNp T ha hvar hlog I J hI hJ
  obtain ⟨hmass, hentry⟩ := hd n t hnNd T ha hvar hlog I J hI hJ
  obtain ⟨hr, hc⟩ := hm n t hnNm T ha hvar hlog I J hI hJ
  have hnorm := hg n t hnNg T ha hvar hlog I J hI hJ
  let X := normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J
  let e := deletedComplementEquiv I J (hI.trans hJ.symm)
  have hcard : (Fintype.card (Iᶜ : Finset (Fin n)) : ℝ) = (n - t : ℝ) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI, Nat.cast_sub htn.le]
  have hcardpos : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  have hmass' : matrixEntryMass X = Fintype.card (Iᶜ : Finset (Fin n)) := by rw [hcard]; exact hmass
  have hnonneg : ∀ i j, 0 ≤ X i j := fun i j => (hentry i j).1
  have habs : ∀ i j, |X i j| ≤ K / Fintype.card (Iᶜ : Finset (Fin n)) := by
    intro i j
    rw [abs_of_nonneg (hnonneg i j), hcard]
    exact (hentry i j).2
  have hcenter : ∀ i j, |rectangularCenteredKernel X i j| ≤ C / Fintype.card (Iᶜ : Finset (Fin n)) := by
    intro i j
    have h := rectangularCenteredKernel_density_bound X e hcardpos K eps habs hr hc i j
    apply h.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    dsimp [C, preconditioningScalingCenteredDensity, K] at *
    linarith
  have hEq : ‖rectangularCenteredKernel X‖ ≤ (9 / 10 : ℝ) := by
    rw [rectangularCenteredKernel_eq_centering X e hcardpos hmass']
    exact hnorm
  have hrow : ∀ i, ∑ j, |X i j| ≤ 2 := by
    intro i
    have habsi : ∀ j, |X i j| = X i j := fun j => abs_of_nonneg (hnonneg i j)
    simp_rw [habsi]
    have h := (abs_le.mp (hr i)).2
    change (∑ j, X i j) - 1 ≤ eps at h
    linarith
  have hcol : ∀ j, ∑ i, |X i j| ≤ 2 := by
    intro j
    have habsj : ∀ i, |X i j| = X i j := fun i => abs_of_nonneg (hnonneg i j)
    simp_rw [habsj]
    have h := (abs_le.mp (hc j)).2
    change (∑ i, X i j) - 1 ≤ eps at h
    linarith
  exact exists_rectangular_scaling_witness X e hcardpos hnonneg hmass' K C (9 / 10) eps
    hK hC (by norm_num) (by norm_num) heps.le habs hcenter hEq hr hc hrow hcol hepssmall hepsgap

end TournamentHamiltonian
