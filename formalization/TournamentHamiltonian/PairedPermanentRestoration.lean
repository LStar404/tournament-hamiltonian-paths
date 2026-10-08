import TournamentHamiltonian.UniformGaussianCost
import TournamentHamiltonian.ScalingIdentities

namespace TournamentHamiltonian

set_option backward.isDefEq.respectTransparency false

theorem rectangularPermanent_row_column_scaling {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι κ ℝ) (e : ι ≃ κ) (r : ι → ℝ) (c : κ → ℝ) :
    rectangularPermanent (fun i j => r i * X i j * c j) e =
      (∏ i, r i) * (∏ j, c j) * rectangularPermanent X e := by
  have h := permanent_row_column_scaling (X.submatrix id e) r (c ∘ e)
  have hp : (∏ i, (c ∘ e) i) = ∏ j, c j := e.prod_comp c
  rw [hp] at h
  exact h

theorem rectangularPermanent_scalar {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι κ ℝ) (e : ι ≃ κ) (d : ℝ) :
    rectangularPermanent (d • X) e = d ^ Fintype.card ι * rectangularPermanent X e := by
  change rectangularPermanent (fun i j => d * X i j) e = _
  simpa only [Finset.prod_const, Finset.card_univ, one_pow, mul_one] using
    rectangularPermanent_row_column_scaling X e (fun _ => d) (fun _ => 1)

noncomputable def pairedScoreProduct {n : ℕ} (T : Tournament n) : ℝ :=
  ∏ i, (1 - tournamentScorePotential T i ^ 2)

theorem pairedScoreProduct_le_exp {n : ℕ} (T : Tournament n)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ 1) :
    pairedScoreProduct T ≤ Real.exp (-scoreVariance T) := by
  apply score_product_le_exp
  intro i
  simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (ha i)

theorem adjacency_nonprincipal_paired_restoration {n : ℕ} (T : Tournament n)
    (hn : 2 ≤ n) (I J : Finset (Fin n)) (e : (Iᶜ : Finset (Fin n)) ≃ (Jᶜ : Finset (Fin n)))
    (ha : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1) :
    rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J) e =
      pairedScoreProduct T * (∏ i ∈ I, pairedLeft (tournamentScorePotential T i)) *
        (∏ j ∈ J, pairedRight (tournamentScorePotential T j)) *
          ((n - 1 : ℝ) / 2) ^ Fintype.card (Iᶜ : Finset (Fin n)) *
            rectangularPermanent (nonprincipalSubmatrix (preconditionedTournamentDensity T) I J) e := by
  have hnR : (n - 1 : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmat : nonprincipalSubmatrix (adjacency T) I J =
      ((n - 1 : ℝ) / 2) •
        ((fun (i : (Iᶜ : Finset (Fin n))) (j : (Jᶜ : Finset (Fin n))) =>
          (1 + tournamentScorePotential T i) * preconditionedTournamentDensity T i j *
            (1 - tournamentScorePotential T j)) : Matrix (Iᶜ : Finset (Fin n)) (Jᶜ : Finset (Fin n)) ℝ) := by
    ext i j
    have hp : 1 + tournamentScorePotential T i ≠ 0 := by linarith [(ha i).1]
    have hm : 1 - tournamentScorePotential T j ≠ 0 := by linarith [(ha j).2]
    change adjacency T i j = ((n - 1 : ℝ) / 2) *
      ((1 + tournamentScorePotential T i) *
        ((1 + tournamentScorePotential T i)⁻¹ *
          ((2 / (n - 1 : ℝ)) * adjacency T i j) *
            (1 - tournamentScorePotential T j)⁻¹) * (1 - tournamentScorePotential T j))
    field_simp [hp, hm, hnR]
  rw [hmat, rectangularPermanent_scalar, rectangularPermanent_row_column_scaling]
  have hp : (∏ i : (Iᶜ : Finset (Fin n)), (1 + tournamentScorePotential T i)) =
      ∏ i ∈ Iᶜ, (1 + tournamentScorePotential T i) :=
    Finset.prod_coe_sort Iᶜ (fun i => 1 + tournamentScorePotential T i)
  have hm : (∏ j : (Jᶜ : Finset (Fin n)), (1 - tournamentScorePotential T j)) =
      ∏ j ∈ Jᶜ, (1 - tournamentScorePotential T j) :=
    Finset.prod_coe_sort Jᶜ (fun j => 1 - tournamentScorePotential T j)
  rw [hp, hm]
  have hpair := paired_deleted_product (tournamentScorePotential T) I J ha
  change _ = pairedScoreProduct T * (∏ i ∈ I, pairedLeft (tournamentScorePotential T i)) *
    (∏ j ∈ J, pairedRight (tournamentScorePotential T j)) at hpair
  rw [← mul_assoc, hpair]
  have heq : (fun (i : (Iᶜ : Finset (Fin n))) (j : (Jᶜ : Finset (Fin n))) =>
      preconditionedTournamentDensity T i j) =
      nonprincipalSubmatrix (preconditionedTournamentDensity T) I J := rfl
  rw [heq]
  ring

theorem adjacency_nonprincipal_true_scaling_restoration {n t : ℕ} (T : Tournament n)
    (hn : 2 ≤ n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t) (ht : t < n)
    (ha : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1)
    (hM : matrixEntryMass (preconditionedTournamentDensity T) ≠ 0)
    (hX : matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) ≠ 0)
    (x : (Iᶜ : Finset (Fin n)) → ℝ) (y : (Jᶜ : Finset (Fin n)) → ℝ) :
    let e := deletedComplementEquiv I J (hI.trans hJ.symm)
    let X := normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J
    rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J) e =
      pairedScoreProduct T * (∏ i ∈ I, pairedLeft (tournamentScorePotential T i)) *
        (∏ j ∈ J, pairedRight (tournamentScorePotential T j)) *
          ((n - 1 : ℝ) / (2 * preconditioningDeletionEta (t := t) T I J)) ^ (n - t) *
            Real.exp (-((∑ i, x i) + ∑ j, y j)) *
              rectangularPermanent (rectangularExpScaling X x y) e := by
  let e := deletedComplementEquiv I J (hI.trans hJ.symm)
  let eta := preconditioningDeletionEta (t := t) T I J
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have heta : eta ≠ 0 := by
    dsimp [eta, preconditioningDeletionEta]
    exact div_ne_zero (pow_ne_zero _ hnR) (mul_ne_zero hM hX)
  have hnorm := normalizedDeletedPreconditioned_eq T I J hI ht hM hX
  have hrestore : nonprincipalSubmatrix (preconditionedTournamentDensity T) I J =
      eta⁻¹ • normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J := by
    rw [hnorm, smul_smul, inv_mul_cancel₀ heta, one_smul]
    rfl
  have hc : Fintype.card (Iᶜ : Finset (Fin n)) = n - t := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
  dsimp only
  rw [adjacency_nonprincipal_paired_restoration T hn I J e ha, hrestore,
    rectangularPermanent_scalar, rectangularPermanent_exp_restoration _ e x y, hc]
  have hbase : ((n - 1 : ℝ) / (2 * preconditioningDeletionEta (t := t) T I J)) =
      ((n - 1 : ℝ) / 2) * eta⁻¹ := by dsimp [eta]; field_simp [heta]
  rw [hbase]
  simp only [mul_pow]
  ring

theorem adjacency_nonprincipal_true_scaling_upper {n t : ℕ} (T : Tournament n)
    (hn : 2 ≤ n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t) (ht : t < n)
    (ha : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1)
    (hM : 0 < matrixEntryMass (preconditionedTournamentDensity T))
    (hX : 0 < matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J))
    (K C q eps : ℝ) (x : (Iᶜ : Finset (Fin n)) → ℝ) (y : (Jᶜ : Finset (Fin n)) → ℝ)
    (hxy : RectangularScalingWitness
      (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J)
      (deletedComplementEquiv I J (hI.trans hJ.symm)) K C q eps x y) :
    let e := deletedComplementEquiv I J (hI.trans hJ.symm)
    let X := normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J
    rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J) e ≤
      pairedScoreProduct T * (∏ i ∈ I, pairedLeft (tournamentScorePotential T i)) *
        (∏ j ∈ J, pairedRight (tournamentScorePotential T j)) *
          ((n - 1 : ℝ) / (2 * preconditioningDeletionEta (t := t) T I J)) ^ (n - t) *
            rectangularPermanent (rectangularExpScaling X x y) e := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have heta : 0 < preconditioningDeletionEta (t := t) T I J := by
    unfold preconditioningDeletionEta
    positivity
  have hG : 0 ≤ pairedScoreProduct T := by
    unfold pairedScoreProduct
    apply Finset.prod_nonneg
    intro i _
    have hp : 0 < 1 + tournamentScorePotential T i := by linarith [(ha i).1]
    have hm : 0 < 1 - tournamentScorePotential T i := by linarith [(ha i).2]
    nlinarith [mul_pos hp hm]
  have hl : 0 ≤ ∏ i ∈ I, pairedLeft (tournamentScorePotential T i) := by
    apply Finset.prod_nonneg
    intro i _
    unfold pairedLeft
    exact inv_nonneg.mpr (by linarith [(ha i).1])
  have hr : 0 ≤ ∏ j ∈ J, pairedRight (tournamentScorePotential T j) := by
    apply Finset.prod_nonneg
    intro j _
    unfold pairedRight
    exact inv_nonneg.mpr (by linarith [(ha j).2])
  have hbase : 0 ≤ (n - 1 : ℝ) / (2 * preconditioningDeletionEta (t := t) T I J) := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (by linarith) (by positivity)
  have hfactor : 0 ≤ pairedScoreProduct T * (∏ i ∈ I, pairedLeft (tournamentScorePotential T i)) *
      (∏ j ∈ J, pairedRight (tournamentScorePotential T j)) *
        ((n - 1 : ℝ) / (2 * preconditioningDeletionEta (t := t) T I J)) ^ (n - t) := by positivity
  have he : Real.exp (-((∑ i, x i) + ∑ j, y j)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [hxy.capacity_nonneg])
  have hper := rectangularPermanent_nonneg _ hxy.nonnegative
    (deletedComplementEquiv I J (hI.trans hJ.symm))
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he hper) hfactor
  dsimp only
  rw [adjacency_nonprincipal_true_scaling_restoration T hn I J hI hJ ht ha hM.ne' hX.ne' x y]
  convert hm using 1 <;> ring

theorem exists_paired_nonprincipal_restoration_uniform_log {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), ∀ hI : I.card = t, ∀ hJ : J.card = t,
          ∃ x : (Iᶜ : Finset (Fin n)) → ℝ, ∃ y : (Jᶜ : Finset (Fin n)) → ℝ,
            let e := deletedComplementEquiv I J (hI.trans hJ.symm)
            let X := normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J
            let BX := rectangularExpScaling X x y
            RectangularScalingWitness X e (preconditioningScalingDensity a0)
              (preconditioningScalingCenteredDensity a0) (9 / 10) (preconditioningScalingEpsilon a0) x y ∧
            |Real.log (gramGaussian (BX - rectangularAverageMatrix _ _)) - Real.log (gaussianFactor T)| ≤
              preconditioningGaussianCostConstant a0 *
                (Real.sqrt (scoreVariance T / n) + ((t : ℝ) + 1) / n) ∧
            rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J) e ≤
              pairedScoreProduct T * (∏ i ∈ I, pairedLeft (tournamentScorePotential T i)) *
                (∏ j ∈ J, pairedRight (tournamentScorePotential T j)) *
                  ((n - 1 : ℝ) / (2 * preconditioningDeletionEta (t := t) T I J)) ^ (n - t) *
                    rectangularPermanent BX e := by
  obtain ⟨Ng, hNg, hg⟩ := exists_preconditioned_scaling_gaussian_cost_uniform_log hA hB h0 h1
  obtain ⟨Np, _hNp, hp⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  refine ⟨max Ng Np, hNg.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNg : Ng ≤ n := by omega
  have hnNp : Np ≤ n := by omega
  have hn20 : 20 ≤ n := hNg.trans hnNg
  obtain ⟨x, y, hxy, hcost⟩ := hg n t hnNg T ha hvar hlog I J hI hJ
  obtain ⟨_h2t, htn, hM, hX, _he⟩ := hp n t hnNp T ha hvar hlog I J hI hJ
  have harange : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1 := by
    intro i
    obtain ⟨hl, hr⟩ := abs_le.mp (ha i)
    constructor <;> linarith
  exact ⟨x, y, hxy, hcost, adjacency_nonprincipal_true_scaling_upper T (by omega)
    I J hI hJ htn harange hM hX _ _ _ _ x y hxy⟩

end TournamentHamiltonian
