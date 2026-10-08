import TournamentHamiltonian.UniformPreconditioningGap

namespace TournamentHamiltonian

theorem retained_matrix_row_error {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (i : (Iᶜ : Finset (Fin n))) :
    matrixRowError (X.submatrix
      (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n)
      (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) i =
        matrixRowError X i - ∑ j ∈ J, X i j := by
  simp only [matrixRowError, Matrix.submatrix_apply]
  rw [Finset.sum_coe_sort (Jᶜ) (fun j => X i j)]
  have h := Finset.sum_add_sum_compl J (fun j => X i j)
  linarith

theorem scaled_retained_row_error_abs_le {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (hJ : J.card = t) (K c : ℝ)
    (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n) (i : (Iᶜ : Finset (Fin n))) :
    |matrixRowError (c • X.submatrix
      (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n)
      (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) i| ≤
        |c| * (|matrixRowError X i| + K * (t : ℝ) / n) + |c - 1| := by
  rw [matrixRowError_smul, retained_matrix_row_error]
  have hs := deleted_row_entry_mass_bounds X J hJ K hX i
  have h := abs_add_le (matrixRowError X i) (-(∑ j ∈ J, X i j))
  simp only [← sub_eq_add_neg, abs_neg, abs_of_nonneg hs.1] at h
  have h1 : |matrixRowError X i - ∑ j ∈ J, X i j| ≤
      |matrixRowError X i| + K * (t : ℝ) / n := by linarith
  calc
    _ ≤ |c * (matrixRowError X i - ∑ j ∈ J, X i j)| + |c - 1| := abs_add_le _ _
    _ = |c| * |matrixRowError X i - ∑ j ∈ J, X i j| + |c - 1| := by rw [abs_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg c)) le_rfl

theorem scaled_retained_column_error_abs_le {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (hI : I.card = t) (K c : ℝ)
    (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n) (j : (Jᶜ : Finset (Fin n))) :
    |matrixColumnError (c • X.submatrix
      (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n)
      (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) j| ≤
        |c| * (|matrixColumnError X j| + K * (t : ℝ) / n) + |c - 1| := by
  have h := scaled_retained_row_error_abs_le X.transpose J I hI K c
    (fun i j => hX j i) j
  simpa only [matrixRowError, matrixColumnError, Matrix.transpose_apply,
    Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul] using h

theorem normalizedDeletedPreconditioned_marginal_error_uniform_log {A B a0 eps : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) (heps : 0 < eps) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), I.card = t → J.card = t →
          (∀ i, |matrixRowError (normalizedDeletedMatrix (t := t)
            (normalizedPreconditionedDensity T) I J) i| ≤ eps) ∧
          (∀ j, |matrixColumnError (normalizedDeletedMatrix (t := t)
            (normalizedPreconditionedDensity T) I J) j| ≤ eps) := by
  let K : ℝ := 4 / (1 - a0) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨Np, hNp, hp⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  obtain ⟨Ne, hNe, he⟩ := preconditioningDeletionEta_uniform_eventually_small hA hB h0 h1
    (show 0 < min 1 (eps / 4) by positivity)
  obtain ⟨Nm, hNm, hm⟩ := preconditioned_marginal_error_uniform_log hA h1
    (show 0 < eps / 8 by positivity)
  obtain ⟨Nt, hNt, ht⟩ := logarithmic_nat_budget_uniform_eventually_small B K (eps / 8)
    hB hK (by positivity)
  refine ⟨max Np (max Ne (max Nm Nt)), hNp.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNp : Np ≤ n := by omega
  have hnNe : Ne ≤ n := by omega
  have hnNm : Nm ≤ n := by omega
  have hnNt : Nt ≤ n := by omega
  have hn4 : 4 ≤ n := hNp.trans hnNp
  obtain ⟨_h2t, htn, hM, hX, _⟩ := hp n t hnNp T ha hvar hlog I J hI hJ
  have heta := he n t hnNe T ha hvar hlog I J hI hJ
  have heta1 := heta.trans (min_le_left _ _)
  have hetaE := heta.trans (min_le_right _ _)
  have heabs : |preconditioningDeletionEta (t := t) T I J| ≤ 2 := by
    have h := abs_add_le (preconditioningDeletionEta (t := t) T I J - 1) 1
    simp only [sub_add_cancel, abs_one] at h
    linarith
  obtain ⟨hr, hc⟩ := hm n hnNm T ha hvar
  have htd := ht n t hnNt hlog
  have hentry : ∀ i j, 0 ≤ preconditionedTournamentDensity T i j ∧
      preconditionedTournamentDensity T i j ≤ K / n := by
    intro i j
    simpa only [K, div_div] using preconditionedTournamentDensity_entry_bounds T
      (by omega) a0 h0 h1 ha i j
  rw [normalizedDeletedPreconditioned_eq T I J hI htn hM.ne' hX.ne']
  constructor
  · intro i
    have h := scaled_retained_row_error_abs_le (preconditionedTournamentDensity T) I J hJ K
      (preconditioningDeletionEta (t := t) T I J) hentry i
    have hsum : |matrixRowError (preconditionedTournamentDensity T) i| + K * (t : ℝ) / n ≤ eps / 4 := by
      linarith [hr i]
    have hsum0 : 0 ≤ |matrixRowError (preconditionedTournamentDensity T) i| + K * (t : ℝ) / n := by positivity
    have hprod := mul_le_mul heabs hsum hsum0 (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  · intro j
    have h := scaled_retained_column_error_abs_le (preconditionedTournamentDensity T) I J hI K
      (preconditioningDeletionEta (t := t) T I J) hentry j
    have hsum : |matrixColumnError (preconditionedTournamentDensity T) j| + K * (t : ℝ) / n ≤ eps / 4 := by
      linarith [hc j]
    have hsum0 : 0 ≤ |matrixColumnError (preconditionedTournamentDensity T) j| + K * (t : ℝ) / n := by positivity
    have hprod := mul_le_mul heabs hsum hsum0 (by norm_num : (0 : ℝ) ≤ 2)
    linarith

theorem normalizedDeletedPreconditioned_density_uniform_log {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), I.card = t → J.card = t →
          matrixEntryMass (normalizedDeletedMatrix (t := t)
            (normalizedPreconditionedDensity T) I J) = (n - t : ℝ) ∧
          ∀ i j, 0 ≤ normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J i j ∧
            normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J i j ≤
              (8 / (1 - a0) ^ 2) / (n - t : ℝ) := by
  obtain ⟨Np, hNp, hp⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  obtain ⟨Ne, hNe, he⟩ := preconditioningDeletionEta_uniform_eventually_small hA hB h0 h1
    (by norm_num : (0 : ℝ) < 1)
  refine ⟨max Np Ne, hNp.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNp : Np ≤ n := by omega
  have hnNe : Ne ≤ n := by omega
  have hn4 : 4 ≤ n := hNp.trans hnNp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨_h2t, htn, hM, hX, _⟩ := hp n t hnNp T ha hvar hlog I J hI hJ
  have htnR : (t : ℝ) < n := by exact_mod_cast htn
  have heta := he n t hnNe T ha hvar hlog I J hI hJ
  have heabs : |preconditioningDeletionEta (t := t) T I J| ≤ 2 := by
    have h := abs_add_le (preconditioningDeletionEta (t := t) T I J - 1) 1
    simp only [sub_add_cancel, abs_one] at h
    linarith
  have heta0 : 0 ≤ preconditioningDeletionEta (t := t) T I J := by
    unfold preconditioningDeletionEta
    positivity
  have heta2 : preconditioningDeletionEta (t := t) T I J ≤ 2 :=
    (le_abs_self _).trans heabs
  constructor
  · change matrixEntryMass (massNormalizedMatrix _) = _
    rw [massNormalizedMatrix_mass _ hX.ne', Fintype.card_coe, Finset.card_compl,
      Fintype.card_fin, hI, Nat.cast_sub htn.le]
  · intro i j
    rw [normalizedDeletedPreconditioned_eq T I J hI htn hM.ne' hX.ne']
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply]
    have hentry := preconditionedTournamentDensity_entry_bounds T (by omega) a0 h0 h1 ha i j
    refine ⟨mul_nonneg heta0 hentry.1, ?_⟩
    calc
      _ ≤ 2 * preconditionedTournamentDensity T i j := mul_le_mul_of_nonneg_right heta2 hentry.1
      _ ≤ 2 * (4 / ((1 - a0) ^ 2 * n)) := mul_le_mul_of_nonneg_left hentry.2 (by norm_num)
      _ = (8 / (1 - a0) ^ 2) / n := by rw [← div_div]; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by linarith)
        (by have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t; linarith)

end TournamentHamiltonian
