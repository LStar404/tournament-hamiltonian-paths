import TournamentHamiltonian.NormalizationBounds

namespace TournamentHamiltonian

theorem subset_abs_sum_le {ι : Type*} [Fintype ι] (s : Finset ι)
    (f : ι → ℝ) (eps : ℝ) (h : ∀ i, |f i| ≤ eps) :
    |∑ i ∈ s, f i| ≤ (s.card : ℝ) * eps := by
  calc
    _ ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, eps := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

noncomputable def scaledDeletedMatrix {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) : Matrix (Iᶜ : Finset (Fin n)) (Jᶜ : Finset (Fin n)) ℝ :=
  ((n : ℝ) / (n - t : ℝ)) • X.submatrix Subtype.val Subtype.val

theorem deletion_scale_bounds {n t : ℕ} (hn : 0 < n) (ht : 2 * t ≤ n) :
    0 ≤ (n : ℝ) / (n - t : ℝ) ∧ (n : ℝ) / (n - t : ℝ) ≤ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htR : 2 * (t : ℝ) ≤ n := by exact_mod_cast ht
  have hm : (0 : ℝ) < n - t := by linarith
  refine ⟨div_nonneg hnR.le hm.le, (div_le_iff₀ hm).mpr ?_⟩
  linarith

theorem deleted_overlap_bounds {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t) (K : ℝ)
    (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n) :
    0 ≤ (∑ i ∈ I, ∑ j ∈ J, X i j) ∧
      (∑ i ∈ I, ∑ j ∈ J, X i j) ≤ K * (t : ℝ) ^ 2 / n := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hX i j).1))
  · calc
      _ ≤ ∑ _i ∈ I, ∑ _j ∈ J, K / n :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => (hX i j).2))
      _ = _ := by simp only [Finset.sum_const, hI, hJ, nsmul_eq_mul]; ring

theorem scaled_deleted_mass_error_bound {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t)
    (ht : 2 * t ≤ n) (hmass : matrixEntryMass X = n) (K eps : ℝ)
    (_hK : 0 ≤ K) (_heps : 0 ≤ eps)
    (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n)
    (hr : ∀ i, |matrixRowError X i| ≤ eps) (hc : ∀ j, |matrixColumnError X j| ≤ eps) :
    |matrixEntryMass (scaledDeletedMatrix (t := t) X I J) - (n - t : ℝ)| ≤
      4 * (t : ℝ) * eps + 2 * (K + 1) * (t : ℝ) ^ 2 / n := by
  have ht' : t < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd := deletion_scale_bounds hn ht
  have hrow := subset_abs_sum_le I (matrixRowError X) eps hr
  have hcol := subset_abs_sum_le J (matrixColumnError X) eps hc
  rw [hI] at hrow
  rw [hJ] at hcol
  have hover := deleted_overlap_bounds X I J hI hJ K hX
  have hnum : |-(∑ i ∈ I, matrixRowError X i) - (∑ j ∈ J, matrixColumnError X j) +
      (∑ i ∈ I, ∑ j ∈ J, X i j) - (t : ℝ) ^ 2 / n| ≤
      2 * (t : ℝ) * eps + (K + 1) * (t : ℝ) ^ 2 / n := by
    have h1 := abs_add_le (-(∑ i ∈ I, matrixRowError X i)) (-(∑ j ∈ J, matrixColumnError X j))
    simp only [← sub_eq_add_neg, abs_neg] at h1
    have h2 := abs_add_le (-(∑ i ∈ I, matrixRowError X i) - ∑ j ∈ J, matrixColumnError X j)
      (∑ i ∈ I, ∑ j ∈ J, X i j)
    have h3 := abs_add_le (-(∑ i ∈ I, matrixRowError X i) - (∑ j ∈ J, matrixColumnError X j) +
      (∑ i ∈ I, ∑ j ∈ J, X i j)) (-((t : ℝ) ^ 2 / n))
    simp only [← sub_eq_add_neg, abs_neg] at h3
    rw [abs_of_nonneg hover.1] at h2
    rw [abs_of_nonneg (by positivity : 0 ≤ (t : ℝ) ^ 2 / n)] at h3
    have he : K * (t : ℝ) ^ 2 / n + (t : ℝ) ^ 2 / n = (K + 1) * (t : ℝ) ^ 2 / n := by ring
    linarith
  change |matrixEntryMass (((n : ℝ) / (n - t : ℝ)) • X.submatrix
    (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) - _| ≤ _
  rw [normalized_deleted_mass X I J hI hJ ht' hmass, abs_mul, abs_of_nonneg hd.1]
  calc
    _ ≤ 2 * (2 * (t : ℝ) * eps + (K + 1) * (t : ℝ) ^ 2 / n) :=
      mul_le_mul hd.2 hnum (abs_nonneg _) (by norm_num)
    _ = _ := by ring

theorem deleted_row_entry_mass_bounds {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (J : Finset (Fin n)) (hJ : J.card = t) (K : ℝ)
    (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n) (i : Fin n) :
    0 ≤ (∑ j ∈ J, X i j) ∧ (∑ j ∈ J, X i j) ≤ K * t / n := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => (hX i j).1)
  · calc
      _ ≤ ∑ _j ∈ J, K / n := Finset.sum_le_sum (fun j _ => (hX i j).2)
      _ = _ := by simp only [Finset.sum_const, hJ, nsmul_eq_mul]; ring

theorem scaled_deleted_row_error_abs_le {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (I J : Finset (Fin n)) (hJ : J.card = t) (ht : 2 * t ≤ n)
    (K : ℝ) (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n) (i : (Iᶜ : Finset (Fin n))) :
    |matrixRowError (scaledDeletedMatrix (t := t) X I J) i| ≤
      2 * (|matrixRowError X i| + (K + 1) * (t : ℝ) / n) := by
  have ht' : t < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd := deletion_scale_bounds hn ht
  have hs := deleted_row_entry_mass_bounds X J hJ K hX i
  have hnum : |matrixRowError X i + (t : ℝ) / n - ∑ j ∈ J, X i j| ≤
      |matrixRowError X i| + (K + 1) * (t : ℝ) / n := by
    have h1 := abs_add_le (matrixRowError X i) ((t : ℝ) / n)
    have h2 := abs_add_le (matrixRowError X i + (t : ℝ) / n) (-(∑ j ∈ J, X i j))
    simp only [← sub_eq_add_neg, abs_neg] at h2
    rw [abs_of_nonneg (by positivity : 0 ≤ (t : ℝ) / n)] at h1
    rw [abs_of_nonneg hs.1] at h2
    have he : (t : ℝ) / n + K * (t : ℝ) / n = (K + 1) * (t : ℝ) / n := by ring
    linarith
  rw [scaledDeletedMatrix, normalized_deleted_row_error X I J ht' i, abs_mul, abs_of_nonneg hd.1]
  exact mul_le_mul hd.2 hnum (abs_nonneg _) (by norm_num)

theorem scaled_deleted_column_error_abs_le {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (I J : Finset (Fin n)) (hI : I.card = t) (ht : 2 * t ≤ n)
    (K : ℝ) (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n) (j : (Jᶜ : Finset (Fin n))) :
    |matrixColumnError (scaledDeletedMatrix (t := t) X I J) j| ≤
      2 * (|matrixColumnError X j| + (K + 1) * (t : ℝ) / n) := by
  simpa only [matrixRowError, matrixColumnError, scaledDeletedMatrix,
    Matrix.smul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, smul_eq_mul] using
    scaled_deleted_row_error_abs_le X.transpose hn J I hI ht K (fun i j => hX j i) j

theorem scaled_deleted_row_error_sq_le {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (I J : Finset (Fin n)) (hJ : J.card = t) (ht : 2 * t ≤ n)
    (K : ℝ) (hK : 0 ≤ K) (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n)
    (i : (Iᶜ : Finset (Fin n))) :
    matrixRowError (scaledDeletedMatrix (t := t) X I J) i ^ 2 ≤
      8 * matrixRowError X i ^ 2 + 8 * ((K + 1) * (t : ℝ) / n) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 ≤ (K + 1) * (t : ℝ) / n := by positivity
  have h := scaled_deleted_row_error_abs_le X hn I J hJ ht K hX i
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity :
    0 ≤ 2 * (|matrixRowError X i| + (K + 1) * (t : ℝ) / n))).mpr h
  rw [sq_abs] at hs
  nlinarith [sq_abs (matrixRowError X i), sq_nonneg (|matrixRowError X i| - (K + 1) * (t : ℝ) / n)]

theorem scaled_deleted_row_error_sum_sq_le {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (I J : Finset (Fin n)) (hJ : J.card = t) (ht : 2 * t ≤ n)
    (K : ℝ) (hK : 0 ≤ K) (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n) :
    (∑ i, matrixRowError (scaledDeletedMatrix (t := t) X I J) i ^ 2) ≤
      8 * (∑ i, matrixRowError X i ^ 2) + 8 * (K + 1) ^ 2 * (t : ℝ) ^ 2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : (∑ i ∈ Iᶜ, matrixRowError X i ^ 2) ≤ (∑ i, matrixRowError X i ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hcard : ((Iᶜ : Finset (Fin n)).card : ℝ) ≤ n := by
    exact_mod_cast ((Finset.card_le_card (Finset.subset_univ Iᶜ)).trans_eq (by simp))
  calc
    _ ≤ ∑ i : (Iᶜ : Finset (Fin n)),
        (8 * matrixRowError X i ^ 2 + 8 * ((K + 1) * (t : ℝ) / n) ^ 2) :=
      Finset.sum_le_sum (fun i _ => scaled_deleted_row_error_sq_le X hn I J hJ ht K hK hX i)
    _ = 8 * (∑ i ∈ Iᶜ, matrixRowError X i ^ 2) +
        8 * ((Iᶜ : Finset (Fin n)).card : ℝ) * ((K + 1) * (t : ℝ) / n) ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      rw [Finset.sum_coe_sort (Iᶜ) (fun i => matrixRowError X i ^ 2)]
      ring
    _ ≤ 8 * (∑ i, matrixRowError X i ^ 2) +
        8 * (n : ℝ) * ((K + 1) * (t : ℝ) / n) ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hsub (by norm_num))
        (by nlinarith [mul_le_mul_of_nonneg_right hcard (sq_nonneg ((K + 1) * (t : ℝ) / n))])
    _ = _ := by field_simp

theorem scaled_deleted_column_error_sum_sq_le {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (I J : Finset (Fin n)) (hI : I.card = t) (ht : 2 * t ≤ n)
    (K : ℝ) (hK : 0 ≤ K) (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n) :
    (∑ j, matrixColumnError (scaledDeletedMatrix (t := t) X I J) j ^ 2) ≤
      8 * (∑ j, matrixColumnError X j ^ 2) + 8 * (K + 1) ^ 2 * (t : ℝ) ^ 2 / n := by
  simpa only [matrixRowError, matrixColumnError, scaledDeletedMatrix,
    Matrix.smul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, smul_eq_mul] using
    scaled_deleted_row_error_sum_sq_le X.transpose hn J I hI ht K hK (fun i j => hX j i)

theorem scaled_deleted_entry_bounds {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (I J : Finset (Fin n)) (ht : 2 * t ≤ n)
    (K : ℝ) (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n)
    (i : (Iᶜ : Finset (Fin n))) (j : (Jᶜ : Finset (Fin n))) :
    0 ≤ scaledDeletedMatrix (t := t) X I J i j ∧
      scaledDeletedMatrix (t := t) X I J i j ≤ K / (n - t : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd := deletion_scale_bounds hn ht
  change 0 ≤ ((n : ℝ) / (n - t : ℝ)) * X i j ∧ _
  refine ⟨mul_nonneg hd.1 (hX i j).1, ?_⟩
  change ((n : ℝ) / (n - t : ℝ)) * X i j ≤ _
  calc
    _ ≤ ((n : ℝ) / (n - t : ℝ)) * (K / n) := mul_le_mul_of_nonneg_left (hX i j).2 hd.1
    _ = _ := by field_simp

noncomputable def normalizedDeletedMatrix {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) : Matrix (Iᶜ : Finset (Fin n)) (Jᶜ : Finset (Fin n)) ℝ :=
  massNormalizedMatrix (scaledDeletedMatrix (t := t) X I J)

theorem normalized_deleted_entry_bounds {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (I J : Finset (Fin n)) (hI : I.card = t) (ht : 2 * t ≤ n)
    (K : ℝ) (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n)
    (hM : (n - t : ℝ) / 2 ≤ matrixEntryMass (scaledDeletedMatrix (t := t) X I J))
    (i : (Iᶜ : Finset (Fin n))) (j : (Jᶜ : Finset (Fin n))) :
    0 ≤ normalizedDeletedMatrix (t := t) X I J i j ∧
      normalizedDeletedMatrix (t := t) X I J i j ≤ 2 * K / (n - t : ℝ) := by
  have ht' : t < n := by omega
  have hcard : (Fintype.card (Iᶜ : Finset (Fin n)) : ℝ) = (n - t : ℝ) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI, Nat.cast_sub ht'.le]
  have hp : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  have h := normalized_entry_bounds (scaledDeletedMatrix (t := t) X I J) K hp
    (by rw [hcard]; exact hM) (by
      intro i j
      rw [hcard]
      exact scaled_deleted_entry_bounds X hn I J ht K hX i j) i j
  simpa only [hcard, normalizedDeletedMatrix] using h

theorem normalized_deleted_row_error_sum_sq_le {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t)
    (ht : 2 * t ≤ n) (K : ℝ) (hK : 0 ≤ K)
    (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n)
    (hM : (n - t : ℝ) / 2 ≤ matrixEntryMass (scaledDeletedMatrix (t := t) X I J)) :
    (∑ i, matrixRowError (normalizedDeletedMatrix (t := t) X I J) i ^ 2) ≤
      32 * (∑ i, matrixRowError X i ^ 2) + 32 * (K + 1) ^ 2 * (t : ℝ) ^ 2 / n := by
  have ht' : t < n := by omega
  have hcard : (Fintype.card (Iᶜ : Finset (Fin n)) : ℝ) = (n - t : ℝ) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI, Nat.cast_sub ht'.le]
  have hp : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  have h1 := normalized_row_error_sum_sq_le (scaledDeletedMatrix (t := t) X I J)
    hp (by rw [hcard]; exact hM)
  have h2 := mul_le_mul_of_nonneg_left (scaled_deleted_row_error_sum_sq_le X hn I J hJ ht K hK hX)
    (by norm_num : (0 : ℝ) ≤ 4)
  change (∑ i, matrixRowError (normalizedDeletedMatrix (t := t) X I J) i ^ 2) ≤ _ at h1
  exact h1.trans (h2.trans_eq (by ring))

theorem normalized_deleted_column_error_sum_sq_le {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t)
    (ht : 2 * t ≤ n) (K : ℝ) (hK : 0 ≤ K)
    (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n)
    (hM : (n - t : ℝ) / 2 ≤ matrixEntryMass (scaledDeletedMatrix (t := t) X I J)) :
    (∑ j, matrixColumnError (normalizedDeletedMatrix (t := t) X I J) j ^ 2) ≤
      32 * (∑ j, matrixColumnError X j ^ 2) + 32 * (K + 1) ^ 2 * (t : ℝ) ^ 2 / n := by
  have ht' : t < n := by omega
  have hcard : (Fintype.card (Iᶜ : Finset (Fin n)) : ℝ) = (n - t : ℝ) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI, Nat.cast_sub ht'.le]
  have hsame : Fintype.card (Jᶜ : Finset (Fin n)) = Fintype.card (Iᶜ : Finset (Fin n)) := by
    simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI, hJ]
  have hp : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  have h1 := normalized_rect_column_error_sum_sq_le (scaledDeletedMatrix (t := t) X I J)
    hsame hp (by rw [hcard]; exact hM)
  have h2 := mul_le_mul_of_nonneg_left (scaled_deleted_column_error_sum_sq_le X hn I J hI ht K hK hX)
    (by norm_num : (0 : ℝ) ≤ 4)
  change (∑ j, matrixColumnError (normalizedDeletedMatrix (t := t) X I J) j ^ 2) ≤ _ at h1
  exact h1.trans (h2.trans_eq (by ring))

end TournamentHamiltonian
