import TournamentHamiltonian.FrobeniusGeometry

namespace TournamentHamiltonian

private theorem abs_five_terms_le (a b c d e : ℝ) :
    |a - b - c - d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le a (-b)
  have h2 := abs_add_le (a - b) (-c)
  have h3 := abs_add_le (a - b - c) (-d)
  have h4 := abs_add_le (a - b - c - d) e
  simp only [← sub_eq_add_neg, abs_neg] at h1 h2 h3
  linarith

theorem retained_mass_error_bound {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t)
    (K eps : ℝ) (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / n)
    (hr : ∀ i, |matrixRowError X i| ≤ eps) (hc : ∀ j, |matrixColumnError X j| ≤ eps) :
    |matrixEntryMass (X.submatrix
      (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) - (n - t : ℝ)| ≤
      |matrixEntryMass X - n| + t + 2 * (t : ℝ) * eps + K * (t : ℝ) ^ 2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrow := subset_abs_sum_le I (matrixRowError X) eps hr
  have hcol := subset_abs_sum_le J (matrixColumnError X) eps hc
  rw [hI] at hrow
  rw [hJ] at hcol
  have hover := deleted_overlap_bounds X I J hI hJ K hX
  have he : matrixEntryMass (X.submatrix
      (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) - (n - t : ℝ) =
      (matrixEntryMass X - n) - t - (∑ i ∈ I, matrixRowError X i) -
        (∑ j ∈ J, matrixColumnError X j) + (∑ i ∈ I, ∑ j ∈ J, X i j) := by
    rw [matrixEntryMass_deleted_errors, hI, hJ]
    ring
  rw [he]
  have h := abs_five_terms_le (matrixEntryMass X - n) t
    (∑ i ∈ I, matrixRowError X i) (∑ j ∈ J, matrixColumnError X j) (∑ i ∈ I, ∑ j ∈ J, X i j)
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (t : ℝ) from Nat.cast_nonneg t), abs_of_nonneg hover.1] at h
  linarith

theorem finite_eta_error_bound (N t r B : ℝ) (hN : 0 < N) (ht : t ≤ N / 2)
    (hr : (N - t) / 2 ≤ r) (hB : |r - (N - t)| ≤ B) :
    |(N - t) / r - 1| ≤ 4 * B / N := by
  have hm : 0 < N - t := by linarith
  have hrp : 0 < r := by linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have he : (N - t) / r - 1 = -(r - (N - t)) / r := by field_simp; ring
  rw [he, abs_div, abs_neg, abs_of_pos hrp]
  calc
    _ ≤ B / r := div_le_div_of_nonneg_right hB hrp.le
    _ ≤ 4 * B / N := by
      apply (div_le_div_iff₀ hrp hN).mpr
      have h := mul_le_mul_of_nonneg_left hr hB0
      have h' := mul_le_mul_of_nonneg_left ht hB0
      nlinarith

theorem preconditioningDeletionEta_error_bound {n t : ℕ} (T : Tournament n)
    (hn : 1 < n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t) (ht : 2 * t ≤ n)
    (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hM : matrixEntryMass (preconditionedTournamentDensity T) ≠ 0)
    (hX : matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) ≠ 0)
    (hret : (n - t : ℝ) / 2 ≤ matrixEntryMass ((preconditionedTournamentDensity T).submatrix
      (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n))) :
    |preconditioningDeletionEta (t := t) T I J - 1| ≤
      4 * (|matrixEntryMass (preconditionedTournamentDensity T) - n| + t +
        8 * (t : ℝ) / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) +
          4 * (t : ℝ) ^ 2 / ((1 - a0) ^ 2 * n)) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htR : (t : ℝ) ≤ n / 2 := by
    have h : 2 * (t : ℝ) ≤ n := by exact_mod_cast ht
    linarith
  rw [preconditioningDeletionEta_eq_retained_mass T I J (by omega) hM hX]
  apply finite_eta_error_bound n t _ _ hn0 htR hret
  have hentry : ∀ i j, 0 ≤ preconditionedTournamentDensity T i j ∧
      preconditionedTournamentDensity T i j ≤ (4 / (1 - a0) ^ 2) / n := by
    intro i j
    simpa only [div_div] using preconditionedTournamentDensity_entry_bounds T hn a0 h0 h1 ha i j
  have h := retained_mass_error_bound (preconditionedTournamentDensity T) (by omega)
    I J hI hJ (4 / (1 - a0) ^ 2) (4 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n)) hentry
    (preconditioned_row_error_abs_bound T hn a0 h1 ha) (preconditioned_column_error_abs_bound T hn a0 h1 ha)
  have he : |matrixEntryMass (preconditionedTournamentDensity T) - n| + t +
      2 * (t : ℝ) * (4 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n)) +
        (4 / (1 - a0) ^ 2) * (t : ℝ) ^ 2 / n =
      |matrixEntryMass (preconditionedTournamentDensity T) - n| + t +
        8 * (t : ℝ) / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) +
          4 * (t : ℝ) ^ 2 / ((1 - a0) ^ 2 * n) := by
    rw [← div_div]
    ring
  exact h.trans_eq he

end TournamentHamiltonian
