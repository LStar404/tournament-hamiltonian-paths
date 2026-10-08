import TournamentHamiltonian.DeletionBounds

namespace TournamentHamiltonian

noncomputable def normalizedPreconditionedDensity {n : ℕ} (T : Tournament n) :
    Matrix (Fin n) (Fin n) ℝ := massNormalizedMatrix (preconditionedTournamentDensity T)

theorem preconditioned_mass_lower_of_budget {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hbudget : (4 / (1 - a0 ^ 2) ^ 2) *
      ((scoreVariance T + scoreVariance T ^ 2) / n + scoreVariance T * Real.sqrt (scoreVariance T / n)) ≤ n / 2) :
    (n : ℝ) / 2 ≤ matrixEntryMass (preconditionedTournamentDensity T) := by
  have h := preconditioned_mass_error_bound T hn a0 h0 h1 ha
  have h' := (abs_le.mp (h.trans hbudget)).1
  linarith

theorem normalizedPreconditionedDensity_mass {n : ℕ} (T : Tournament n)
    (hn : 0 < n) (hM : (n : ℝ) / 2 ≤ matrixEntryMass (preconditionedTournamentDensity T)) :
    matrixEntryMass (normalizedPreconditionedDensity T) = n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < matrixEntryMass (preconditionedTournamentDensity T) := by linarith
  simpa only [normalizedPreconditionedDensity, Fintype.card_fin] using
    massNormalizedMatrix_mass (preconditionedTournamentDensity T) hp.ne'

theorem normalizedPreconditionedDensity_entry_bounds {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hM : (n : ℝ) / 2 ≤ matrixEntryMass (preconditionedTournamentDensity T)) (i j : Fin n) :
    0 ≤ normalizedPreconditionedDensity T i j ∧
      normalizedPreconditionedDensity T i j ≤ 8 / ((1 - a0) ^ 2 * n) := by
  have hp : 0 < Fintype.card (Fin n) := by simp; omega
  have h := normalized_entry_bounds (preconditionedTournamentDensity T) (4 / (1 - a0) ^ 2)
    hp (by simpa only [Fintype.card_fin] using hM) (by
      intro i j
      simp only [Fintype.card_fin]
      simpa only [div_div] using preconditionedTournamentDensity_entry_bounds T hn a0 h0 h1 ha i j) i j
  simpa only [normalizedPreconditionedDensity, Fintype.card_fin, ← mul_div_assoc, div_div,
    show (2 : ℝ) * 4 = 8 by norm_num] using h

theorem normalizedPreconditionedDensity_row_error_abs_le {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (a0 : ℝ) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hM : (n : ℝ) / 2 ≤ matrixEntryMass (preconditionedTournamentDensity T)) (i : Fin n) :
    |matrixRowError (normalizedPreconditionedDensity T) i| ≤
      8 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) +
        2 * |matrixEntryMass (preconditionedTournamentDensity T) - n| / n := by
  have hp : 0 < Fintype.card (Fin n) := by simp; omega
  have h := normalized_row_error_abs_le (preconditionedTournamentDensity T) hp
    (by simpa only [Fintype.card_fin] using hM) i
  simp only [Fintype.card_fin] at h
  calc
    _ ≤ _ := h
    _ ≤ 2 * (4 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n)) +
        2 * |matrixEntryMass (preconditionedTournamentDensity T) - n| / n :=
      add_le_add (mul_le_mul_of_nonneg_left (preconditioned_row_error_abs_bound T hn a0 h1 ha i)
        (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ = _ := by ring

theorem normalizedPreconditionedDensity_column_error_abs_le {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (a0 : ℝ) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hM : (n : ℝ) / 2 ≤ matrixEntryMass (preconditionedTournamentDensity T)) (j : Fin n) :
    |matrixColumnError (normalizedPreconditionedDensity T) j| ≤
      8 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) +
        2 * |matrixEntryMass (preconditionedTournamentDensity T) - n| / n := by
  have hp : 0 < Fintype.card (Fin n) := by simp; omega
  have h := normalized_column_error_abs_le (preconditionedTournamentDensity T) hp
    (by simpa only [Fintype.card_fin] using hM) j
  simp only [Fintype.card_fin] at h
  calc
    _ ≤ _ := h
    _ ≤ 2 * (4 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n)) +
        2 * |matrixEntryMass (preconditionedTournamentDensity T) - n| / n :=
      add_le_add (mul_le_mul_of_nonneg_left (preconditioned_column_error_abs_bound T hn a0 h1 ha j)
        (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ = _ := by ring

theorem normalizedPreconditionedDensity_row_error_sum_sq_le {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (a0 : ℝ) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hM : (n : ℝ) / 2 ≤ matrixEntryMass (preconditionedTournamentDensity T)) :
    (∑ i, matrixRowError (normalizedPreconditionedDensity T) i ^ 2) ≤
      64 * scoreVariance T / (1 - a0) ^ 4 := by
  have hp : 0 < Fintype.card (Fin n) := by simp; omega
  have h := normalized_row_error_sum_sq_le (preconditionedTournamentDensity T) hp
    (by simpa only [Fintype.card_fin] using hM)
  have h' := mul_le_mul_of_nonneg_left (preconditioned_row_error_sum_sq_bound T hn a0 h1 ha)
    (by norm_num : (0 : ℝ) ≤ 4)
  exact h.trans (h'.trans_eq (by ring))

theorem normalizedPreconditionedDensity_column_error_sum_sq_le {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (a0 : ℝ) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hM : (n : ℝ) / 2 ≤ matrixEntryMass (preconditionedTournamentDensity T)) :
    (∑ j, matrixColumnError (normalizedPreconditionedDensity T) j ^ 2) ≤
      64 * scoreVariance T / (1 - a0) ^ 4 := by
  have hp : 0 < Fintype.card (Fin n) := by simp; omega
  have h := normalized_column_error_sum_sq_le (preconditionedTournamentDensity T) hp
    (by simpa only [Fintype.card_fin] using hM)
  have h' := mul_le_mul_of_nonneg_left (preconditioned_column_error_sum_sq_bound T hn a0 h1 ha)
    (by norm_num : (0 : ℝ) ≤ 4)
  exact h.trans (h'.trans_eq (by ring))

end TournamentHamiltonian
