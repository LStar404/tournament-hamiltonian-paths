import TournamentHamiltonian.PreconditioningNormalization

namespace TournamentHamiltonian

/-- The deleted and full normalization masses are controlled together by
the true score variance and the actual number of deleted rows and columns. -/
theorem preconditioned_retained_mass_error_budget {n t : ℕ} (T : Tournament n)
    (hn : 1 < n) (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hM : (n : ℝ) / 2 ≤ matrixEntryMass (preconditionedTournamentDensity T))
    (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t) (ht : 2 * t ≤ n) :
    |matrixEntryMass (preconditionedTournamentDensity T) - n| +
      |matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) -
        (n - t : ℝ)| ≤
      5 * (4 / (1 - a0 ^ 2) ^ 2) *
        ((scoreVariance T + scoreVariance T ^ 2) / n +
          scoreVariance T * Real.sqrt (scoreVariance T / n)) +
      (32 / (1 - a0) ^ 2) * (t : ℝ) * Real.sqrt (scoreVariance T / n) +
      2 * (8 / (1 - a0) ^ 2 + 1) * (t : ℝ) ^ 2 / n := by
  let ν := |matrixEntryMass (preconditionedTournamentDensity T) - n|
  let s := Real.sqrt (scoreVariance T / n)
  let K := 8 / (1 - a0) ^ 2
  let eps := K * s + 2 * ν / n
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have htR : 2 * (t : ℝ) ≤ n := by exact_mod_cast ht
  have hν : 0 ≤ ν := abs_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have heps : 0 ≤ eps := by dsimp [eps, s]; positivity
  have hentry (i j : Fin n) : 0 ≤ normalizedPreconditionedDensity T i j ∧
      normalizedPreconditionedDensity T i j ≤ K / n := by
    simpa only [K, div_div] using
      normalizedPreconditionedDensity_entry_bounds T hn a0 h0 h1 ha hM i j
  have hr (i : Fin n) : |matrixRowError (normalizedPreconditionedDensity T) i| ≤ eps :=
    normalizedPreconditionedDensity_row_error_abs_le T hn a0 h1 ha hM i
  have hc (j : Fin n) : |matrixColumnError (normalizedPreconditionedDensity T) j| ≤ eps :=
    normalizedPreconditionedDensity_column_error_abs_le T hn a0 h1 ha hM j
  have hQ := scaled_deleted_mass_error_bound (normalizedPreconditionedDensity T) hn0
    I J hI hJ ht (normalizedPreconditionedDensity_mass T hn0 hM) K eps hK heps
    hentry hr hc
  have htfrac : 8 * (t : ℝ) / n ≤ 4 := (div_le_iff₀ hnR).mpr (by linarith)
  have hνfrac := mul_le_mul_of_nonneg_right htfrac hν
  have hQB : |matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) -
      (n - t : ℝ)| ≤ 4 * K * (t : ℝ) * s + 4 * ν + 2 * (K + 1) * (t : ℝ) ^ 2 / n := by
    apply hQ.trans
    change 4 * (t : ℝ) * (K * s + 2 * ν / n) + _ ≤ _
    calc
      _ = 4 * K * (t : ℝ) * s + (8 * (t : ℝ) / n) * ν +
          2 * (K + 1) * (t : ℝ) ^ 2 / n := by ring
      _ ≤ _ := add_le_add (add_le_add le_rfl hνfrac) le_rfl
  have hfull := mul_le_mul_of_nonneg_left (preconditioned_mass_error_bound T hn a0 h0 h1 ha)
    (by norm_num : (0 : ℝ) ≤ 5)
  calc
    _ ≤ 5 * ν + 4 * K * (t : ℝ) * s + 2 * (K + 1) * (t : ℝ) ^ 2 / n := by
      change ν + _ ≤ _
      linarith [hQB]
    _ ≤ _ := by
      dsimp only [ν, K, s]
      convert add_le_add (add_le_add hfull le_rfl) le_rfl using 1
      ring

end TournamentHamiltonian
