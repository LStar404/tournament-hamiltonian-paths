import TournamentHamiltonian.UniformDeletionBudgets

namespace TournamentHamiltonian

theorem normalization_mass_half_of_eta (N m M Q : ℝ) (hN : 0 < N) (hm : m ≤ N)
    (hM : 0 < M) (hQ : 0 < Q) (hMupper : M ≤ 5 * N / 4)
    (heta : N ^ 2 / (M * Q) ≤ 5 / 4) : m / 2 ≤ Q := by
  have hprod := (div_le_iff₀ (mul_pos hM hQ)).mp heta
  by_contra h
  have hQn : Q < N / 2 := (lt_of_not_ge h).trans_le (by linarith)
  have h1 := mul_le_mul_of_nonneg_right hMupper (show 0 ≤ (5 / 4 : ℝ) * Q by positivity)
  have h2 := mul_lt_mul_of_pos_left hQn (show 0 < (25 / 16 : ℝ) * N by positivity)
  nlinarith [sq_pos_of_pos hN]

/-- A common uniform threshold gives both actual normalization masses at
least half their dimensions, also for different deleted row and column sets. -/
theorem preconditioned_normalization_masses_uniform_half_log {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), I.card = t → J.card = t →
          2 * t ≤ n ∧ t < n ∧
          (n : ℝ) / 2 ≤ matrixEntryMass (preconditionedTournamentDensity T) ∧
          ((n - t : ℕ) : ℝ) / 2 ≤
            matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) := by
  obtain ⟨Nm, _hNm, hm⟩ := preconditioned_mass_error_uniform_log hA h0 h1 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Ne, _hNe, he⟩ := preconditioningDeletionEta_uniform_eventually_small hA hB h0 h1
    (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨Np, hNp, hp⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  refine ⟨max Np (max Nm Ne), hNp.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNp : Np ≤ n := by omega
  have hnNm : Nm ≤ n := by omega
  have hnNe : Ne ≤ n := by omega
  have hn4 : 4 ≤ n := hNp.trans hnNp
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  obtain ⟨ht2, ht, hM, hQ, _hη⟩ := hp n t hnNp T ha hvar hlog I J hI hJ
  have herr := abs_le.mp (hm n hnNm T ha hvar)
  have hMhalf : (n : ℝ) / 2 ≤ matrixEntryMass (preconditionedTournamentDensity T) := by linarith
  have hMupper : matrixEntryMass (preconditionedTournamentDensity T) ≤ 5 * (n : ℝ) / 4 := by linarith
  have heta := (abs_le.mp (he n t hnNe T ha hvar hlog I J hI hJ)).2
  have heta' : preconditioningDeletionEta (t := t) T I J ≤ 5 / 4 := by linarith
  refine ⟨ht2, ht, hMhalf, ?_⟩
  exact normalization_mass_half_of_eta n (n - t : ℕ) _ _ (by linarith)
    (by exact_mod_cast Nat.sub_le n t) hM hQ hMupper heta'

end TournamentHamiltonian
