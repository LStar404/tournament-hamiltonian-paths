import TournamentHamiltonian.UniformScaledGaussian

namespace TournamentHamiltonian

noncomputable def preconditionedDeletedMarginalBudget (n t : ℕ) (tau a0 : ℝ) : ℝ :=
  let c : ℝ := 4 / (1 - a0) ^ 2
  2 * c * Real.sqrt (tau / n) + 2 * c * (t : ℝ) / n + 4 * (1 + 4 * t) / n

theorem preconditioned_deleted_marginal_budget_uniform_log {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), I.card = t → J.card = t →
          (∀ i, |matrixRowError (normalizedDeletedMatrix (t := t)
            (normalizedPreconditionedDensity T) I J) i| ≤
              preconditionedDeletedMarginalBudget n t (scoreVariance T) a0) ∧
          (∀ j, |matrixColumnError (normalizedDeletedMatrix (t := t)
            (normalizedPreconditionedDensity T) I J) j| ≤
              preconditionedDeletedMarginalBudget n t (scoreVariance T) a0) ∧
          preconditioningCenteredDisplacementBudget (t := t) T a0 I J ≤
            8 * (1 + 4 * (t : ℝ)) / n +
              (32 / (1 - a0) ^ 2) * Real.sqrt (scoreVariance T / n) := by
  let c : ℝ := 4 / (1 - a0) ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨Np, hNp, hp⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  obtain ⟨Ne, hNe, he⟩ := preconditioningDeletionEta_uniform_eventually_small hA hB h0 h1
    (by norm_num : (0 : ℝ) < 1)
  refine ⟨max Np Ne, hNp.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNp : Np ≤ n := by omega
  have hnNe : Ne ≤ n := by omega
  have hn4 : 4 ≤ n := hNp.trans hnNp
  obtain ⟨_h2t, htn, hM, hX, heta⟩ := hp n t hnNp T ha hvar hlog I J hI hJ
  have heta1 := he n t hnNe T ha hvar hlog I J hI hJ
  have heabs : |preconditioningDeletionEta (t := t) T I J| ≤ 2 := by
    have h := abs_add_le (preconditioningDeletionEta (t := t) T I J - 1) 1
    simp only [sub_add_cancel, abs_one] at h
    linarith
  have hentry : ∀ i j, 0 ≤ preconditionedTournamentDensity T i j ∧
      preconditionedTournamentDensity T i j ≤ c / n := by
    intro i j
    simpa only [c, div_div] using preconditionedTournamentDensity_entry_bounds T
      (by omega) a0 h0 h1 ha i j
  have hrow (i : (Iᶜ : Finset (Fin n))) :=
    preconditioned_row_error_abs_bound T (by omega) a0 h1 ha i
  have hcol (j : (Jᶜ : Finset (Fin n))) :=
    preconditioned_column_error_abs_bound T (by omega) a0 h1 ha j
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [normalizedDeletedPreconditioned_eq T I J hI htn hM.ne' hX.ne']
    have h := scaled_retained_row_error_abs_le (preconditionedTournamentDensity T) I J hJ c
      (preconditioningDeletionEta (t := t) T I J) hentry i
    have hprod := mul_le_mul heabs (add_le_add (hrow i) (le_refl (c * (t : ℝ) / n)))
      (show 0 ≤ |matrixRowError (preconditionedTournamentDensity T) i| + c * (t : ℝ) / n by positivity)
      (by norm_num : (0 : ℝ) ≤ 2)
    have hsum := h.trans (add_le_add hprod heta)
    exact hsum.trans_eq (by unfold preconditionedDeletedMarginalBudget; dsimp [c]; ring)
  · intro j
    rw [normalizedDeletedPreconditioned_eq T I J hI htn hM.ne' hX.ne']
    have h := scaled_retained_column_error_abs_le (preconditionedTournamentDensity T) I J hI c
      (preconditioningDeletionEta (t := t) T I J) hentry j
    have hprod := mul_le_mul heabs (add_le_add (hcol j) (le_refl (c * (t : ℝ) / n)))
      (show 0 ≤ |matrixColumnError (preconditionedTournamentDensity T) j| + c * (t : ℝ) / n by positivity)
      (by norm_num : (0 : ℝ) ≤ 2)
    have hsum := h.trans (add_le_add hprod heta)
    exact hsum.trans_eq (by unfold preconditionedDeletedMarginalBudget; dsimp [c]; ring)
  · have hf0 : 0 ≤ 16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) := by positivity
    have hprod := mul_le_mul_of_nonneg_right heabs hf0
    have hsum := add_le_add (mul_le_mul_of_nonneg_left heta (by norm_num : (0 : ℝ) ≤ 2)) hprod
    have heq : preconditioningCenteredDisplacementBudget (t := t) T a0 I J =
        2 * |preconditioningDeletionEta (t := t) T I J - 1| +
          |preconditioningDeletionEta (t := t) T I J| *
            (16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n)) := by
      unfold preconditioningCenteredDisplacementBudget
      ring
    rw [heq]
    exact hsum.trans_eq (by ring)

end TournamentHamiltonian
