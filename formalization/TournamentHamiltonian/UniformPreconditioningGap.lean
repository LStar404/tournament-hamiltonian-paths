import TournamentHamiltonian.UniformDeletionBudgets

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

theorem shiftedSkewNormBudget_sqrt_le_three_quarters (n : ℕ) (hn : 20 ≤ n) :
    Real.sqrt (shiftedSkewNormBudget n) ≤ 3 / 4 := by
  have hnR : (20 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n - 1 : ℝ) ^ 2 := sq_pos_of_pos (by linarith)
  apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 3 / 4)).mpr
  unfold shiftedSkewNormBudget
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 20 by linarith) (show 0 ≤ (n : ℝ) + 10 by linarith)]

theorem normalizedDeletedPreconditioned_centered_gap_uniform_log {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), I.card = t → J.card = t →
          ‖centeringProjection (Iᶜ : Finset (Fin n)) *
            normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J *
              centeringProjection (Jᶜ : Finset (Fin n))‖ ≤ 9 / 10 := by
  obtain ⟨Np, hNp, hp⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  obtain ⟨Ne, hNe, he⟩ := preconditioningDeletionEta_uniform_eventually_small hA hB h0 h1
    (by norm_num : (0 : ℝ) < 1 / 20)
  obtain ⟨Ns, hNs, hs⟩ := score_sqrt_budget_uniform_eventually_small A
    (16 / (1 - a0) ^ 2) (1 / 20) hA (by positivity) (by norm_num)
  refine ⟨max 20 (max Np (max Ne Ns)), le_max_left _ _, ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hn20 : 20 ≤ n := (le_max_left 20 (max Np (max Ne Ns))).trans hn
  have hnNp := (le_max_left Np (max Ne Ns)).trans
    ((le_max_right 20 (max Np (max Ne Ns))).trans hn)
  have hnNe := (le_max_left Ne Ns).trans ((le_max_right Np (max Ne Ns)).trans
    ((le_max_right 20 (max Np (max Ne Ns))).trans hn))
  have hnNs := (le_max_right Ne Ns).trans ((le_max_right Np (max Ne Ns)).trans
    ((le_max_right 20 (max Np (max Ne Ns))).trans hn))
  obtain ⟨_h2t, htn, hM, hX, _hetaBound⟩ := hp n t hnNp T ha hvar hlog I J hI hJ
  have heta := he n t hnNe T ha hvar hlog I J hI hJ
  have hf := hs n hnNs (scoreVariance T) (scoreVariance_nonneg T) hvar
  have hq := shiftedSkewNormBudget_sqrt_le_three_quarters n hn20
  have heabs : |preconditioningDeletionEta (t := t) T I J| ≤ 21 / 20 := by
    have h := abs_add_le (preconditioningDeletionEta (t := t) T I J - 1) 1
    simp only [sub_add_cancel, abs_one] at h
    linarith
  have h := normalizedDeletedPreconditioned_centered_opNorm_le T (by omega)
    I J hI hJ htn a0 h0 h1 ha hM.ne' hX.ne'
  have hsum0 : 0 ≤ Real.sqrt (shiftedSkewNormBudget n) +
      16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) := by positivity
  have hsum : Real.sqrt (shiftedSkewNormBudget n) +
      16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) ≤ 4 / 5 := by linarith
  have hprod := mul_le_mul heabs hsum hsum0 (by norm_num : (0 : ℝ) ≤ 21 / 20)
  exact h.trans (hprod.trans (by norm_num))

end TournamentHamiltonian
