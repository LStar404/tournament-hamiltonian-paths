import TournamentHamiltonian.UniformPreconditioningBudgets

open Filter
open scoped Topology

namespace TournamentHamiltonian

theorem logarithmic_nat_budget_uniform_eventually_small (B c eps : ℝ)
    (_hB : 0 ≤ B) (hc : 0 ≤ c) (heps : 0 < eps) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      (t : ℝ) ≤ B * Real.log (n : ℝ) → c * (t : ℝ) / n ≤ eps := by
  have hlim := log_div_nat_tendsto_zero.const_mul (c * B)
  simp only [mul_zero] at hlim
  have h := hlim.eventually (eventually_lt_nhds heps)
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨max N 4, le_max_right _ _, ?_⟩
  intro n t hn ht
  have h1 : c * (t : ℝ) / n ≤ (c * B) * (Real.log (n : ℝ) / n) := by
    have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht hc) (Nat.cast_nonneg n)
    exact hm.trans_eq (by ring)
  exact h1.trans (by simpa only [sub_zero] using (hN n ((le_max_left N 4).trans hn)).le)

theorem preconditioned_retained_mass_uniform_log {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), I.card = t → J.card = t →
          2 * t ≤ n ∧ t < n ∧
          |matrixEntryMass ((preconditionedTournamentDensity T).submatrix
            (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n)
            (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) - (n - t : ℝ)| ≤ 1 + 4 * t ∧
          (n - t : ℝ) / 2 ≤ matrixEntryMass ((preconditionedTournamentDensity T).submatrix
            (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n)
            (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) := by
  let K : ℝ := 4 / (1 - a0) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨Nm, hNm, hm⟩ := preconditioned_mass_error_uniform_log hA h0 h1 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Ne, hNe, he⟩ := preconditioned_marginal_error_uniform_log hA h1 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Nt, hNt, ht⟩ := logarithmic_nat_budget_uniform_eventually_small B (20 + K) 1 hB
    (by positivity) (by norm_num)
  refine ⟨max Nt (max Nm Ne), hNt.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNt := (le_max_left Nt (max Nm Ne)).trans hn
  have hnNm := (le_max_left Nm Ne).trans ((le_max_right Nt (max Nm Ne)).trans hn)
  have hnNe := (le_max_right Nm Ne).trans ((le_max_right Nt (max Nm Ne)).trans hn)
  have hn4 : 4 ≤ n := hNt.trans hnNt
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn0 : (0 : ℝ) < n := by linarith
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hbudget := (div_le_iff₀ hn0).mp (ht n t hnNt hlog)
  have h20 : 20 * (t : ℝ) ≤ n := by nlinarith [mul_nonneg hK ht0]
  have hKt : K * (t : ℝ) / n ≤ 1 := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith
  have h2tR : 2 * (t : ℝ) ≤ n := by linarith
  have h2t : 2 * t ≤ n := by exact_mod_cast h2tR
  have htn : t < n := by exact_mod_cast (show (t : ℝ) < n by linarith)
  obtain ⟨hrow, hcol⟩ := he n hnNe T ha hvar
  have hentry : ∀ i j, 0 ≤ preconditionedTournamentDensity T i j ∧
      preconditionedTournamentDensity T i j ≤ K / n := by
    intro i j
    simpa only [K, div_div] using preconditionedTournamentDensity_entry_bounds T
      (by omega) a0 h0 h1 ha i j
  have hr := retained_mass_error_bound (preconditionedTournamentDensity T) (by omega)
    I J hI hJ K 1 hentry hrow hcol
  have hsq : K * (t : ℝ) ^ 2 / n ≤ t := by
    have h := mul_le_mul_of_nonneg_right hKt ht0
    convert h using 1 <;> ring
  have herr : |matrixEntryMass ((preconditionedTournamentDensity T).submatrix
      (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n)
      (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) - (n - t : ℝ)| ≤ 1 + 4 * t := by
    have hm' := hm n hnNm T ha hvar
    nlinarith
  refine ⟨h2t, htn, herr, ?_⟩
  have hl := (abs_le.mp herr).1
  linarith

theorem scaledDeletedPreconditioned_mass {n t : ℕ} (T : Tournament n)
    (I J : Finset (Fin n)) :
    matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) =
      ((n : ℝ) / (n - t : ℝ)) * ((n : ℝ) / matrixEntryMass (preconditionedTournamentDensity T)) *
        matrixEntryMass ((preconditionedTournamentDensity T).submatrix
          (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n)
          (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) := by
  rw [scaledDeletedMatrix, matrixEntryMass_smul]
  simp only [normalizedPreconditionedDensity, massNormalizedMatrix, Fintype.card_fin]
  change ((n : ℝ) / (n - t : ℝ)) *
    matrixEntryMass (((n : ℝ) / matrixEntryMass (preconditionedTournamentDensity T)) •
      (preconditionedTournamentDensity T).submatrix Subtype.val Subtype.val) = _
  rw [matrixEntryMass_smul]
  ring

theorem preconditioningDeletionEta_uniform_log_bound {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), I.card = t → J.card = t →
          2 * t ≤ n ∧ t < n ∧
          0 < matrixEntryMass (preconditionedTournamentDensity T) ∧
          0 < matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) ∧
          |preconditioningDeletionEta (t := t) T I J - 1| ≤ 4 * (1 + 4 * t) / n := by
  obtain ⟨Nr, hNr, hr⟩ := preconditioned_retained_mass_uniform_log hA hB h0 h1
  obtain ⟨Nm, hNm, hm⟩ := preconditioned_mass_uniform_lower_log hA h0 h1
  refine ⟨max Nr Nm, hNr.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNr := (le_max_left Nr Nm).trans hn
  have hnNm := (le_max_right Nr Nm).trans hn
  have hn4 : 4 ≤ n := hNr.trans hnNr
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨h2t, htn, herr, hret⟩ := hr n t hnNr T ha hvar hlog I J hI hJ
  have htR : (t : ℝ) < n := by exact_mod_cast htn
  have hM : 0 < matrixEntryMass (preconditionedTournamentDensity T) := by
    have h := hm n hnNm T ha hvar
    linarith
  have hretp : 0 < matrixEntryMass ((preconditionedTournamentDensity T).submatrix
      (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n)
      (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) := by linarith
  have hX : 0 < matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) := by
    rw [scaledDeletedPreconditioned_mass]
    exact mul_pos (mul_pos (div_pos hnR (by linarith)) (div_pos hnR hM)) hretp
  refine ⟨h2t, htn, hM, hX, ?_⟩
  rw [preconditioningDeletionEta_eq_retained_mass T I J htn hM.ne' hX.ne']
  apply finite_eta_error_bound n t _ _ hnR _ hret herr
  have h : 2 * (t : ℝ) ≤ n := by exact_mod_cast h2t
  linarith

theorem deletionEta_log_budget_tendsto_zero (B : ℝ) :
    Tendsto (fun n : ℕ => 4 * (1 + 4 * B * Real.log (n : ℝ)) / n) atTop (𝓝 0) := by
  have h1 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4
  have h2 := log_div_nat_tendsto_zero.const_mul (16 * B)
  have h := h1.add h2
  simp only [mul_zero, zero_add] at h
  convert h using 1
  ext n
  ring

theorem preconditioningDeletionEta_uniform_eventually_small {A B a0 eps : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) (heps : 0 < eps) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), I.card = t → J.card = t →
          |preconditioningDeletionEta (t := t) T I J - 1| ≤ eps := by
  obtain ⟨Nb, hNb, hb⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  obtain ⟨Ne, he⟩ := eventually_atTop.mp
    ((deletionEta_log_budget_tendsto_zero B).eventually (eventually_lt_nhds heps))
  refine ⟨max Nb Ne, hNb.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNb := (le_max_left Nb Ne).trans hn
  have hnNe := (le_max_right Nb Ne).trans hn
  have h := (hb n t hnNb T ha hvar hlog I J hI hJ).2.2.2.2
  have hcomp : 4 * (1 + 4 * (t : ℝ)) / n ≤
      4 * (1 + 4 * B * Real.log (n : ℝ)) / n := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    nlinarith
  exact (h.trans hcomp).trans (he n hnNe).le

end TournamentHamiltonian
