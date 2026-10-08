import TournamentHamiltonian.PreconditionedMarginalBudgets

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

noncomputable def preconditioningGaussianCostConstant (a0 : ℝ) : ℝ :=
  let c : ℝ := 4 / (1 - a0) ^ 2
  let a : ℝ := (1400 / 39) * 16 * preconditioningScalingDensity a0 *
    localScalingInverseBudget (preconditioningScalingCenteredDensity a0) (9 / 10)
  let b : ℝ := 250 / 19
  (2 * a * c + 8 * b * c + 18) + (a * (2 * c + 16) + 32 * b + 24) +
    (4 * a + 8 * b + 11)

theorem preconditioningGaussianCostConstant_pos (a0 : ℝ) :
    0 < preconditioningGaussianCostConstant a0 := by
  have hC : 0 ≤ preconditioningScalingCenteredDensity a0 := by
    unfold preconditioningScalingCenteredDensity preconditioningScalingDensity
    positivity
  have hL := localScalingInverseBudget_nonneg _ (9 / 10) hC (by norm_num)
  have hK : 0 ≤ preconditioningScalingDensity a0 := by
    unfold preconditioningScalingDensity
    positivity
  unfold preconditioningGaussianCostConstant
  dsimp only
  positivity

theorem gaussian_cost_scalar_bound (a c b u v w : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    a * (2 * c * u + 2 * c * v + 4 * w + 16 * v) +
        b * (8 * w + 32 * v + 8 * c * u) + 24 * v + 18 * u + 11 * w ≤
      ((2 * a * c + 8 * b * c + 18) + (a * (2 * c + 16) + 32 * b + 24) +
        (4 * a + 8 * b + 11)) * (u + v + w) := by
  have h1 : 0 ≤ 2 * a * c + 8 * b * c + 18 := by positivity
  have h2 : 0 ≤ a * (2 * c + 16) + 32 * b + 24 := by positivity
  have h3 : 0 ≤ 4 * a + 8 * b + 11 := by positivity
  nlinarith [mul_nonneg h1 hv, mul_nonneg h1 hw, mul_nonneg h2 hu,
    mul_nonneg h2 hw, mul_nonneg h3 hu, mul_nonneg h3 hv]

theorem exists_preconditioned_scaling_gaussian_cost_uniform_log {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), ∀ hI : I.card = t, ∀ hJ : J.card = t,
          ∃ x : (Iᶜ : Finset (Fin n)) → ℝ, ∃ y : (Jᶜ : Finset (Fin n)) → ℝ,
            let X := normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J
            let BX := rectangularExpScaling X x y
            RectangularScalingWitness X (deletedComplementEquiv I J (hI.trans hJ.symm))
              (preconditioningScalingDensity a0) (preconditioningScalingCenteredDensity a0)
              (9 / 10) (preconditioningScalingEpsilon a0) x y ∧
            |Real.log (gramGaussian (BX - rectangularAverageMatrix _ _)) - Real.log (gaussianFactor T)| ≤
              preconditioningGaussianCostConstant a0 *
                (Real.sqrt (scoreVariance T / n) + ((t : ℝ) + 1) / n) := by
  obtain ⟨Ng, hNg, hg⟩ := exists_preconditioned_scaling_gaussian_uniform_log hA hB h0 h1
  obtain ⟨Nm, _hNm, hm⟩ := preconditioned_deleted_marginal_budget_uniform_log hA hB h0 h1
  obtain ⟨Np, _hNp, hp⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  obtain ⟨Ns, _hNs, hs⟩ := score_sqrt_budget_uniform_eventually_small A 1 1 hA
    (by norm_num) (by norm_num)
  refine ⟨max Ng (max Nm (max Np Ns)), hNg.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ
  have hnNg : Ng ≤ n := by omega
  have hnNm : Nm ≤ n := by omega
  have hnNp : Np ≤ n := by omega
  have hnNs : Ns ≤ n := by omega
  have hn20 : 20 ≤ n := hNg.trans hnNg
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨x, y, hxy, hgauss⟩ := hg n t hnNg T ha hvar hlog I J hI hJ
  obtain ⟨hr, hc, hD⟩ := hm n t hnNm T ha hvar hlog I J hI hJ
  obtain ⟨_h2t, htn, _hM, _hX, _he⟩ := hp n t hnNp T ha hvar hlog I J hI hJ
  let K := preconditioningScalingDensity a0
  let C := preconditioningScalingCenteredDensity a0
  let L := localScalingInverseBudget C (9 / 10)
  let c : ℝ := 4 / (1 - a0) ^ 2
  let a : ℝ := (1400 / 39) * 16 * K * L
  have hK : 0 ≤ K := by dsimp [K, preconditioningScalingDensity]; positivity
  have hC : 0 ≤ C := by dsimp [C, preconditioningScalingCenteredDensity]; linarith
  have hL : 0 ≤ L := localScalingInverseBudget_nonneg C (9 / 10) hC (by norm_num)
  have hcc : 0 ≤ c := by dsimp [c]; positivity
  have haa : 0 ≤ a := by dsimp [a]; positivity
  have hdelta : 0 ≤ preconditionedDeletedMarginalBudget n t (scoreVariance T) a0 := by
    unfold preconditionedDeletedMarginalBudget
    positivity
  have hcardpos : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  have hdisp := rectangularScaling_frobenius_le_marginal_bound _
    (deletedComplementEquiv I J (hI.trans hJ.symm)) hcardpos K C (9 / 10)
      (preconditioningScalingEpsilon a0) _ hK hL hdelta x y hxy hr hc
  have htau : 0 ≤ scoreVariance T / (n : ℝ) := div_nonneg (scoreVariance_nonneg T) hnpos.le
  have hsmall := hs n hnNs (scoreVariance T) (scoreVariance_nonneg T) hvar
  simp only [one_mul] at hsmall
  have hsquare := Real.sq_sqrt htau
  have htaubound : scoreVariance T / (n : ℝ) ≤ Real.sqrt (scoreVariance T / n) := by
    nlinarith [Real.sqrt_nonneg (scoreVariance T / n)]
  have hf := mul_le_mul_of_nonneg_left hdisp (by norm_num : (0 : ℝ) ≤ 1400 / 39)
  have hd := mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 250 / 19)
  have he : (24 * (t : ℝ) + 18 * scoreVariance T + 11) / n ≤
      24 * ((t : ℝ) / n) + 18 * Real.sqrt (scoreVariance T / n) + 11 * (1 / n) := by
    have hh := mul_le_mul_of_nonneg_left htaubound (by norm_num : (0 : ℝ) ≤ 18)
    calc
      _ = 24 * ((t : ℝ) / n) + 18 * (scoreVariance T / n) + 11 * (1 / n) := by ring
      _ ≤ _ := by linarith
  refine ⟨x, y, hxy, ?_⟩
  have hb := hgauss.trans (add_le_add (add_le_add hf hd) he)
  have hscalar := gaussian_cost_scalar_bound a c (250 / 19)
    (Real.sqrt (scoreVariance T / n)) ((t : ℝ) / n) (1 / (n : ℝ))
      haa hcc (by norm_num) (Real.sqrt_nonneg _) (by positivity) (by positivity)
  have hleft : (1400 / 39) * (16 * K * L * preconditionedDeletedMarginalBudget n t (scoreVariance T) a0) +
      (250 / 19) * (8 * (1 + 4 * (t : ℝ)) / n + (32 / (1 - a0) ^ 2) * Real.sqrt (scoreVariance T / n)) +
        (24 * ((t : ℝ) / n) + 18 * Real.sqrt (scoreVariance T / n) + 11 * (1 / n)) =
      a * (2 * c * Real.sqrt (scoreVariance T / n) + 2 * c * ((t : ℝ) / n) + 4 * (1 / n) + 16 * ((t : ℝ) / n)) +
        (250 / 19) * (8 * (1 / n) + 32 * ((t : ℝ) / n) + 8 * c * Real.sqrt (scoreVariance T / n)) +
          24 * ((t : ℝ) / n) + 18 * Real.sqrt (scoreVariance T / n) + 11 * (1 / n) := by
    dsimp [a, c, preconditionedDeletedMarginalBudget]
    ring
  rw [hleft] at hb
  exact hb.trans (hscalar.trans_eq (by dsimp [preconditioningGaussianCostConstant, a, c, K, C, L]; ring))

end TournamentHamiltonian
