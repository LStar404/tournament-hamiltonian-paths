import TournamentHamiltonian.ScaledGaussianComparison

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem rectangularMarginalVector_euclidean_le (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (delta : ℝ) (hd : 0 ≤ delta) (hr : ∀ i, |matrixRowError X i| ≤ delta)
    (hc : ∀ j, |matrixColumnError X j| ≤ delta) :
    localEuclideanNorm (rectangularMarginalVector X) ≤
      2 * Real.sqrt (Fintype.card ι) * delta := by
  have hrow := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (sq_le_sq₀ (abs_nonneg _) hd).mpr (hr i))
  have hcol := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    (sq_le_sq₀ (abs_nonneg _) hd).mpr (hc j))
  simp only [sq_abs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hrow hcol
  rw [← Fintype.card_congr e] at hcol
  have hsum : localEuclideanNorm (rectangularMarginalVector X) ^ 2 ≤
      2 * Fintype.card ι * delta ^ 2 := by
    rw [localEuclideanNorm_sq]
    simp only [Fintype.sum_sum_type, rectangularMarginalVector, Sum.elim_inl, Sum.elim_inr]
    linarith
  have hm : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hs := Real.sq_sqrt hm
  apply (sq_le_sq₀ (localEuclideanNorm_nonneg (rectangularMarginalVector X))
    (by positivity : 0 ≤ 2 * Real.sqrt (Fintype.card ι) * delta)).mp
  calc
    _ ≤ 2 * Fintype.card ι * delta ^ 2 := hsum
    _ ≤ 4 * Fintype.card ι * delta ^ 2 := by nlinarith [mul_nonneg hm (sq_nonneg delta)]
    _ = (2 * Real.sqrt (Fintype.card ι) * delta) ^ 2 := by
      rw [mul_pow, mul_pow, hs]
      ring

theorem rectangularScaling_frobenius_le_marginal_bound (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K C q eps delta : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ localScalingInverseBudget C q)
    (hd : 0 ≤ delta) (x : ι → ℝ) (y : κ → ℝ)
    (hxy : RectangularScalingWitness X e K C q eps x y)
    (hr : ∀ i, |matrixRowError X i| ≤ delta) (hc : ∀ j, |matrixColumnError X j| ≤ delta) :
    realFrobeniusNorm (rectangularExpScaling X x y - X) ≤
      16 * K * localScalingInverseBudget C q * delta := by
  have hs : 0 < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hp)
  have h := mul_le_mul_of_nonneg_left (rectangularMarginalVector_euclidean_le X e delta hd hr hc)
    (show 0 ≤ 8 * K * localScalingInverseBudget C q / Real.sqrt (Fintype.card ι) by positivity)
  exact hxy.frobenius.trans (h.trans_eq (by field_simp [hs.ne']; ring))

theorem preconditioned_scaling_displacement_uniform_eventually_small {A B a0 eta : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) (heta : 0 < eta) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n t : ℕ, N ≤ n →
      ∀ T : Tournament n, (∀ i, |tournamentScorePotential T i| ≤ a0) →
        scoreVariance T ≤ A * Real.log (n : ℝ) → (t : ℝ) ≤ B * Real.log (n : ℝ) →
        ∀ I J : Finset (Fin n), ∀ hI : I.card = t, ∀ hJ : J.card = t,
          ∀ x : (Iᶜ : Finset (Fin n)) → ℝ, ∀ y : (Jᶜ : Finset (Fin n)) → ℝ,
            RectangularScalingWitness
              (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J)
              (deletedComplementEquiv I J (hI.trans hJ.symm))
              (preconditioningScalingDensity a0) (preconditioningScalingCenteredDensity a0)
              (9 / 10) (preconditioningScalingEpsilon a0) x y →
                realFrobeniusNorm (rectangularExpScaling
                  (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y -
                    normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) ≤ eta := by
  let K := preconditioningScalingDensity a0
  let C := preconditioningScalingCenteredDensity a0
  let L := localScalingInverseBudget C (9 / 10)
  have hK : 0 ≤ K := by dsimp [K, preconditioningScalingDensity]; positivity
  have hC : 0 ≤ C := by dsimp [C, preconditioningScalingCenteredDensity]; linarith
  have hL : 0 ≤ L := localScalingInverseBudget_nonneg C (9 / 10) hC (by norm_num)
  let delta := eta / (16 * K * L + 1)
  have hden : 0 < 16 * K * L + 1 := by positivity
  have hd : 0 < delta := div_pos heta hden
  obtain ⟨Np, hNp, hp⟩ := preconditioningDeletionEta_uniform_log_bound hA hB h0 h1
  obtain ⟨Nm, hNm, hm⟩ := normalizedDeletedPreconditioned_marginal_error_uniform_log hA hB h0 h1 hd
  refine ⟨max Np Nm, hNp.trans (le_max_left _ _), ?_⟩
  intro n t hn T ha hvar hlog I J hI hJ x y hxy
  have hnNp : Np ≤ n := by omega
  have hnNm : Nm ≤ n := by omega
  obtain ⟨_h2t, htn, _hM, _hX, _⟩ := hp n t hnNp T ha hvar hlog I J hI hJ
  obtain ⟨hr, hc⟩ := hm n t hnNm T ha hvar hlog I J hI hJ
  have hcardpos : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  have h := rectangularScaling_frobenius_le_marginal_bound _
    (deletedComplementEquiv I J (hI.trans hJ.symm)) hcardpos K C (9 / 10)
      (preconditioningScalingEpsilon a0) delta hK hL hd.le x y hxy hr hc
  have heq : delta * (16 * K * L + 1) = eta := by dsimp [delta]; field_simp
  apply h.trans
  change 16 * K * L * delta ≤ eta
  nlinarith

end TournamentHamiltonian
