import TournamentHamiltonian.PreconditionedRetainedMassBudget
import TournamentHamiltonian.UniformGaussianCost
import TournamentHamiltonian.PermanentApproximationConstant

namespace TournamentHamiltonian

noncomputable def pairedPermanentErrorBudget (n t : ℕ) (τ : ℝ) : ℝ :=
  Real.sqrt (τ / n) + ((t : ℝ) + 1) / n +
    ((τ + τ ^ 2) / n + τ * Real.sqrt (τ / n)) +
      (t : ℝ) * Real.sqrt (τ / n) + (t : ℝ) ^ 2 / n

noncomputable def pairedPermanentErrorConstant (a0 : ℝ) : ℝ :=
  1 + 5 * (4 / (1 - a0 ^ 2) ^ 2) + 32 / (1 - a0) ^ 2 +
    2 * (8 / (1 - a0) ^ 2 + 1) + preconditioningGaussianCostConstant a0 +
      2 * uniformPermanentActivityConstant (2 * preconditioningScalingDensity a0 + 1) (19 / 20)

theorem pairedPermanentErrorBudget_nonneg (n t : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    0 ≤ pairedPermanentErrorBudget n t τ := by
  unfold pairedPermanentErrorBudget
  positivity

theorem pairedPermanentErrorConstant_pos (a0 : ℝ) :
    0 < pairedPermanentErrorConstant a0 := by
  have hG := (preconditioningGaussianCostConstant_pos a0).le
  have hP := uniformPermanentActivityConstant_nonneg
    (2 * preconditioningScalingDensity a0 + 1) (19 / 20) (by norm_num) (by norm_num)
  unfold pairedPermanentErrorConstant
  positivity

theorem positive_rate_budget_combine (u v w z r a b c d e : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hz : 0 ≤ z) (hr : 0 ≤ r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    v + a * w + b * z + c * r + d * (u + v) + e * v ≤
      (1 + a + b + c + d + e) * (u + v + w + z + r) := by
  have h1 : v ≤ u + v + w + z + r := by linarith
  have h2 : w ≤ u + v + w + z + r := by linarith
  have h3 : z ≤ u + v + w + z + r := by linarith
  have h4 : r ≤ u + v + w + z + r := by linarith
  have h5 : u + v ≤ u + v + w + z + r := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h3 hb,
    mul_le_mul_of_nonneg_left h4 hc, mul_le_mul_of_nonneg_left h5 hd,
    mul_le_mul_of_nonneg_left h1 he]

/-- The actual restoration exponent, Gaussian log cost and finite permanent
error fit one dimension-independent score/deletion budget. -/
theorem paired_permanent_error_exponent_le {n t : ℕ} (T : Tournament n)
    (hn : 1 < n) (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hM : (n : ℝ) / 2 ≤ matrixEntryMass (preconditionedTournamentDensity T))
    (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t) (ht : 2 * t ≤ n) :
    (t : ℝ) / n + |matrixEntryMass (preconditionedTournamentDensity T) - n| +
      |matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) -
        (n - t : ℝ)| + preconditioningGaussianCostConstant a0 *
          (Real.sqrt (scoreVariance T / n) + ((t : ℝ) + 1) / n) +
      uniformPermanentActivityConstant (2 * preconditioningScalingDensity a0 + 1) (19 / 20) /
        (n - t : ℝ) ≤ pairedPermanentErrorConstant a0 * pairedPermanentErrorBudget n t (scoreVariance T) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htR : 2 * (t : ℝ) ≤ n := by exact_mod_cast ht
  have hmR : (0 : ℝ) < n - t := by linarith
  have hτ := scoreVariance_nonneg T
  let p := uniformPermanentActivityConstant (2 * preconditioningScalingDensity a0 + 1) (19 / 20)
  have hp : 0 ≤ p := uniformPermanentActivityConstant_nonneg _ _ (by norm_num) (by norm_num)
  have hper : p / (n - t : ℝ) ≤ 2 * p * (((t : ℝ) + 1) / n) := by
    have hh : (n : ℝ) / 2 ≤ n - t := by linarith
    have h := div_le_div_of_nonneg_left hp (by positivity : (0 : ℝ) < n / 2) hh
    have htwo : p / ((n : ℝ) / 2) = 2 * p / n := by ring
    rw [htwo] at h
    apply h.trans
    have htp : 1 ≤ (t : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) t]
    have hm := mul_le_mul_of_nonneg_left htp (show 0 ≤ 2 * p / n by positivity)
    calc
      _ ≤ (2 * p / n) * ((t : ℝ) + 1) := by simpa only [mul_one] using hm
      _ = _ := by ring
  have htv : (t : ℝ) / n ≤ ((t : ℝ) + 1) / n :=
    div_le_div_of_nonneg_right (by linarith) hnR.le
  have hmass := preconditioned_retained_mass_error_budget T hn a0 h0 h1 ha hM I J hI hJ ht
  have hcombine := positive_rate_budget_combine (Real.sqrt (scoreVariance T / n))
    (((t : ℝ) + 1) / n) ((scoreVariance T + scoreVariance T ^ 2) / n +
      scoreVariance T * Real.sqrt (scoreVariance T / n))
    ((t : ℝ) * Real.sqrt (scoreVariance T / n)) ((t : ℝ) ^ 2 / n)
    (5 * (4 / (1 - a0 ^ 2) ^ 2)) (32 / (1 - a0) ^ 2)
    (2 * (8 / (1 - a0) ^ 2 + 1)) (preconditioningGaussianCostConstant a0) (2 * p)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity)
    (preconditioningGaussianCostConstant_pos a0).le (by positivity)
  change _ ≤ (1 + 5 * (4 / (1 - a0 ^ 2) ^ 2) + 32 / (1 - a0) ^ 2 +
    2 * (8 / (1 - a0) ^ 2 + 1) + preconditioningGaussianCostConstant a0 + 2 * p) * _
  unfold pairedPermanentErrorBudget
  apply le_trans _ hcombine
  dsimp only [p] at hper
  convert add_le_add (add_le_add (add_le_add htv hmass)
    (le_refl (preconditioningGaussianCostConstant a0 *
      (Real.sqrt (scoreVariance T / n) + ((t : ℝ) + 1) / n)))) hper using 1 <;> ring

end TournamentHamiltonian
