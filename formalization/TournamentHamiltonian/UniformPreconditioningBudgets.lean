import TournamentHamiltonian.EtaBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology Asymptotics

namespace TournamentHamiltonian

theorem log_pow_div_sqrt_nat_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ k / Real.sqrt n) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  have h' := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, Real.rpow_natCast, Real.sqrt_eq_rpow] using h'

noncomputable def pairedMassErrorBudget (N tau c : ℝ) : ℝ :=
  c * ((tau + tau ^ 2) / N + tau * Real.sqrt (tau / N))

theorem pairedMassErrorBudget_coarse (N tau c : ℝ) (hN : 1 ≤ N)
    (ht : 0 ≤ tau) (hc : 0 ≤ c) :
    pairedMassErrorBudget N tau c ≤ 2 * c * (tau + tau ^ 2) / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsN2 := Real.sq_sqrt hN0.le
  have hsNle : Real.sqrt N ≤ N := by
    nlinarith [mul_nonneg hN0.le (show 0 ≤ N - 1 by linarith), Real.sqrt_nonneg N]
  have htroot : Real.sqrt tau ≤ 1 + tau := by
    nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg tau, sq_nonneg tau]
  have h1 : (tau + tau ^ 2) / N ≤ (tau + tau ^ 2) / Real.sqrt N :=
    div_le_div_of_nonneg_left (by positivity) hsN hsNle
  have h2 : tau * Real.sqrt (tau / N) ≤ (tau + tau ^ 2) / Real.sqrt N := by
    rw [Real.sqrt_div ht]
    have he : tau * (Real.sqrt tau / Real.sqrt N) = (tau * Real.sqrt tau) / Real.sqrt N := by ring
    rw [he]
    apply div_le_div_of_nonneg_right _ hsN.le
    nlinarith [mul_le_mul_of_nonneg_left htroot ht]
  unfold pairedMassErrorBudget
  have h := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hc
  exact h.trans_eq (by ring)

theorem logarithmic_mass_budget_tendsto_zero (A c : ℝ) :
    Tendsto (fun n : ℕ => 2 * c * (A * Real.log (n : ℝ) + (A * Real.log (n : ℝ)) ^ 2) / Real.sqrt n)
      atTop (𝓝 0) := by
  have h1 := (log_pow_div_sqrt_nat_tendsto_zero 1).const_mul (2 * c * A)
  have h2 := (log_pow_div_sqrt_nat_tendsto_zero 2).const_mul (2 * c * A ^ 2)
  have h := h1.add h2
  simp only [pow_one, mul_zero, zero_add] at h
  convert h using 1
  ext n
  ring

theorem pairedMassErrorBudget_uniform_eventually_small (A c eps : ℝ)
    (_hA : 0 ≤ A) (hc : 0 ≤ c) (heps : 0 < eps) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ tau : ℝ,
      0 ≤ tau → tau ≤ A * Real.log (n : ℝ) → pairedMassErrorBudget n tau c ≤ eps := by
  have h := (logarithmic_mass_budget_tendsto_zero A c).eventually
    (eventually_lt_nhds heps)
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro n hn tau ht htA
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have htAsq := pow_le_pow_left₀ ht htA 2
  have hsum : tau + tau ^ 2 ≤ A * Real.log (n : ℝ) + (A * Real.log (n : ℝ)) ^ 2 :=
    add_le_add htA htAsq
  have hb := pairedMassErrorBudget_coarse n tau c hnR ht hc
  have hs := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * c))
    (Real.sqrt_nonneg (n : ℝ))
  exact (hb.trans hs).trans (hN n ((le_max_left N 2).trans hn)).le

theorem preconditioned_mass_error_uniform_log {A a0 eps : ℝ} (hA : 0 ≤ A)
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (heps : 0 < eps) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ T : Tournament n,
      (∀ i, |tournamentScorePotential T i| ≤ a0) → scoreVariance T ≤ A * Real.log (n : ℝ) →
        |matrixEntryMass (preconditionedTournamentDensity T) - n| ≤ eps := by
  have hc : 0 ≤ (4 : ℝ) / (1 - a0 ^ 2) ^ 2 := by positivity
  obtain ⟨N, hN2, hN⟩ := pairedMassErrorBudget_uniform_eventually_small A
    (4 / (1 - a0 ^ 2) ^ 2) eps hA hc heps
  refine ⟨N, hN2, ?_⟩
  intro n hn T ha ht
  have hn1 : 1 < n := by omega
  exact (preconditioned_mass_error_bound T hn1 a0 h0 h1 ha).trans
    (hN n hn (scoreVariance T) (scoreVariance_nonneg T) ht)

theorem preconditioned_mass_uniform_lower_log {A a0 : ℝ} (hA : 0 ≤ A)
    (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ T : Tournament n,
      (∀ i, |tournamentScorePotential T i| ≤ a0) → scoreVariance T ≤ A * Real.log (n : ℝ) →
        (n : ℝ) / 2 ≤ matrixEntryMass (preconditionedTournamentDensity T) := by
  obtain ⟨N, hN2, hN⟩ := preconditioned_mass_error_uniform_log hA h0 h1 (show (0 : ℝ) < 1 by norm_num)
  refine ⟨N, hN2, ?_⟩
  intro n hn T ha ht
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (hN2.trans hn)
  have h := (abs_le.mp (hN n hn T ha ht)).1
  linarith

theorem log_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

theorem logarithmic_sqrt_budget_tendsto_zero (A c : ℝ) :
    Tendsto (fun n : ℕ => c * Real.sqrt (A * Real.log (n : ℝ) / n)) atTop (𝓝 0) := by
  have h := ((log_div_nat_tendsto_zero.const_mul A).sqrt).const_mul c
  have he : (fun n : ℕ => c * Real.sqrt (A * Real.log (n : ℝ) / n)) =
      (fun n : ℕ => c * Real.sqrt (A * (Real.log (n : ℝ) / n))) := by
    funext n
    rw [mul_div_assoc]
  rw [he]
  simpa only [mul_zero, Real.sqrt_zero] using h

theorem score_sqrt_budget_uniform_eventually_small (A c eps : ℝ)
    (_hA : 0 ≤ A) (hc : 0 ≤ c) (heps : 0 < eps) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ tau : ℝ,
      0 ≤ tau → tau ≤ A * Real.log (n : ℝ) → c * Real.sqrt (tau / n) ≤ eps := by
  have h := (logarithmic_sqrt_budget_tendsto_zero A c).eventually (eventually_lt_nhds heps)
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro n hn tau _ht htA
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right htA hn0)) hc
  exact hm.trans (hN n ((le_max_left N 2).trans hn)).le

theorem preconditioned_marginal_error_uniform_log {A a0 eps : ℝ} (hA : 0 ≤ A)
    (h1 : a0 < 1) (heps : 0 < eps) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ T : Tournament n,
      (∀ i, |tournamentScorePotential T i| ≤ a0) → scoreVariance T ≤ A * Real.log (n : ℝ) →
        (∀ i, |matrixRowError (preconditionedTournamentDensity T) i| ≤ eps) ∧
          (∀ j, |matrixColumnError (preconditionedTournamentDensity T) j| ≤ eps) := by
  obtain ⟨N, hN2, hN⟩ := score_sqrt_budget_uniform_eventually_small A
    (4 / (1 - a0) ^ 2) eps hA (by positivity) heps
  refine ⟨N, hN2, ?_⟩
  intro n hn T ha ht
  have hb := hN n hn (scoreVariance T) (scoreVariance_nonneg T) ht
  have hn1 : 1 < n := by omega
  exact ⟨fun i => (preconditioned_row_error_abs_bound T hn1 a0 h1 ha i).trans hb,
    fun j => (preconditioned_column_error_abs_bound T hn1 a0 h1 ha j).trans hb⟩

end TournamentHamiltonian
