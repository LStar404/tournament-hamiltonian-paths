import TournamentHamiltonian.UniformPairedShortUpper
import TournamentHamiltonian.ActualExceptionalExclusion
import TournamentHamiltonian.OperatorCap

/-! Unconditional upper bound for every actual tournament Hamiltonian path count.
The high-variance, large-score and dense paired classes cover all tournaments. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter
set_option backward.isDefEq.respectTransparency false

theorem scorePotential_cap_of_exceptional_empty {n : ℕ} (T : Tournament n)
    (hn : 2 ≤ n) (hF : exceptionalVertices T = ∅) :
    ∀ i, |tournamentScorePotential T i| ≤ 9 / 10 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 1 := by linarith
  intro i
  have hscore : |score T i| ≤ (9 / 10 : ℝ) * ((n : ℝ) - 1) := by
    by_contra h
    have hi : i ∈ exceptionalVertices T := by
      simp only [exceptionalVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_not_ge h
    rw [hF] at hi
    simp at hi
  rw [tournamentScorePotential, abs_div, abs_of_pos hd]
  exact (div_le_iff₀ hd).mpr hscore

theorem scoreVariance_le_256_log_of_lowVariance {n : ℕ} (T : Tournament n) (hn : 2 ≤ n)
    (hV : degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n) :
    scoreVariance T ≤ 256 * Real.log (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hd : 0 < (n : ℝ) - 1 := by linarith
  have hden : 0 < ((n : ℝ) - 1) ^ 2 := by positivity
  have hs : (n : ℝ) ^ 2 ≤ 4 * ((n : ℝ) - 1) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hm := mul_le_mul_of_nonneg_right hs hlog
  rw [scoreVariance_eq_degreeVariance]
  apply (div_le_iff₀ hden).mpr
  nlinarith

theorem actual_uniform_pathCount_upper :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      (pathCount T : ℝ) / meanPaths n ≤ upperConstant + C / n := by
  obtain ⟨C, hC, hshort⟩ := actual_paired_shortConvolution_uniform_upper 256 (9 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C + 1, by linarith, ?_⟩
  filter_upwards [hshort, actual_largeScore_eventually_lt_mean,
    highVariance_pathCount_eventually_small (ε := 1) (by norm_num),
    longConvolution_eventually_small (ε := 1) (by norm_num), eventually_ge_atTop (2 : ℕ)]
    with n hs he hv hl hn T
  have hnpos : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hCdiv : 0 ≤ C / (n : ℝ) := div_nonneg hC hn0.le
  have hC1div : 0 ≤ (C + 1) / (n : ℝ) := by positivity
  have hupper := upperConstant_bounds.1
  by_cases hV : 16 * (n : ℝ) ^ 2 * Real.log n ≤ degreeVariance T
  · have h := hv T hV
    simp only [one_div] at h
    apply h.trans
    have heq : (C + 1) / (n : ℝ) = C / n + (n : ℝ)⁻¹ := by ring
    rw [heq]
    linarith
  by_cases hF : 1 ≤ (exceptionalVertices T).card
  · have hmean : 0 < meanPaths n := by unfold meanPaths; positivity
    have h := (div_lt_one hmean).mpr (he T hF)
    linarith
  have hFempty : exceptionalVertices T = ∅ := Finset.card_eq_zero.mp (by omega)
  have hlow : degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n := lt_of_not_ge hV
  have hcap := scorePotential_cap_of_exceptional_empty T hn hFempty
  have hvar := scoreVariance_le_256_log_of_lowVariance T hn hlow
  have hmain := hs T hcap hvar
  have htail := hl T
  have hρ := spectralRatio_le_upperConstant T hnpos
  rw [← shortConvolution_add_longConvolution T (subsetCutoff n), add_div]
  calc
    _ ≤ spectralRatio T + C / n + 1 / n := add_le_add hmain htail
    _ ≤ upperConstant + (C + 1) / n := by
      have h := add_le_add hρ (le_refl (C / n + 1 / (n : ℝ)))
      convert h using 1 <;> ring

end TournamentHamiltonian
