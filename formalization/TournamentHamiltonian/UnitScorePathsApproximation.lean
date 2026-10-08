import TournamentHamiltonian.UnitScorePathsUpper
import TournamentHamiltonian.UnitScorePathsLower

namespace TournamentHamiltonian

noncomputable def unitScorePathApproximationConstant : ℝ :=
  max unitScorePathLowerConstant unitScorePathUpperConstant

theorem unitScorePathApproximationConstant_pos : 0 < unitScorePathApproximationConstant :=
  unitScorePathUpperConstant_pos.trans_le (le_max_right _ _)

/-- Actual Hamilton paths have the stated spectral approximation uniformly
over all tournaments whose vertex scores have absolute value at most one. -/
theorem unit_score_pathCount_spectral_approximation_uniform :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ T : Tournament n,
      (∀ i, |score T i| ≤ 1) →
        |(pathCount T : ℝ) / meanPaths n - spectralRatio T| ≤
          unitScorePathApproximationConstant / n := by
  obtain ⟨Nl, hNl, hl⟩ := unit_score_pathCount_spectral_lower_uniform
  obtain ⟨Nu, _hNu, hu⟩ := unit_score_path_upper_uniform
  refine ⟨max Nl Nu, hNl.trans (le_max_left _ _), ?_⟩
  intro n hn T hs
  have hlo := hl n (by omega) T hs
  have hup := hu n (by omega) T hs
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcl := div_le_div_of_nonneg_right (le_max_left unitScorePathLowerConstant unitScorePathUpperConstant) hnR
  have hcu := div_le_div_of_nonneg_right (le_max_right unitScorePathLowerConstant unitScorePathUpperConstant) hnR
  unfold unitScorePathApproximationConstant
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end TournamentHamiltonian
