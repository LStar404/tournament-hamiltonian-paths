import TournamentHamiltonian.DisjointConvolution
import TournamentHamiltonian.ExceptionalBudgets

/-! Uniform global exceptional exclusion from the remaining actual core permanent estimate. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter

/-- The missing analytic input is explicit: the actual permanent remaining after
short disjoint deletions, with the Gaussian factor of the fixed actual dense core. -/
def HasUniformExceptionalPermanentBound (E : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
    degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
    ∀ U : Finset (Fin n), U.card < subsetCutoff n → Disjoint U (exceptionalVertices T) →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        (Real.exp (-1) * gaussianFactor (inducedTournament T (exceptionalVertices T)ᶜ) *
          (1 / 4 : ℝ) ^ (exceptionalVertices T).card * Real.exp (E n)) *
            (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))

theorem lowVariance_exceptional_eventually_lt_mean_of_remaining_bound (E : ℕ → ℝ)
    (hE : Tendsto E atTop (𝓝 0)) (hper : HasUniformExceptionalPermanentBound E) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
      1 ≤ (exceptionalVertices T).card → (pathCount T : ℝ) < meanPaths n := by
  let eps : ℝ := Real.log (6 / 5 : ℝ) / 2
  have heps : 0 < eps := by dsimp [eps]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  filter_upwards [hE.eventually_le_const heps, convolution_cutoff_error_eventually_small eps heps,
    hper, exceptional_meeting_convolution_eventually_small (1 / 25) (by norm_num),
    longConvolution_eventually_small (ε := 1 / 25) (by norm_num),
    exceptional_core_uniform_dense, short_cutoff_eventually_small]
    with n he hk hp hm hl hcore hn T hV hF
  have hnpos : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hK : 2 * subsetCutoff n ≤ n := by
    have hkR : 2 * (subsetCutoff n : ℝ) ≤ n := by linarith [hn.2.1, hn.2.2]
    exact_mod_cast hkR
  have hN : 0 < (exceptionalVertices T)ᶜ.card := by have := (hcore T hV).1; omega
  have hsum : E n + 2 * (subsetCutoff n : ℝ) ^ 2 / n ≤ Real.log (6 / 5 : ℝ) := by
    dsimp [eps] at he hk
    linarith
  have hExp : Real.exp (E n + 2 * (subsetCutoff n : ℝ) ^ 2 / n) ≤ (6 / 5 : ℝ) :=
    (Real.exp_le_exp.mpr hsum).trans_eq (Real.exp_log (by norm_num))
  have htail : longConvolution T (subsetCutoff n) / meanPaths n ≤ 1 / 25 := by
    apply (hl T).trans
    apply (div_le_iff₀ hn0).mpr
    nlinarith
  exact exceptional_pathCount_lt_mean_of_core_bound T (exceptionalVertices T) (subsetCutoff n)
    hnpos hK hN hF (1 / 4) (E n) (by norm_num) le_rfl hExp (hm T hV) htail (hp T hV)

/-- The high-variance class is already unconditional; only the explicit
low-variance core estimate is required to exclude all actual large scores. -/
theorem largeScore_eventually_lt_mean_of_remaining_bound (E : ℕ → ℝ)
    (hE : Tendsto E atTop (𝓝 0)) (hper : HasUniformExceptionalPermanentBound E) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      1 ≤ (exceptionalVertices T).card → (pathCount T : ℝ) < meanPaths n := by
  filter_upwards [lowVariance_exceptional_eventually_lt_mean_of_remaining_bound E hE hper,
    highVariance_pathCount_eventually_small (ε := 1 / 2) (by norm_num), eventually_ge_atTop (1 : ℕ)]
    with n hlow hhigh hn T hF
  by_cases hV : 16 * (n : ℝ) ^ 2 * Real.log n ≤ degreeVariance T
  · have h := hhigh T hV
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hsmall : (1 / 2 : ℝ) / n < 1 := (div_lt_iff₀ hn0).mpr (by linarith)
    have hm0 : 0 < meanPaths n := by unfold meanPaths; positivity
    exact (div_lt_one hm0).mp (h.trans_lt hsmall)
  · exact hlow T (lt_of_not_ge hV) hF

end TournamentHamiltonian
