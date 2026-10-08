import TournamentHamiltonian.DisjointConvolution
import TournamentHamiltonian.ExceptionalBudgets
import TournamentHamiltonian.CrudeSpectralDeterminant

/-! Exceptional exclusion using absolute Gaussian/determinant bounds. This avoids
comparing Gaussian factors of two different actual deleted tournaments. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter

theorem disjointShortConvolution_le_crude {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (K : ℕ) (hn : 0 < n) (hK : 2 * K ≤ n) (hN : 0 < Fᶜ.card) (E : ℝ)
    (hper : ∀ U : Finset (Fin n), U.card < K → Disjoint U F →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        (2 * Real.exp (-1) * (1 / 4 : ℝ) ^ F.card * Real.exp E) *
          (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) :
    disjointShortConvolution T F K / meanPaths n ≤
      (10 / 3) * (1 / 4 : ℝ) ^ F.card * Real.exp (E + 2 * (K : ℝ) ^ 2 / n) := by
  have h := disjointShortConvolution_le_core_det T F K hn hK
    (2 * Real.exp (-1) * (1 / 4 : ℝ) ^ F.card * Real.exp E) (by positivity) hper
  have hd := (tournament_skew_kernel_det_lt_five_thirds (inducedTournament T Fᶜ) hN).le
  have hm := mul_le_mul_of_nonneg_left hd (by positivity :
    0 ≤ (2 * Real.exp (-1) * (1 / 4 : ℝ) ^ F.card * Real.exp E) * Real.exp 1 *
      Real.exp (2 * (K : ℝ) ^ 2 / n))
  apply h.trans
  convert hm using 1
  rw [Real.exp_add, Real.exp_neg]
  field_simp
  ring

theorem exceptional_pathCount_lt_mean_of_crude_bound {n : ℕ} (T : Tournament n)
    (F : Finset (Fin n)) (K : ℕ) (hn : 0 < n) (hK : 2 * K ≤ n)
    (hN : 0 < Fᶜ.card) (hF : 1 ≤ F.card) (E : ℝ)
    (hE : Real.exp (E + 2 * (K : ℝ) ^ 2 / n) ≤ 21 / 20)
    (hm : meetingShortConvolution T F K / meanPaths n ≤ 1 / 25)
    (hl : longConvolution T K / meanPaths n ≤ 1 / 25)
    (hper : ∀ U : Finset (Fin n), U.card < K → Disjoint U F →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        (2 * Real.exp (-1) * (1 / 4 : ℝ) ^ F.card * Real.exp E) *
          (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) :
    (pathCount T : ℝ) < meanPaths n := by
  have hp : (1 / 4 : ℝ) ^ F.card ≤ 1 / 4 := by
    simpa only [pow_one] using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1) hF
  have hd := disjointShortConvolution_le_crude T F K hn hK hN E hper
  have hb := mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 10 / 3))
    hE (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ (10 / 3) * (1 / 4))
  have hsum : (pathCount T : ℝ) / meanPaths n =
      disjointShortConvolution T F K / meanPaths n + meetingShortConvolution T F K / meanPaths n +
        longConvolution T K / meanPaths n := by
    rw [pathCount_eq_disjoint_meeting_long T F K, add_div, add_div]
  have hbound : (pathCount T : ℝ) / meanPaths n ≤ 191 / 200 := by rw [hsum]; nlinarith
  have hmean : 0 < meanPaths n := by unfold meanPaths; positivity
  exact (div_lt_one hmean).mp (hbound.trans_lt (by norm_num))

/-- Explicit actual remaining-permanent input; the weaker absolute factor 2
allows every deleted core to use its own genuine Gaussian factor. -/
def HasCrudeUniformExceptionalPermanentBound (E : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
    degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
    ∀ U : Finset (Fin n), U.card < subsetCutoff n → Disjoint U (exceptionalVertices T) →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        (2 * Real.exp (-1) * (1 / 4 : ℝ) ^ (exceptionalVertices T).card * Real.exp (E n)) *
          (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))

theorem lowVariance_exceptional_eventually_lt_mean_of_crude_bound (E : ℕ → ℝ)
    (hE : Tendsto E atTop (𝓝 0)) (hper : HasCrudeUniformExceptionalPermanentBound E) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
      1 ≤ (exceptionalVertices T).card → (pathCount T : ℝ) < meanPaths n := by
  let eps : ℝ := Real.log (21 / 20 : ℝ) / 2
  have heps : 0 < eps := by dsimp [eps]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  filter_upwards [hE.eventually_le_const heps, convolution_cutoff_error_eventually_small eps heps,
    hper, exceptional_meeting_convolution_eventually_small (1 / 25) (by norm_num),
    longConvolution_eventually_small (ε := 1 / 25) (by norm_num),
    exceptional_core_uniform_dense, short_cutoff_eventually_small]
    with n he hk hp hm hl hcore hn T hV hF
  have hnpos : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hK : 2 * subsetCutoff n ≤ n := by
    have hkR : 2 * (subsetCutoff n : ℝ) ≤ n := by linarith [hn.2.1, hn.2.2]
    exact_mod_cast hkR
  have hN : 0 < (exceptionalVertices T)ᶜ.card := by have := (hcore T hV).1; omega
  have hsum : E n + 2 * (subsetCutoff n : ℝ) ^ 2 / n ≤ Real.log (21 / 20 : ℝ) := by
    dsimp [eps] at he hk
    linarith
  have hExp : Real.exp (E n + 2 * (subsetCutoff n : ℝ) ^ 2 / n) ≤ (21 / 20 : ℝ) :=
    (Real.exp_le_exp.mpr hsum).trans_eq (Real.exp_log (by norm_num))
  have htail : longConvolution T (subsetCutoff n) / meanPaths n ≤ 1 / 25 := by
    apply (hl T).trans
    apply (div_le_iff₀ hn0).mpr
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith
  exact exceptional_pathCount_lt_mean_of_crude_bound T (exceptionalVertices T) (subsetCutoff n)
    hnpos hK hN hF (E n) hExp (hm T hV) htail (hp T hV)

theorem largeScore_eventually_lt_mean_of_crude_bound (E : ℕ → ℝ)
    (hE : Tendsto E atTop (𝓝 0)) (hper : HasCrudeUniformExceptionalPermanentBound E) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      1 ≤ (exceptionalVertices T).card → (pathCount T : ℝ) < meanPaths n := by
  filter_upwards [lowVariance_exceptional_eventually_lt_mean_of_crude_bound E hE hper,
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
