import TournamentHamiltonian.PairedShortSpectral
import TournamentHamiltonian.UniformPairedPermanentGaussian
import TournamentHamiltonian.ExceptionalBudgets

/-! Unconditional uniform actual short-path upper bound. The analytic principal
minor premise is discharged by the proved paired/nonprincipal permanent theorem. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem principalPermanent_eq_rectangularPermanent {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) (e : (Uᶜ : Finset (Fin n)) ≃ (Uᶜ : Finset (Fin n))) :
    ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent =
      rectangularPermanent (nonprincipalSubmatrix (adjacency T) U U) e := by
  have h := rectangularPermanent_independent (nonprincipalSubmatrix (adjacency T) U U)
    e (Equiv.refl (Uᶜ : Finset (Fin n)))
  exact h.symm

theorem actual_paired_shortConvolution_uniform_upper (A a0 : ℝ)
    (hA : 0 ≤ A) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      (∀ i, |tournamentScorePotential T i| ≤ a0) → scoreVariance T ≤ A * Real.log (n : ℝ) →
      shortConvolution T (subsetCutoff n) / meanPaths n ≤ spectralRatio T + C / n := by
  obtain ⟨K, hK, Np, _hNp, hp⟩ := adjacency_nonprincipal_gaussian_uniform_log
    (A := A) (B := 1) (a0 := a0) hA (by norm_num) h0 h1
  let W := pairedConvolutionWeightCap a0 1
  let Ceff := pairedShortInflation a0 K
  let D := pairedShortQuadraticInflation a0 K
  let B := fullScoreAbsorptionExponent K Ceff D
  let C := 3 * (B * Real.exp B)
  have hd : 0 < 1 - a0 ^ 2 := by nlinarith
  have hW : 0 ≤ W := by dsimp [W, pairedConvolutionWeightCap]; positivity
  have hM1 := weightedPrincipalMoment_nonneg W hW
  have hM2 : 0 ≤ ∑' k, subsetMoment W 2 k := tsum_nonneg (fun k => subsetMoment_nonneg hW 2 k)
  have hCeff : 0 ≤ Ceff := by dsimp [Ceff, pairedShortInflation]; positivity
  have hD : 0 ≤ D := by dsimp [D, pairedShortQuadraticInflation]; positivity
  have hB : 0 ≤ B := by dsimp [B, fullScoreAbsorptionExponent]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hxlim := (((hlog.const_mul A).sqrt).add hinv).const_mul K
  simp only [mul_zero, Real.sqrt_zero, add_zero] at hxlim
  have heps : 0 < (2 / (K + 2) : ℝ) := by positivity
  filter_upwards [hxlim.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    convolution_cutoff_error_eventually_small (2 / (K + 2)) heps,
    actual_full_score_factor_uniform A K Ceff D hA hK.le hCeff hD,
    short_cutoff_eventually_small, eventually_ge_atTop Np, eventually_ge_atTop (1 : ℕ)]
    with n hx hk hscore hcut hnNp hn T ha hvar
  have hnpos : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hcutN : 2 * subsetCutoff n ≤ n := by
    have h : (2 : ℝ) * subsetCutoff n ≤ n := by linarith [hcut.2.1, hcut.2.2]
    exact_mod_cast h
  have hxT : K * (Real.sqrt (scoreVariance T / n) + 1 / n) ≤ 1 := by
    change K * (Real.sqrt (A * (Real.log (n : ℝ) / n)) + (n : ℝ)⁻¹) ≤ 1 at hx
    have hr := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hvar hn0.le)
    have heq : (A * Real.log (n : ℝ)) / n = A * (Real.log (n : ℝ) / n) := by ring
    rw [heq] at hr
    apply le_trans _ hx
    exact mul_le_mul_of_nonneg_left (add_le_add hr (by simp : (1 / (n : ℝ)) ≤ (n : ℝ)⁻¹)) hK.le
  have hsmall : (K + 2) * (subsetCutoff n : ℝ) ^ 2 / n ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ (K + 2) / 2)
    convert h using 1 <;> field_simp
  have hper : ∀ U : Finset (Fin n), U.card < subsetCutoff n →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        pairedScoreProduct T * (∏ i ∈ U, pairedLeft (tournamentScorePotential T i)) *
          (∏ j ∈ U, pairedRight (tournamentScorePotential T j)) *
            (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) * gaussianFactor T *
              Real.exp (-1 + K * pairedPermanentErrorBudget n U.card (scoreVariance T)) := by
    intro U hU
    have ht : (U.card : ℝ) ≤ 1 * Real.log (n : ℝ) := by
      have h : (U.card : ℝ) ≤ subsetCutoff n := by exact_mod_cast hU.le
      linarith [hcut.2.1]
    rw [principalPermanent_eq_rectangularPermanent T U (deletedComplementEquiv U U rfl)]
    have h := hp n U.card hnNp T ha hvar ht U U rfl rfl
    convert h using 1
    ring
  have hshort := paired_shortConvolution_spectral_of_principal_bound T (subsetCutoff n) hn
    hcutN a0 K h0 h1 hK.le ha hxT hsmall hper
  have hfactor := hscore T (fun i => (ha i).trans (by linarith)) hvar
  have hrho := spectralRatio_bounds T hnpos
  have hmul := mul_le_mul_of_nonneg_left hfactor hrho.1.le
  have hmain : shortConvolution T (subsetCutoff n) / meanPaths n ≤
      spectralRatio T * (1 + (B * Real.exp B) / n) := by
    apply hshort.trans
    convert hmul using 1
    ring
  have herr := mul_le_mul_of_nonneg_right hrho.2
    (by positivity : 0 ≤ (B * Real.exp B) / n)
  apply hmain.trans
  dsimp [C]
  convert add_le_add (le_refl (spectralRatio T)) herr using 1 <;> ring

end TournamentHamiltonian
