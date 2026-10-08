import TournamentHamiltonian.PairedErrorWeights
import TournamentHamiltonian.WeightedKernelInflation
import TournamentHamiltonian.ShortQuadraticConvolution
import TournamentHamiltonian.FullScoreAbsorption

/-! Actual finite paired short-convolution upper bound, with the full variance
and deletion error retained through generating-function inflation. -/
namespace TournamentHamiltonian
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable def pairedShortInflation (a0 K : ℝ) : ℝ :=
  Real.exp 1 * (1 / (1 - a0 ^ 2) + K) * weightedPrincipalMoment (pairedConvolutionWeightCap a0 1)
noncomputable def pairedShortQuadraticInflation (a0 K : ℝ) : ℝ :=
  (K + 2) * Real.exp 1 * ∑' k, subsetMoment (pairedConvolutionWeightCap a0 1) 2 k

theorem paired_shortConvolution_spectral_of_principal_bound {n : ℕ} (T : Tournament n)
    (N : ℕ) (hn : 1 ≤ n) (hN : 2 * N ≤ n) (a0 K : ℝ)
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (hK : 0 ≤ K)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hx : K * (Real.sqrt (scoreVariance T / n) + 1 / n) ≤ 1)
    (hsmall : (K + 2) * (N : ℝ) ^ 2 / n ≤ 1)
    (hper : ∀ U : Finset (Fin n), U.card < N →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        pairedScoreProduct T * (∏ i ∈ U, pairedLeft (tournamentScorePotential T i)) *
          (∏ j ∈ U, pairedRight (tournamentScorePotential T j)) *
            (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) * gaussianFactor T *
              Real.exp (-1 + K * pairedPermanentErrorBudget n U.card (scoreVariance T))) :
    shortConvolution T N / meanPaths n ≤ spectralRatio T * pairedScoreProduct T * Real.exp
      (K * pairedPermanentErrorBudget n 0 (scoreVariance T) + pairedShortInflation a0 K *
        (scoreVariance T / n + Real.sqrt (scoreVariance T / n) + 1 / n) +
          pairedShortQuadraticInflation a0 K / n) := by
  have hnpos : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hτ := scoreVariance_nonneg T
  have hd : 0 < 1 - a0 ^ 2 := by nlinarith
  let x := K * (Real.sqrt (scoreVariance T / n) + 1 / n)
  let w := pairedErrorWeight T x
  let W := pairedConvolutionWeightCap a0 1
  let R := scoreVariance T / n + Real.sqrt (scoreVariance T / n) + 1 / n
  let C := Real.exp 1 * (1 / (1 - a0 ^ 2) + K)
  let D := pairedShortQuadraticInflation a0 K
  let Q := pairedScoreProduct T * gaussianFactor T * Real.exp (-1) *
    Real.exp (K * pairedPermanentErrorBudget n 0 (scoreVariance T))
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hw := pairedErrorWeight_bounds T a0 x h0 h1 hx0 hx ha
  have hW : 1 ≤ W := by
    have hdle : 1 - a0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg a0]
    have h := (le_div_iff₀ hd).mpr (show 1 * (1 - a0 ^ 2) ≤ Real.exp 1 by
      have he := Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1); linarith)
    exact h
  have hGamma : 0 ≤ pairedScoreProduct T := by
    unfold pairedScoreProduct
    apply Finset.prod_nonneg
    intro i _
    have hs : tournamentScorePotential T i ^ 2 ≤ a0 ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) h0).mpr (ha i)
    linarith
  have hG := (gaussianFactor_bounds T hnpos).1.le
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hmoment : 0 ≤ ∑' k, subsetMoment W 2 k := tsum_nonneg (fun k => subsetMoment_nonneg (by linarith) 2 k)
  have hD : 0 ≤ D := by dsimp [D, pairedShortQuadraticInflation]; positivity
  have hexcess : (∑ i, (w i - 1)) / n ≤ C * R := by
    have h := pairedErrorWeight_excess T hnpos a0 x h0 h1 hx0 hx ha
    apply h.trans
    dsimp [C, R, x]
    have hrate : 0 ≤ scoreVariance T / (n : ℝ) := div_nonneg hτ hn0.le
    have hr : 0 ≤ Real.sqrt (scoreVariance T / n) + 1 / n := by positivity
    have hi : 0 ≤ 1 / (1 - a0 ^ 2) := by positivity
    have hh : (1 / (1 - a0 ^ 2)) * (scoreVariance T / n) +
        K * (Real.sqrt (scoreVariance T / n) + 1 / n) ≤
          (1 / (1 - a0 ^ 2) + K) *
            (scoreVariance T / n + Real.sqrt (scoreVariance T / n) + 1 / n) := by
      nlinarith [mul_nonneg hi hr, mul_nonneg hK hrate]
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg 1)
    convert hm using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring
  have hquad : ∀ U : Finset (Fin n), U.card < N →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) * (∏ i ∈ U, w i) *
          Real.exp (K * (U.card : ℝ) ^ 2 / n) := by
    intro U hU
    have hu := hper U hU
    have hs : -1 + K * pairedPermanentErrorBudget n U.card (scoreVariance T) =
        (-1 + K * pairedPermanentErrorBudget n 0 (scoreVariance T)) + (U.card : ℝ) * x +
          K * (U.card : ℝ) ^ 2 / n := by
      rw [pairedPermanentErrorBudget_card_split]
      dsimp [x]
      ring
    rw [hs] at hu
    simp only [Real.exp_add] at hu
    change _ ≤ Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
      (∏ i ∈ U, pairedErrorWeight T x i) * Real.exp (K * (U.card : ℝ) ^ 2 / n)
    rw [pairedErrorWeight_prod]
    convert hu using 1
    dsimp [Q]
    ring
  have hshort := shortConvolution_le_quadratic_weighted_mass T N hnpos hN K hK hsmall Q hQ
    w W (by linarith) (fun i => by have h := (hw i).1; linarith) (fun i => (hw i).2) hquad
  have hDnorm : ((K + 2) * Real.exp 1 / n) * (∑' k, subsetMoment W 2 k) = D / n := by
    dsimp [D, pairedShortQuadraticInflation, W]
    ring
  rw [hDnorm] at hshort
  have hinfl := weightedPrincipalMass_add_le_kernel_exp T hnpos w W hW (fun i => (hw i).1)
    (fun i => (hw i).2) C R D hC hR hD hexcess
  have hcombine := hshort.trans (mul_le_mul_of_nonneg_left hinfl (by positivity : 0 ≤ Q / 2))
  convert hcombine using 1
  dsimp [Q, C, R, D, W, pairedShortInflation]
  rw [spectralRatio]
  simp only [Real.exp_add, Real.exp_neg]
  field_simp

end TournamentHamiltonian
