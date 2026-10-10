import TournamentHamiltonian.GeneralScoreShortConvolution
import TournamentHamiltonian.GeneralScoreLowerConvolution
import TournamentHamiltonian.UnitScorePathsApproximation

namespace TournamentHamiltonian
open Filter
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem tournament_generating_det_lower_score_absolute {n : ℕ} (T : Tournament n)
    (hn : 0 < n) (d : ℝ) (hd : 0 ≤ d) (hs : ∀ i, |score T i| ≤ d) :
    2 * Real.exp 1 * ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det -
      (12 * Real.exp 1 * (d + 1) ^ 2) / n ≤
        ((1 : Matrix (Fin n) (Fin n) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T)).det := by
  have h := tournament_generating_det_lower_small_scores T hn d hd hs
  have hdet := (tournament_skew_kernel_det_lt_five_thirds T hn).le
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdet2 : ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det ≤ 2 := by linarith
  have hb := mul_le_mul_of_nonneg_left hdet2
    (show 0 ≤ Real.exp 1 * (5 + d ^ 2) / n by positivity)
  have hsquare : 5 + d ^ 2 ≤ 6 * (d + 1) ^ 2 := by nlinarith [sq_nonneg d]
  have hc := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare
    (show 0 ≤ 2 * Real.exp 1 by positivity)) hnR.le
  have he : (Real.exp 1 * (5 + d ^ 2) / n) *
      ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det ≤
        12 * Real.exp 1 * (d + 1) ^ 2 / n := by
    apply hb.trans
    convert hc using 1 <;> ring
  nlinarith

theorem score_principal_minors_uniform :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ T : Tournament n, ∀ d : ℝ,
      0 ≤ d → (∀ i, |score T i| ≤ d) → scoreVariance T ≤ 1 →
      smallScoreUniformPermanentConstant * (d + (subsetCutoff n : ℝ) + 1) ^ 2 / n ≤ 1 →
      ∀ U : Finset (Fin n), U.card < subsetCutoff n →
        smallScoreUniformPermanentConstant * (d + (U.card : ℝ) + 1) ^ 2 / n ≤ 1 ∧
        |((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent -
          pathLowerPermanentFactor T * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))| ≤
            pathLowerPermanentFactor T * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
              (smallScoreUniformPermanentConstant * (d + (U.card : ℝ) + 1) ^ 2 / n) := by
  obtain ⟨Nm, hNm, hm⟩ := adjacency_nonprincipal_small_score_uniform (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨Nc, hc⟩ := eventually_atTop.mp short_cutoff_eventually_small
  refine ⟨max Nm Nc, hNm.trans (le_max_left _ _), ?_⟩
  intro n hn T d hd hs htau hwindow U hU
  have hnNm : Nm ≤ n := by omega
  have hnNc : Nc ≤ n := by omega
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hkR : (U.card : ℝ) ≤ subsetCutoff n := by exact_mod_cast hU.le
  have hsq : (d + (U.card : ℝ) + 1) ^ 2 ≤ (d + (subsetCutoff n : ℝ) + 1) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    linarith
  have hsmall := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq
    smallScoreUniformPermanentConstant_pos.le) hnR).trans hwindow
  have hlog : (U.card : ℝ) ≤ (1 : ℝ) * Real.log n := by
    simpa only [one_mul] using hkR.trans (hc n hnNc).2.1
  have hsmallLog : smallScoreUniformLogConstant * (d + (U.card : ℝ) + 1) ^ 2 / n ≤ 1 := by
    apply le_trans _ hsmall
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      smallScoreUniformLogConstant_le_permanentConstant (sq_nonneg _)) hnR
  have habs := hm n U.card hnNm T d hd hs htau hlog hsmallLog U U rfl rfl
  rw [rectangularPermanent_principal_deleted] at habs
  exact ⟨hsmall, habs⟩

theorem score_path_upper_uniform :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ T : Tournament n,
      ∀ d : ℝ, 0 ≤ d → (∀ i, |score T i| ≤ d) → scoreVariance T ≤ 1 →
      smallScoreUniformPermanentConstant * (d + (subsetCutoff n : ℝ) + 1) ^ 2 / n ≤ 1 →
        (pathCount T : ℝ) / meanPaths n ≤ spectralRatio T + unitScorePathUpperConstant * (d + 1) ^ 2 / n := by
  obtain ⟨Nm, hNm, hm⟩ := score_principal_minors_uniform
  have hevent : ∀ᶠ n : ℕ in atTop, 20 ≤ n ∧ ∀ T : Tournament n, ∀ d : ℝ, 0 ≤ d → (∀ i, |score T i| ≤ d) → scoreVariance T ≤ 1 →
      smallScoreUniformPermanentConstant * (d + (subsetCutoff n : ℝ) + 1) ^ 2 / n ≤ 1 →
      (pathCount T : ℝ) / meanPaths n ≤ spectralRatio T + unitScorePathUpperConstant * (d + 1) ^ 2 / n := by
    filter_upwards [eventually_ge_atTop Nm, short_cutoff_eventually_small,
      unit_score_cutoff_budget_eventually_small 2 (by norm_num),
      longConvolution_eventually_small (ε := 1) (by norm_num)] with n hn hcut hfac hlong
    have hn20 : 20 ≤ n := hNm.trans hn
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    refine ⟨hn20, ?_⟩
    intro T d hd hscore htau hwindow
    have hminor := hm n hn T d hd hscore htau hwindow
    have hK : 2 * subsetCutoff n ≤ n := by
      have hkR : 2 * (subsetCutoff n : ℝ) ≤ n := by linarith [hcut.2.1, hcut.2.2]
      exact_mod_cast hkR
    have hfactorial : 2 * (subsetCutoff n : ℝ) ^ 2 / n ≤ 1 := by
      apply le_trans _ (hfac (subsetCutoff n) le_rfl)
      apply div_le_div_of_nonneg_right _ hnR.le
      nlinarith [Nat.cast_nonneg (α := ℝ) (subsetCutoff n)]
    have hQ := pathLowerPermanentFactor_bounds T hn0
    have hper (U : Finset (Fin n)) (hU : U.card < subsetCutoff n) :
        ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        pathLowerPermanentFactor T * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
          (1 + smallScoreUniformPermanentConstant * (d + (U.card : ℝ) + 1) ^ 2 / n) := by
      have hh := (abs_le.mp (hminor U hU).2).2
      nlinarith
    have hshort := shortConvolution_upper_from_score_minors T (subsetCutoff n) hn0 hK hfactorial
      (pathLowerPermanentFactor T) smallScoreUniformPermanentConstant d hQ.1 smallScoreUniformPermanentConstant_pos.le hd
      (fun U hU => (hminor U hU).1) hper
    have hgen := tournament_generating_det_le T n hn0 le_rfl
    have hE : 0 ≤ ((smallScoreUniformPermanentConstant * (d + 1) ^ 2 + 4 * Real.exp 1) / n) * principalErrorMomentConstant := by
      have hM := principalErrorMomentConstant_nonneg
      have hc := smallScoreUniformPermanentConstant_pos
      positivity
    have hbound := hshort.trans (mul_le_mul_of_nonneg_left (add_le_add hgen le_rfl)
      (div_nonneg hQ.1 (by norm_num : (0 : ℝ) ≤ 2)))
    have hexp : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
    have heq : pathLowerPermanentFactor T / 2 *
        (2 * Real.exp 1 * ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det +
          ((smallScoreUniformPermanentConstant * (d + 1) ^ 2 + 4 * Real.exp 1) / n) * principalErrorMomentConstant) =
        spectralRatio T + pathLowerPermanentFactor T / 2 *
          (((smallScoreUniformPermanentConstant * (d + 1) ^ 2 + 4 * Real.exp 1) / n) * principalErrorMomentConstant) := by
      unfold pathLowerPermanentFactor spectralRatio
      calc
        _ = (Real.exp (-1) * Real.exp 1) * gaussianFactor T *
            ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det +
              (Real.exp (-1) * gaussianFactor T / 2) *
                (((smallScoreUniformPermanentConstant * (d + 1) ^ 2 + 4 * Real.exp 1) / n) * principalErrorMomentConstant) := by ring
        _ = _ := by rw [hexp]; ring
    rw [heq] at hbound
    have hshort' := hbound.trans (add_le_add le_rfl (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hQ.2 hE))
    have hsplit := shortConvolution_add_longConvolution T (subsetCutoff n)
    have htotal := add_le_add hshort' (hlong T)
    rw [← add_div, hsplit] at htotal
    apply htotal.trans
    have hS : 1 ≤ (d + 1) ^ 2 := by nlinarith
    have hM := principalErrorMomentConstant_nonneg
    have hb := mul_le_mul_of_nonneg_right hS
      (show 0 ≤ 4 * Real.exp 1 * principalErrorMomentConstant + 1 by positivity)
    unfold unitScorePathUpperConstant
    have hh : (smallScoreUniformPermanentConstant * (d + 1) ^ 2 + 4 * Real.exp 1) *
        principalErrorMomentConstant + 1 ≤
        ((smallScoreUniformPermanentConstant + 4 * Real.exp 1) * principalErrorMomentConstant + 1) * (d + 1) ^ 2 := by nlinarith
    convert add_le_add (le_refl (spectralRatio T)) (div_le_div_of_nonneg_right hh hnR.le) using 1
    ring
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨max N 20, le_max_right _ _, ?_⟩
  intro n hn
  exact (hN n ((le_max_left N 20).trans hn)).2


theorem score_path_lower_uniform :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ T : Tournament n, ∀ d : ℝ,
      0 ≤ d → (∀ i, |score T i| ≤ d) → scoreVariance T ≤ 1 →
      smallScoreUniformPermanentConstant * (d + (subsetCutoff n : ℝ) + 1) ^ 2 / n ≤ 1 →
      spectralRatio T - unitScorePathLowerConstant * (d + 1) ^ 2 / n ≤
        (pathCount T : ℝ) / meanPaths n := by
  obtain ⟨Nm, hNm, hm⟩ := score_principal_minors_uniform
  obtain ⟨Nt, ht⟩ := eventually_atTop.mp principal_subset_tail_eventually_le_inverse
  refine ⟨max Nm Nt, hNm.trans (le_max_left _ _), ?_⟩
  intro n hn T d hd hs htau hwindow
  have hnNm : Nm ≤ n := by omega
  have hnNt : Nt ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hminor := hm n hnNm T d hd hs htau hwindow
  have hQ := pathLowerPermanentFactor_bounds T hn0
  have hc := smallScoreUniformPermanentConstant_pos.le
  have hper (U : Finset (Fin n)) (hU : U.card < subsetCutoff n) :
      pathLowerPermanentFactor T * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
        (1 - (smallScoreUniformPermanentConstant * (d + 1) ^ 2) * ((U.card : ℝ) + 2) ^ 2 / n) ≤
          ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent := by
    have hh := (abs_le.mp (hminor U hU).2).1
    have hrad := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (score_minor_radius_sq_le d U.card hd (Nat.cast_nonneg _)) hc) hnR.le
    have hQ0 := hQ.1
    have hbase : 0 ≤ pathLowerPermanentFactor T * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) := by positivity
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_left hrad 1) hbase
    have hh' : pathLowerPermanentFactor T * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
        (1 - smallScoreUniformPermanentConstant * (d + (U.card : ℝ) + 1) ^ 2 / n) ≤
          ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent := by nlinarith
    exact (le_of_eq (by ring)).trans (hmul.trans hh')
  have hlower := pathCount_spectral_lower_from_signed_minors T hn0
    (smallScoreUniformPermanentConstant * (d + 1) ^ 2) (12 * Real.exp 1 * (d + 1) ^ 2)
    (by positivity) (by positivity) (tournament_generating_det_lower_score_absolute T hn0 d hd hs) hper
  have hS : 1 ≤ (d + 1) ^ 2 := by nlinarith
  have htail := (ht n hnNt).trans (div_le_div_of_nonneg_right hS hnR.le)
  have hb : ((12 * Real.exp 1 * (d + 1) ^ 2 +
      (smallScoreUniformPermanentConstant * (d + 1) ^ 2) * principalErrorMomentConstant) / n + subsetTailAt 1 n) ≤
        unitScorePathLowerConstant * (d + 1) ^ 2 / n := by
    apply (add_le_add (le_refl _) htail).trans_eq
    unfold unitScorePathLowerConstant
    ring
  exact (sub_le_sub_left hb (spectralRatio T)).trans hlower

/-- The whole-path approximation uses the original minor error window. -/
theorem score_pathCount_spectral_approximation_uniform :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ T : Tournament n, ∀ d : ℝ,
      0 ≤ d → (∀ i, |score T i| ≤ d) → scoreVariance T ≤ 1 →
      smallScoreUniformPermanentConstant * (d + (subsetCutoff n : ℝ) + 1) ^ 2 / n ≤ 1 →
      |(pathCount T : ℝ) / meanPaths n - spectralRatio T| ≤
        unitScorePathApproximationConstant * (d + 1) ^ 2 / n := by
  obtain ⟨Nu, hNu, hu⟩ := score_path_upper_uniform
  obtain ⟨Nl, hNl, hl⟩ := score_path_lower_uniform
  refine ⟨max Nu Nl, hNu.trans (le_max_left _ _), ?_⟩
  intro n hn T d hd hs htau hwindow
  have hnU : Nu ≤ n := by omega
  have hnL : Nl ≤ n := by omega
  have hupper := hu n hnU T d hd hs htau hwindow
  have hlower := hl n hnL T d hd hs htau hwindow
  have huC := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (le_max_right unitScorePathLowerConstant unitScorePathUpperConstant) (sq_nonneg (d + 1))) (Nat.cast_nonneg (α := ℝ) n)
  have hlC := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (le_max_left unitScorePathLowerConstant unitScorePathUpperConstant) (sq_nonneg (d + 1))) (Nat.cast_nonneg (α := ℝ) n)
  change unitScorePathUpperConstant * (d + 1) ^ 2 / n ≤ unitScorePathApproximationConstant * (d + 1) ^ 2 / n at huC
  change unitScorePathLowerConstant * (d + 1) ^ 2 / n ≤ unitScorePathApproximationConstant * (d + 1) ^ 2 / n at hlC
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end TournamentHamiltonian
