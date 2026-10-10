import TournamentHamiltonian.UniformUnitScoreMinors
import TournamentHamiltonian.SmallScorePathsLower

namespace TournamentHamiltonian

open scoped Classical Topology
open Filter

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem exponential_minor_error_product_le (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + r) * Real.exp x ≤ 1 + r + 2 * Real.exp 1 * x := by
  have he := exp_sub_one_le_self_mul_exp x
  have hb := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx1) hx0
  have hexp : Real.exp x ≤ 1 + Real.exp 1 * x := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 1 + r by linarith)
  have hrx := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ Real.exp 1 * x by positivity)
  nlinarith

theorem shortConvolution_upper_from_small_minors {n : ℕ} (T : Tournament n) (K : ℕ)
    (hn : 0 < n) (hK : 2 * K ≤ n) (hfactorial : 2 * (K : ℝ) ^ 2 / n ≤ 1)
    (Q c : ℝ) (hQ : 0 ≤ Q) (hc : 0 ≤ c)
    (hsmall : ∀ U : Finset (Fin n), U.card < K → c * ((U.card : ℝ) + 2) ^ 2 / n ≤ 1)
    (hper : ∀ U : Finset (Fin n), U.card < K →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
          (1 + c * ((U.card : ℝ) + 2) ^ 2 / n)) :
    shortConvolution T K / meanPaths n ≤ Q / 2 *
      (((1 : Matrix (Fin n) (Fin n) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T)).det +
        ((c + 4 * Real.exp 1) / n) * principalErrorMomentConstant) := by
  let Z : ℝ := (n.factorial : ℝ) / (2 : ℝ) ^ n
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  have hmZ : meanPaths n = 2 * Z := by
    dsimp [Z]
    simpa only [mul_div_assoc] using meanPaths_eq_twice_normalization n (by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let b (U : Finset (Fin n)) := (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det
  have hb U : 0 ≤ b U := mul_nonneg (by positivity) (principal_weight_pos T U).le
  have hloc U : (if U.card < K then convolutionTerm T U else 0) / meanPaths n ≤
      Q / 2 * (b U + ((c + 4 * Real.exp 1) / n) * (b U * ((U.card : ℝ) + 2) ^ 2)) := by
    by_cases hs : U.card < K
    · simp only [hs, ite_true]
      have hkN : 2 * U.card ≤ n := by omega
      have hkR : (U.card : ℝ) ≤ K := by exact_mod_cast hs.le
      have hx : 2 * (U.card : ℝ) ^ 2 / n ≤ 1 := by
        apply le_trans _ hfactorial
        apply div_le_div_of_nonneg_right _ hnR.le
        nlinarith [Nat.cast_nonneg (α := ℝ) U.card]
      have he := exponential_minor_error_product_le (c * ((U.card : ℝ) + 2) ^ 2 / n)
        (2 * (U.card : ℝ) ^ 2 / n) (by positivity) (hsmall U hs) (by positivity) hx
      have hdegree : (U.card : ℝ) ^ 2 ≤ ((U.card : ℝ) + 2) ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) U.card]
      have hprod : (1 + c * ((U.card : ℝ) + 2) ^ 2 / n) *
          Real.exp (2 * (U.card : ℝ) ^ 2 / n) ≤
            1 + ((c + 4 * Real.exp 1) / n) * ((U.card : ℝ) + 2) ^ 2 := by
        apply he.trans
        have hh := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdegree (show 0 ≤ 4 * Real.exp 1 by positivity)) hnR.le
        convert add_le_add (le_refl (1 + c * ((U.card : ℝ) + 2) ^ 2 / n)) hh using 1 <;> ring
      have hf := convolution_factorial_ratio_le n U.card hn hkN
      have hd := (principal_weight_pos T U).le
      calc
        _ ≤ (Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
            (1 + c * ((U.card : ℝ) + 2) ^ 2 / n)) * (principalWeightMatrix T U).det / meanPaths n := by
          exact div_le_div_of_nonneg_right
            ((mul_le_mul_of_nonneg_left (hper U hs) hd).trans_eq (by
              change (principalWeightMatrix T U).det * _ = _
              ring)) hm.le
        _ = (Q / 2 * (principalWeightMatrix T U).det) *
            (1 + c * ((U.card : ℝ) + 2) ^ 2 / n) *
              ((((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) / Z) := by rw [hmZ]; ring
        _ ≤ (Q / 2 * (principalWeightMatrix T U).det) *
            (1 + c * ((U.card : ℝ) + 2) ^ 2 / n) *
              (Real.exp (2 * (U.card : ℝ) ^ 2 / n) * (2 / (n : ℝ)) ^ U.card) :=
          mul_le_mul_of_nonneg_left hf (by positivity)
        _ = (Q / 2 * b U) * ((1 + c * ((U.card : ℝ) + 2) ^ 2 / n) *
            Real.exp (2 * (U.card : ℝ) ^ 2 / n)) := by dsimp [b]; ring
        _ ≤ (Q / 2 * b U) * (1 + ((c + 4 * Real.exp 1) / n) * ((U.card : ℝ) + 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = _ := by ring
    · simp only [hs, ite_false, zero_div]
      have hbU := hb U
      positivity
  have hmoment : (∑ U : Finset (Fin n), b U * ((U.card : ℝ) + 2) ^ 2) ≤ principalErrorMomentConstant := by
    convert shortPrincipalErrorMoment_le T (n + 1) hn using 1
    unfold shortPrincipalErrorMoment
    apply Finset.sum_congr rfl
    intro U _
    have hk : U.card < n + 1 := by
      have hh : U.card ≤ n := by simpa using U.card_le_univ
      omega
    simp only [hk, ite_true]
    rfl
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun U _ => hloc U)
  rw [← Finset.sum_div] at hsum
  change shortConvolution T K / meanPaths n ≤ _ at hsum
  apply hsum.trans
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hmass : (∑ U : Finset (Fin n), b U) =
      ((1 : Matrix (Fin n) (Fin n) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T)).det :=
    (principalWeight_generating_det T (2 / (n : ℝ))).symm
  rw [hmass]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hmoment (by positivity))) (by positivity)

noncomputable def unitScorePathUpperConstant : ℝ :=
  (smallScoreUniformPermanentConstant + 4 * Real.exp 1) * principalErrorMomentConstant + 1

theorem unitScorePathUpperConstant_pos : 0 < unitScorePathUpperConstant := by
  have hc := smallScoreUniformPermanentConstant_pos
  have hM := principalErrorMomentConstant_nonneg
  unfold unitScorePathUpperConstant
  positivity

theorem unit_score_path_upper_uniform :
    ∃ N : ℕ, 20 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ T : Tournament n,
      (∀ i, |score T i| ≤ 1) →
        (pathCount T : ℝ) / meanPaths n ≤ spectralRatio T + unitScorePathUpperConstant / n := by
  obtain ⟨Nm, hNm, hm⟩ := unit_score_principal_minors_uniform
  have hevent : ∀ᶠ n : ℕ in atTop, 20 ≤ n ∧ ∀ T : Tournament n, (∀ i, |score T i| ≤ 1) →
      (pathCount T : ℝ) / meanPaths n ≤ spectralRatio T + unitScorePathUpperConstant / n := by
    filter_upwards [eventually_ge_atTop Nm, short_cutoff_eventually_small,
      unit_score_cutoff_budget_eventually_small 2 (by norm_num),
      longConvolution_eventually_small (ε := 1) (by norm_num)] with n hn hcut hfac hlong
    have hn20 : 20 ≤ n := hNm.trans hn
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    refine ⟨hn20, ?_⟩
    intro T hscore
    obtain ⟨_htau, hminor⟩ := hm n hn T hscore
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
          (1 + smallScoreUniformPermanentConstant * ((U.card : ℝ) + 2) ^ 2 / n) := by
      have hh := (abs_le.mp (hminor U hU).2.1).2
      unfold pathLowerPermanentFactor
      nlinarith
    have hshort := shortConvolution_upper_from_small_minors T (subsetCutoff n) hn0 hK hfactorial
      (pathLowerPermanentFactor T) smallScoreUniformPermanentConstant hQ.1 smallScoreUniformPermanentConstant_pos.le
      (fun U hU => (hminor U hU).1) hper
    have hgen := tournament_generating_det_le T n hn0 le_rfl
    have hE : 0 ≤ ((smallScoreUniformPermanentConstant + 4 * Real.exp 1) / n) * principalErrorMomentConstant := by
      have hM := principalErrorMomentConstant_nonneg
      have hc := smallScoreUniformPermanentConstant_pos
      positivity
    have hbound := hshort.trans (mul_le_mul_of_nonneg_left (add_le_add hgen le_rfl)
      (div_nonneg hQ.1 (by norm_num : (0 : ℝ) ≤ 2)))
    have hexp : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
    have heq : pathLowerPermanentFactor T / 2 *
        (2 * Real.exp 1 * ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det +
          ((smallScoreUniformPermanentConstant + 4 * Real.exp 1) / n) * principalErrorMomentConstant) =
        spectralRatio T + pathLowerPermanentFactor T / 2 *
          (((smallScoreUniformPermanentConstant + 4 * Real.exp 1) / n) * principalErrorMomentConstant) := by
      unfold pathLowerPermanentFactor spectralRatio
      calc
        _ = (Real.exp (-1) * Real.exp 1) * gaussianFactor T *
            ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det +
              (Real.exp (-1) * gaussianFactor T / 2) *
                (((smallScoreUniformPermanentConstant + 4 * Real.exp 1) / n) * principalErrorMomentConstant) := by ring
        _ = _ := by rw [hexp]; ring
    rw [heq] at hbound
    have hshort' := hbound.trans (add_le_add le_rfl (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hQ.2 hE))
    have hsplit := shortConvolution_add_longConvolution T (subsetCutoff n)
    have htotal := add_le_add hshort' (hlong T)
    rw [← add_div, hsplit] at htotal
    exact htotal.trans_eq (by unfold unitScorePathUpperConstant; ring)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨max N 20, le_max_right _ _, ?_⟩
  intro n hn
  exact (hN n ((le_max_left N 20).trans hn)).2

end TournamentHamiltonian
