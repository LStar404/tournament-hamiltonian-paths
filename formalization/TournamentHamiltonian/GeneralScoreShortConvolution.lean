import TournamentHamiltonian.UnitScorePathsUpper

namespace TournamentHamiltonian
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem score_minor_radius_sq_le (d k : ℝ) (hd : 0 ≤ d) (hk : 0 ≤ k) :
    (d + k + 1) ^ 2 ≤ (d + 1) ^ 2 * (k + 2) ^ 2 := by
  have h : d + k + 1 ≤ (d + 1) * (k + 2) := by nlinarith [mul_nonneg hd hk]
  have hh := (sq_le_sq₀ (by positivity : 0 ≤ d + k + 1)
    (by positivity : 0 ≤ (d + 1) * (k + 2))).mpr h
  simpa only [mul_pow] using hh
theorem shortConvolution_upper_from_score_minors {n : ℕ} (T : Tournament n) (K : ℕ)
    (hn : 0 < n) (hK : 2 * K ≤ n) (hfactorial : 2 * (K : ℝ) ^ 2 / n ≤ 1)
    (Q c d : ℝ) (hQ : 0 ≤ Q) (hc : 0 ≤ c) (hdscore : 0 ≤ d)
    (hsmall : ∀ U : Finset (Fin n), U.card < K → c * (d + (U.card : ℝ) + 1) ^ 2 / n ≤ 1)
    (hper : ∀ U : Finset (Fin n), U.card < K →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
          (1 + c * (d + (U.card : ℝ) + 1) ^ 2 / n)) :
    shortConvolution T K / meanPaths n ≤ Q / 2 *
      (((1 : Matrix (Fin n) (Fin n) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T)).det +
        ((c * (d + 1) ^ 2 + 4 * Real.exp 1) / n) * principalErrorMomentConstant) := by
  let Z : ℝ := (n.factorial : ℝ) / (2 : ℝ) ^ n
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  have hmZ : meanPaths n = 2 * Z := by
    dsimp [Z]
    simpa only [mul_div_assoc] using meanPaths_eq_twice_normalization n (by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let b (U : Finset (Fin n)) := (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det
  have hb U : 0 ≤ b U := mul_nonneg (by positivity) (principal_weight_pos T U).le
  have hloc U : (if U.card < K then convolutionTerm T U else 0) / meanPaths n ≤
      Q / 2 * (b U + ((c * (d + 1) ^ 2 + 4 * Real.exp 1) / n) * (b U * ((U.card : ℝ) + 2) ^ 2)) := by
    by_cases hs : U.card < K
    · simp only [hs, ite_true]
      have hkN : 2 * U.card ≤ n := by omega
      have hkR : (U.card : ℝ) ≤ K := by exact_mod_cast hs.le
      have hx : 2 * (U.card : ℝ) ^ 2 / n ≤ 1 := by
        apply le_trans _ hfactorial
        apply div_le_div_of_nonneg_right _ hnR.le
        nlinarith [Nat.cast_nonneg (α := ℝ) U.card]
      have he := exponential_minor_error_product_le (c * (d + (U.card : ℝ) + 1) ^ 2 / n)
        (2 * (U.card : ℝ) ^ 2 / n) (by positivity) (hsmall U hs) (by positivity) hx
      have hdegree : (U.card : ℝ) ^ 2 ≤ ((U.card : ℝ) + 2) ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) U.card]
      have hprod : (1 + c * (d + (U.card : ℝ) + 1) ^ 2 / n) *
          Real.exp (2 * (U.card : ℝ) ^ 2 / n) ≤
            1 + ((c * (d + 1) ^ 2 + 4 * Real.exp 1) / n) * ((U.card : ℝ) + 2) ^ 2 := by
        apply he.trans
        have hh := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdegree (show 0 ≤ 4 * Real.exp 1 by positivity)) hnR.le
        have hphi := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (score_minor_radius_sq_le d U.card hdscore (Nat.cast_nonneg _)) hc) hnR.le
        convert add_le_add (add_le_add (le_refl (1 : ℝ)) hphi) hh using 1 <;> ring
      have hf := convolution_factorial_ratio_le n U.card hn hkN
      have hd := (principal_weight_pos T U).le
      calc
        _ ≤ (Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
            (1 + c * (d + (U.card : ℝ) + 1) ^ 2 / n)) * (principalWeightMatrix T U).det / meanPaths n := by
          exact div_le_div_of_nonneg_right
            ((mul_le_mul_of_nonneg_left (hper U hs) hd).trans_eq (by
              change (principalWeightMatrix T U).det * _ = _
              ring)) hm.le
        _ = (Q / 2 * (principalWeightMatrix T U).det) *
            (1 + c * (d + (U.card : ℝ) + 1) ^ 2 / n) *
              ((((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) / Z) := by rw [hmZ]; ring
        _ ≤ (Q / 2 * (principalWeightMatrix T U).det) *
            (1 + c * (d + (U.card : ℝ) + 1) ^ 2 / n) *
              (Real.exp (2 * (U.card : ℝ) ^ 2 / n) * (2 / (n : ℝ)) ^ U.card) :=
          mul_le_mul_of_nonneg_left hf (by positivity)
        _ = (Q / 2 * b U) * ((1 + c * (d + (U.card : ℝ) + 1) ^ 2 / n) *
            Real.exp (2 * (U.card : ℝ) ^ 2 / n)) := by dsimp [b]; ring
        _ ≤ (Q / 2 * b U) * (1 + ((c * (d + 1) ^ 2 + 4 * Real.exp 1) / n) * ((U.card : ℝ) + 2) ^ 2) :=
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


end TournamentHamiltonian
