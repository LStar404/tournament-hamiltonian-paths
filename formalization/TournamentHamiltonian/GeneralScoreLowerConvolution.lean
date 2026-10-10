import TournamentHamiltonian.SmallScorePathsLower

namespace TournamentHamiltonian
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem shortConvolution_lower_from_signed_minors {n : ℕ} (T : Tournament n) (K : ℕ)
    (hn : 0<n) (Q c : ℝ) (hQ : 0≤Q)
    (hper : ∀ U : Finset (Fin n), U.card<K →
      Q*(((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card))*(1-c*((U.card : ℝ)+2)^2/n)≤
        ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n))→Fin n) Subtype.val).permanent) :
    Q/2*(shortPrincipalMass T K-c/n*shortPrincipalErrorMoment T K)≤shortConvolution T K/meanPaths n := by
  let Z : ℝ := (n.factorial : ℝ)/(2 : ℝ)^n
  have hZ : 0<Z := by dsimp [Z]; positivity
  have hm : 0<meanPaths n := by unfold meanPaths; positivity
  have hmZ : meanPaths n=2*Z := by
    dsimp [Z]
    simpa only [mul_div_assoc] using meanPaths_eq_twice_normalization n (by omega)
  have hloc (U : Finset (Fin n)) :
      (if U.card<K then Q/2*((2/(n : ℝ))^U.card*(principalWeightMatrix T U).det)*
        (1-c*((U.card : ℝ)+2)^2/n) else 0)≤
      (if U.card<K then convolutionTerm T U else 0)/meanPaths n := by
    by_cases hs : U.card<K
    · simp only [hs,ite_true]
      have hk : U.card≤n := by simpa using U.card_le_univ
      have hd := (principal_weight_pos T U).le
      by_cases hr : 0≤1-c*((U.card : ℝ)+2)^2/n
      · have hfac := convolution_factorial_ratio_ge n U.card hn hk
        have hlow := mul_le_mul_of_nonneg_left hfac
          (show 0≤Q/2*(principalWeightMatrix T U).det*(1-c*((U.card : ℝ)+2)^2/n) by positivity)
        calc
          _ = (Q/2*(principalWeightMatrix T U).det*(1-c*((U.card : ℝ)+2)^2/n))*(2/(n : ℝ))^U.card := by ring
          _ ≤ (Q/2*(principalWeightMatrix T U).det*(1-c*((U.card : ℝ)+2)^2/n))*
              ((((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card))/Z) := hlow
          _ = (principalWeightMatrix T U).det*
              (Q*(((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card))*(1-c*((U.card : ℝ)+2)^2/n))/meanPaths n := by rw [hmZ]; ring
          _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hper U hs) hd) hm.le
      · have hneg : 1-c*((U.card : ℝ)+2)^2/n≤0 := le_of_lt (lt_of_not_ge hr)
        have hb : 0≤Q/2*((2/(n : ℝ))^U.card*(principalWeightMatrix T U).det) := by positivity
        exact (mul_nonpos_of_nonneg_of_nonpos hb hneg).trans (div_nonneg (convolutionTerm_nonneg T U) hm.le)
    · simp [hs]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun U _ => hloc U)
  rw [←Finset.sum_div] at hsum
  change _≤shortConvolution T K/meanPaths n at hsum
  apply le_trans _ hsum
  apply le_of_eq
  rw [shortPrincipalMass,shortPrincipalErrorMoment,Finset.mul_sum,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  split_ifs <;>ring

theorem pathCount_normalized_lower_from_signed_minors {n : ℕ} (T : Tournament n)
    (hn : 0<n) (Q c : ℝ) (hQ : 0≤Q) (hc : 0≤c)
    (hper : ∀ U : Finset (Fin n), U.card<subsetCutoff n →
      Q*(((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card))*(1-c*((U.card : ℝ)+2)^2/n)≤
        ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n))→Fin n) Subtype.val).permanent) :
    Q/2*(((1 : Matrix (Fin n) (Fin n) ℝ)+(2/(n : ℝ))•(1+adjacency T)).det-
      subsetTailAt 1 n-c/n*principalErrorMomentConstant)≤(pathCount T : ℝ)/meanPaths n := by
  have hm : 0<meanPaths n := by unfold meanPaths; positivity
  have h1 := shortPrincipalMass_lower T hn
  have h2 := shortPrincipalErrorMoment_le T (subsetCutoff n) hn
  have hmid := sub_le_sub h1 (mul_le_mul_of_nonneg_left h2 (by positivity : 0≤c/(n : ℝ)))
  have h3 := shortConvolution_lower_from_signed_minors T (subsetCutoff n) hn Q c hQ hper
  have h4 := div_le_div_of_nonneg_right (shortConvolution_le_pathCount T (subsetCutoff n)) hm.le
  exact (mul_le_mul_of_nonneg_left hmid (by positivity : 0≤Q/2)).trans (h3.trans h4)

theorem pathCount_spectral_lower_from_signed_minors {n : ℕ} (T : Tournament n)
    (hn : 0<n) (c Cg : ℝ) (hc : 0≤c) (hCg : 0≤Cg)
    (hgen : 2*Real.exp 1*((1 : Matrix (Fin n) (Fin n) ℝ)+(1/(n : ℝ))•signMatrix T).det-Cg/n≤
      ((1 : Matrix (Fin n) (Fin n) ℝ)+(2/(n : ℝ))•(1+adjacency T)).det)
    (hper : ∀ U : Finset (Fin n), U.card<subsetCutoff n →
      pathLowerPermanentFactor T*(((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card))*(1-c*((U.card : ℝ)+2)^2/n)≤
        ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n))→Fin n) Subtype.val).permanent) :
    spectralRatio T-((Cg+c*principalErrorMomentConstant)/n+subsetTailAt 1 n)≤
      (pathCount T : ℝ)/meanPaths n := by
  obtain ⟨hQ0,hQ1⟩ := pathLowerPermanentFactor_bounds T hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have htail : 0≤subsetTailAt 1 n := by
    unfold subsetTailAt
    exact tsum_nonneg (fun k=>mul_nonneg (by positivity) (subsetWeight_nonneg _))
  have hE : 0≤(Cg+c*principalErrorMomentConstant)/n+subsetTailAt 1 n := by
    have hM := principalErrorMomentConstant_nonneg
    positivity
  have hbase := pathCount_normalized_lower_from_signed_minors T hn
    (pathLowerPermanentFactor T) c hQ0 hc hper
  have h1 := sub_le_sub_right (sub_le_sub_right hgen (subsetTailAt 1 n))
    (c/n*principalErrorMomentConstant)
  have h2 := (mul_le_mul_of_nonneg_left h1 (by positivity : 0≤pathLowerPermanentFactor T/2)).trans hbase
  have he : Real.exp (-1)*Real.exp 1=1 := by rw [←Real.exp_add]; norm_num
  have hEq : pathLowerPermanentFactor T/2*(2*Real.exp 1*
      ((1 : Matrix (Fin n) (Fin n) ℝ)+(1/(n : ℝ))•signMatrix T).det-Cg/n-
        subsetTailAt 1 n-c/n*principalErrorMomentConstant)=
      spectralRatio T-(pathLowerPermanentFactor T/2)*((Cg+c*principalErrorMomentConstant)/n+subsetTailAt 1 n) := by
    unfold pathLowerPermanentFactor spectralRatio
    calc
      _ = (Real.exp (-1)*Real.exp 1)*gaussianFactor T*
          ((1 : Matrix (Fin n) (Fin n) ℝ)+(1/(n : ℝ))•signMatrix T).det-
            (Real.exp (-1)*gaussianFactor T/2)*((Cg+c*principalErrorMomentConstant)/n+subsetTailAt 1 n) := by ring
      _ = _ := by rw [he]; ring
  rw [hEq] at h2
  have h3 := mul_le_mul_of_nonneg_right hQ1 hE
  simp only [one_mul] at h3
  linarith


end TournamentHamiltonian
