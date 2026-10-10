import TournamentHamiltonian.LowerShortConvolution

namespace TournamentHamiltonian
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def principalErrorMomentConstant : ℝ :=
  8*((∑' k,subsetMoment 1 2 k)+(∑' k,subsetMoment 1 0 k))

theorem principalErrorMomentConstant_nonneg : 0≤principalErrorMomentConstant := by
  have h2 : 0≤∑' k,subsetMoment 1 2 k := tsum_nonneg (fun k=>subsetMoment_nonneg (by norm_num) 2 k)
  have h0 : 0≤∑' k,subsetMoment 1 0 k := tsum_nonneg (fun k=>subsetMoment_nonneg (by norm_num) 0 k)
  unfold principalErrorMomentConstant
  positivity

theorem shortPrincipalErrorMoment_le {n : ℕ} (T : Tournament n) (K : ℕ) (hn : 0<n) :
    shortPrincipalErrorMoment T K≤principalErrorMomentConstant := by
  have h2 := weighted_principal_powerMoment_le T hn 2 (fun _=>1) 1 (by norm_num) (fun _=>by norm_num) (fun _=>by norm_num)
  have h0 := weighted_principal_powerMoment_le T hn 0 (fun _=>1) 1 (by norm_num) (fun _=>by norm_num) (fun _=>by norm_num)
  simp only [Finset.prod_const_one,mul_one,pow_zero] at h2 h0
  have he (U : Finset (Fin n)) : ((U.card : ℝ)+2)^2≤8*((U.card : ℝ)^2+1) := by
    nlinarith [sq_nonneg ((U.card : ℝ)-1)]
  have hloc (U : Finset (Fin n)) :
      (if U.card<K then (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det*((U.card : ℝ)+2)^2 else 0)≤
        8*((2/(n : ℝ))^U.card*(principalWeightMatrix T U).det*(U.card : ℝ)^2+
          (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det) := by
    have hb : 0≤(2/(n : ℝ))^U.card*(principalWeightMatrix T U).det :=
      mul_nonneg (by positivity) (principal_weight_pos T U).le
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (he U) hb).trans_eq (by ring)
    · positivity
  calc
    _ ≤ ∑ U : Finset (Fin n),8*((2/(n : ℝ))^U.card*(principalWeightMatrix T U).det*(U.card : ℝ)^2+
        (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det) := Finset.sum_le_sum (fun U _=>hloc U)
    _ = 8*((∑ U : Finset (Fin n),(2/(n : ℝ))^U.card*(principalWeightMatrix T U).det*(U.card : ℝ)^2)+
        (∑ U : Finset (Fin n),(2/(n : ℝ))^U.card*(principalWeightMatrix T U).det)) := by rw [←Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h2 h0) (by norm_num)

theorem principal_card_mass_le {n : ℕ} (T : Tournament n) (k : ℕ) (hn : 0<n) :
    (∑ U∈(Finset.univ : Finset (Fin n)).powersetCard k,
      (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det)≤subsetWeight k := by
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hloc (U : Finset (Fin n)) (hU : U∈(Finset.univ : Finset (Fin n)).powersetCard k) :
      (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det≤
      (2/(n : ℝ))^k*(((k : ℝ)+1)/2)^((k : ℝ)/2) := by
    have hc := (Finset.mem_powersetCard.mp hU).2
    have hd := principal_weight_le_rpow T U
    rw [hc] at hd ⊢
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  calc
    _ ≤ ∑ _U∈(Finset.univ : Finset (Fin n)).powersetCard k,
        (2/(n : ℝ))^k*(((k : ℝ)+1)/2)^((k : ℝ)/2) := Finset.sum_le_sum (fun U hU=>hloc U hU)
    _ = (n.choose k : ℝ)*((2/(n : ℝ))^k*(((k : ℝ)+1)/2)^((k : ℝ)/2)) := by simp
    _ ≤ ((n : ℝ)^k/k.factorial)*((2/(n : ℝ))^k*(((k : ℝ)+1)/2)^((k : ℝ)/2)) :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div k n) (by positivity)
    _ = _ := by rw [subsetWeight_eq,div_pow]; field_simp

noncomputable def longPrincipalMass {n : ℕ} (T : Tournament n) (K : ℕ) : ℝ :=
  ∑ U : Finset (Fin n), if K≤U.card then (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det else 0

theorem short_add_long_principal_mass {n : ℕ} (T : Tournament n) (K : ℕ) :
    shortPrincipalMass T K+longPrincipalMass T K=
      ((1 : Matrix (Fin n) (Fin n) ℝ)+(2/(n : ℝ))•(1+adjacency T)).det := by
  rw [shortPrincipalMass,longPrincipalMass,←Finset.sum_add_distrib,principalWeight_generating_det]
  apply Finset.sum_congr rfl
  intro U _
  by_cases h : U.card<K
  · simp [h,show ¬K≤U.card by omega]
  · simp [h,show K≤U.card by omega]

theorem longPrincipalMass_le_subsetTail {n : ℕ} (T : Tournament n) (hn : 0<n) :
    longPrincipalMass T (subsetCutoff n)≤subsetTailAt 1 n := by
  unfold longPrincipalMass
  rw [sum_finsets_by_card]
  have hloc (k : ℕ) :
      (∑ U∈(Finset.univ : Finset (Fin n)).powersetCard k,
        if subsetCutoff n≤U.card then (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det else 0)≤
      if subsetCutoff n≤k then subsetWeight k else 0 := by
    by_cases hk : subsetCutoff n≤k
    · simp only [hk,ite_true]
      have he : (∑ U∈(Finset.univ : Finset (Fin n)).powersetCard k,
          if subsetCutoff n≤U.card then (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det else 0)=
          ∑ U∈(Finset.univ : Finset (Fin n)).powersetCard k,
            (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det := by
        apply Finset.sum_congr rfl
        intro U hU
        rw [(Finset.mem_powersetCard.mp hU).2]
        simp only [hk,ite_true]
      rw [he]
      exact principal_card_mass_le T k hn
    · simp only [hk,ite_false]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro U hU
      rw [(Finset.mem_powersetCard.mp hU).2]
      simp only [hk,ite_false]
  apply (Finset.sum_le_sum (fun k _=>hloc k)).trans
  simpa only [subsetTailAt,subsetCutoff,one_pow,one_mul] using finite_subsetWeight_tail_le n (subsetCutoff n)

theorem shortPrincipalMass_lower {n : ℕ} (T : Tournament n) (hn : 0<n) :
    ((1 : Matrix (Fin n) (Fin n) ℝ)+(2/(n : ℝ))•(1+adjacency T)).det-subsetTailAt 1 n≤
      shortPrincipalMass T (subsetCutoff n) := by
  have he := short_add_long_principal_mass T (subsetCutoff n)
  have ht := longPrincipalMass_le_subsetTail T hn
  linarith

theorem pathCount_normalized_lower_from_small_minors {n : ℕ} (T : Tournament n)
    (hn : 0<n) (Q c : ℝ) (hQ : 0≤Q) (hc : 0≤c)
    (hsmall : ∀ U : Finset (Fin n), U.card<subsetCutoff n → c*((U.card : ℝ)+2)^2/n≤1)
    (hper : ∀ U : Finset (Fin n), U.card<subsetCutoff n →
      Q*(((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card))*(1-c*((U.card : ℝ)+2)^2/n)≤
        ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n))→Fin n) Subtype.val).permanent) :
    Q/2*(((1 : Matrix (Fin n) (Fin n) ℝ)+(2/(n : ℝ))•(1+adjacency T)).det-
      subsetTailAt 1 n-c/n*principalErrorMomentConstant)≤(pathCount T : ℝ)/meanPaths n := by
  have hm : 0<meanPaths n := by unfold meanPaths; positivity
  have h1 := shortPrincipalMass_lower T hn
  have h2 := shortPrincipalErrorMoment_le T (subsetCutoff n) hn
  have hmid := sub_le_sub h1 (mul_le_mul_of_nonneg_left h2 (by positivity : 0≤c/(n : ℝ)))
  have h3 := shortConvolution_lower_from_minors T (subsetCutoff n) hn Q c hQ hsmall hper
  have h4 := div_le_div_of_nonneg_right (shortConvolution_le_pathCount T (subsetCutoff n)) hm.le
  exact (mul_le_mul_of_nonneg_left hmid (by positivity : 0≤Q/2)).trans (h3.trans h4)

end TournamentHamiltonian
