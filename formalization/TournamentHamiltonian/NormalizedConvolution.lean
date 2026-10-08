import TournamentHamiltonian.DegreeDeletion
import TournamentHamiltonian.PathConvolutionGenerating
import TournamentHamiltonian.LongTail

/-! Uniform normalization of the actual determinant--permanent convolution. -/

namespace TournamentHamiltonian

open scoped Classical
open Filter
open scoped Topology

noncomputable def convolutionTerm {n : ℕ} (T : Tournament n) (U : Finset (Fin n)) : ℝ :=
  (principalWeightMatrix T U).det *
    ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent

theorem convolutionTerm_nonneg {n : ℕ} (T : Tournament n) (U : Finset (Fin n)) :
    0 ≤ convolutionTerm T U :=
  mul_nonneg (principal_weight_pos T U).le (adjacency_principal_permanent_nonneg T Uᶜ)

theorem choose_factorial_normalization (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) * ((n - k).factorial : ℝ) / (2 : ℝ) ^ (n - k) =
      (n.factorial : ℝ) / (2 : ℝ) ^ n * (2 : ℝ) ^ k / (k.factorial : ℝ) := by
  have hf : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hp : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - k) * (2 : ℝ) ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rw [← hf, hp]
  field_simp

theorem convolutionTerm_le_stirling {n : ℕ} (T : Tournament n) (U : Finset (Fin n)) :
    convolutionTerm T U ≤ Real.exp 7 * Real.sqrt ((n : ℝ) + 1) *
      ((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card) *
        (((U.card : ℝ) + 1) / 2) ^ ((U.card : ℝ) / 2) := by
  have hp := adjacency_principal_permanent_le_stirling T Uᶜ
  have hcard : Uᶜ.card = n - U.card := by simpa using Finset.card_compl U
  have hsmall : (Uᶜ.card : ℝ) ≤ n := by exact_mod_cast (show Uᶜ.card ≤ n by simpa using Uᶜ.card_le_univ)
  have hs := Real.sqrt_le_sqrt (by linarith : (Uᶜ.card : ℝ) + 1 ≤ (n : ℝ) + 1)
  rw [hcard] at hs
  have hp' : ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * ((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card) := by
    apply hp.trans
    rw [hcard]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le) (by positivity))
      (by positivity)
  unfold convolutionTerm
  have hd := principal_weight_le_rpow T U
  have h := mul_le_mul hd hp' (adjacency_principal_permanent_nonneg T Uᶜ) (by positivity)
  simpa only [mul_comm] using h

theorem sum_convolution_card_le {n : ℕ} (T : Tournament n) (k : ℕ) (hk : k ≤ n) :
    (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k, convolutionTerm T U) ≤
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n * subsetWeight k := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)).powersetCard k)
    (fun U hU => convolutionTerm_le_stirling T U)
  have hs : (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * ((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card) *
        (((U.card : ℝ) + 1) / 2) ^ ((U.card : ℝ) / 2)) =
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n * subsetWeight k := by
    rw [Finset.sum_powersetCard k (Finset.univ : Finset (Fin n)) (fun j =>
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * ((n - j).factorial : ℝ) / (2 : ℝ) ^ (n - j) *
        (((j : ℝ) + 1) / 2) ^ ((j : ℝ) / 2))]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [subsetWeight_eq]
    have he := choose_factorial_normalization n k hk
    linear_combination (Real.exp 7 * Real.sqrt ((n : ℝ) + 1) *
      (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2)) * he
  exact h.trans_eq hs

theorem sum_finsets_by_card {n : ℕ} (f : Finset (Fin n) → ℝ) :
    (∑ U, f U) = ∑ k ∈ Finset.range (n + 1),
      ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k, f U := by
  rw [← Finset.powerset_univ, Finset.sum_powerset]
  simp

noncomputable def longConvolution {n : ℕ} (T : Tournament n) (N : ℕ) : ℝ :=
  ∑ U, if N ≤ U.card then convolutionTerm T U else 0

theorem longConvolution_nonneg {n : ℕ} (T : Tournament n) (N : ℕ) :
    0 ≤ longConvolution T N := by
  apply Finset.sum_nonneg
  intro U _
  split_ifs
  · exact convolutionTerm_nonneg T U
  · rfl

theorem longConvolution_le_card_tail {n : ℕ} (T : Tournament n) (N : ℕ) :
    longConvolution T N ≤
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n *
        ∑ k ∈ Finset.range (n + 1), if N ≤ k then subsetWeight k else 0 := by
  unfold longConvolution
  rw [sum_finsets_by_card, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  have he : (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      if N ≤ U.card then convolutionTerm T U else 0) =
      if N ≤ k then (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k, convolutionTerm T U) else 0 := by
    by_cases hN : N ≤ k
    · rw [ite_eq_left hN]
      apply Finset.sum_congr rfl
      intro U hU
      rw [(Finset.mem_powersetCard.mp hU).2, ite_eq_left hN]
    · rw [ite_eq_right hN]
      apply Finset.sum_eq_zero
      intro U hU
      rw [(Finset.mem_powersetCard.mp hU).2, ite_eq_right hN]
  rw [he]
  split_ifs
  · exact sum_convolution_card_le T k hkn
  · simp

theorem finite_subsetWeight_tail_le (n N : ℕ) :
    (∑ k ∈ Finset.range (n + 1), if N ≤ k then subsetWeight k else 0) ≤
      ∑' m, subsetWeight (N + m) := by
  rw [← Finset.sum_filter]
  have he : (Finset.range (n + 1)).filter (fun k => N ≤ k) = Finset.Ico N (n + 1) := by
    ext k
    simp
    omega
  rw [he, Finset.sum_Ico_eq_sum_range]
  have hs : Summable (fun m => subsetWeight m) := by
    have h := subsetMoment_summable (by norm_num : (0 : ℝ) ≤ 1) 0
    convert h using 1
    funext m
    simp [subsetMoment]
  have hs' : Summable (fun m => subsetWeight (N + m)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).mpr hs
  exact hs'.sum_le_tsum _ (fun _ _ => subsetWeight_nonneg _)

theorem longConvolution_le_subsetTail {n : ℕ} (T : Tournament n) :
    longConvolution T (subsetCutoff n) ≤
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n *
        subsetTailAt 1 n := by
  have h := longConvolution_le_card_tail T (subsetCutoff n)
  have ht := finite_subsetWeight_tail_le n (subsetCutoff n)
  have he : (∑' m, subsetWeight (subsetCutoff n + m)) = subsetTailAt 1 n := by
    simp [subsetTailAt, subsetCutoff]
  rw [he] at ht
  exact h.trans (mul_le_mul_of_nonneg_left ht (by positivity))

theorem meanPaths_eq_twice_normalization (n : ℕ) (hn : 1 ≤ n) :
    meanPaths n = 2 * (n.factorial : ℝ) / (2 : ℝ) ^ n := by
  have hp : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [meanPaths, hp]
  field_simp

theorem longConvolution_normalized_le {n : ℕ} (T : Tournament n) (hn : 1 ≤ n) :
    longConvolution T (subsetCutoff n) / meanPaths n ≤
      (Real.exp 7 / 2) * Real.sqrt ((n : ℝ) + 1) * subsetTailAt 1 n := by
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  apply (div_le_iff₀ hm).mpr
  rw [meanPaths_eq_twice_normalization n hn]
  have h := longConvolution_le_subsetTail T
  convert h using 1
  ring

/-- One threshold works for every actual tournament. The full long-subset
contribution is uniformly o(1/n) after normalization by the manuscript mean. -/
theorem longConvolution_eventually_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      longConvolution T (subsetCutoff n) / meanPaths n ≤ ε / n := by
  have h := scaled_subsetTail_eventually_small (by norm_num : (0 : ℝ) < 1) (Real.exp 7) hε
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hn1 T
  exact (longConvolution_normalized_le T hn1).trans hn

theorem convolutionTerm_le_of_permanent_bound {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) (q : ℝ) (hq : 0 ≤ q)
    (hper : ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
      Real.exp 7 * Real.sqrt ((Uᶜ.card : ℝ) + 1) * (Uᶜ.card.factorial : ℝ) / (2 : ℝ) ^ Uᶜ.card * q) :
    convolutionTerm T U ≤ Real.exp 7 * Real.sqrt ((n : ℝ) + 1) *
      ((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card) *
        (((U.card : ℝ) + 1) / 2) ^ ((U.card : ℝ) / 2) * q := by
  have hcard : Uᶜ.card = n - U.card := by simpa using Finset.card_compl U
  have hm : (Uᶜ.card : ℝ) ≤ n := by exact_mod_cast (show Uᶜ.card ≤ n by simpa using Uᶜ.card_le_univ)
  have hs := Real.sqrt_le_sqrt (by linarith : (Uᶜ.card : ℝ) + 1 ≤ (n : ℝ) + 1)
  have hbound : Real.exp 7 * Real.sqrt ((Uᶜ.card : ℝ) + 1) * (Uᶜ.card.factorial : ℝ) / (2 : ℝ) ^ Uᶜ.card * q ≤
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * ((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card) * q := by
    rw [← hcard]
    apply mul_le_mul_of_nonneg_right _ hq
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le) (by positivity))
      (by positivity)
  have h := mul_le_mul (principal_weight_le_rpow T U) (hper.trans hbound)
    (adjacency_principal_permanent_nonneg T Uᶜ) (by positivity)
  unfold convolutionTerm
  convert h using 1
  ring

theorem sum_convolution_card_le_of_permanent_bound {n : ℕ} (T : Tournament n)
    (k : ℕ) (hk : k ≤ n) (q : ℝ) (hq : 0 ≤ q)
    (hper : ∀ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        Real.exp 7 * Real.sqrt ((Uᶜ.card : ℝ) + 1) * (Uᶜ.card.factorial : ℝ) / (2 : ℝ) ^ Uᶜ.card * q) :
    (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k, convolutionTerm T U) ≤
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n * subsetWeight k * q := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)).powersetCard k)
    (fun U hU => convolutionTerm_le_of_permanent_bound T U q hq (hper U hU))
  have he : (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * ((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card) *
        (((U.card : ℝ) + 1) / 2) ^ ((U.card : ℝ) / 2) * q) =
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n * subsetWeight k * q := by
    rw [Finset.sum_powersetCard k (Finset.univ : Finset (Fin n)) (fun j =>
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * ((n - j).factorial : ℝ) / (2 : ℝ) ^ (n - j) *
        (((j : ℝ) + 1) / 2) ^ ((j : ℝ) / 2) * q)]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [subsetWeight_eq]
    linear_combination (Real.exp 7 * Real.sqrt ((n : ℝ) + 1) *
      (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2) * q) * choose_factorial_normalization n k hk
  exact h.trans_eq he

end TournamentHamiltonian
