import TournamentHamiltonian.ExceptionalConvolution
import TournamentHamiltonian.PrincipalGenerating
import TournamentHamiltonian.GeneratingDeterminant

/-! Actual weighted principal-determinant sums, controlled by the proved Hadamard
subset moments. No linear bound on tournament principal determinants is assumed. -/
namespace TournamentHamiltonian
open scoped Classical

theorem prod_excess_le_card_power {α : Type*} [DecidableEq α] (U : Finset α)
    (w : α → ℝ) (W : ℝ) (hW : 1 ≤ W) (hw1 : ∀ x ∈ U, 1 ≤ w x)
    (hwW : ∀ x ∈ U, w x ≤ W) :
    (∏ x ∈ U, w x) - 1 ≤ W ^ U.card * ∑ x ∈ U, (w x - 1) := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert a U ha ih =>
    have ha1 := hw1 a (Finset.mem_insert_self _ _)
    have haW := hwW a (Finset.mem_insert_self _ _)
    have h1 : ∀ x ∈ U, 1 ≤ w x := fun x hx => hw1 x (Finset.mem_insert_of_mem hx)
    have h2 : ∀ x ∈ U, w x ≤ W := fun x hx => hwW x (Finset.mem_insert_of_mem hx)
    have hsum : 0 ≤ ∑ x ∈ U, (w x - 1) := Finset.sum_nonneg (fun x hx => by linarith [h1 x hx])
    have hmul := mul_le_mul_of_nonneg_left (ih h1 h2) (by linarith : 0 ≤ w a)
    have hmul2 := mul_le_mul_of_nonneg_right haW (by positivity : 0 ≤ W ^ U.card * ∑ x ∈ U, (w x - 1))
    have hp : 1 ≤ W ^ (U.card + 1) := one_le_pow₀ hW
    have hd := mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ w a - 1)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    nlinarith [pow_succ W U.card]

theorem powersetCard_sum_vertex_weights {n k : ℕ} (d : Fin n → ℝ) (hk : 0 < k) :
    (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ i ∈ U, d i) =
      ((n - 1).choose (k - 1) : ℝ) * ∑ i, d i := by
  have hi (U : Finset (Fin n)) : (∑ i ∈ U, d i) = ∑ i, if i ∈ U then d i else 0 := by simp
  simp_rw [hi]
  rw [Finset.sum_comm]
  have hc (i : Fin n) : (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun U => i ∈ U)).card =
      (n - 1).choose (k - 1) := by
    have h := Finset.card_filter_powersetCard_subset ({i} : Finset (Fin n)) Finset.univ k
      (Finset.subset_univ _) (by simpa using Nat.succ_le_of_lt hk)
    simpa only [Finset.singleton_subset_iff, Finset.card_singleton, Finset.card_univ,
      Fintype.card_fin] using h
  simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hc]
  rw [Finset.mul_sum]
  simp

theorem weighted_principal_card_excess_le {n : ℕ} (T : Tournament n) (k : ℕ) (hn : 0 < n)
    (w : Fin n → ℝ) (W : ℝ) (hW : 1 ≤ W) (hw1 : ∀ i, 1 ≤ w i) (hwW : ∀ i, w i ≤ W) :
    (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det * ((∏ i ∈ U, w i) - 1)) ≤
        ((∑ i, (w i - 1)) / n) * subsetMoment W 1 k := by
  by_cases hk : k = 0
  · subst k
    simp [subsetMoment]
  have hk0 : 0 < k := Nat.pos_of_ne_zero hk
  let H : ℝ := (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2)
  have hsum : 0 ≤ ∑ i, (w i - 1) := Finset.sum_nonneg (fun i _ => by linarith [hw1 i])
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hloc (U : Finset (Fin n)) (hU : U ∈ (Finset.univ : Finset (Fin n)).powersetCard k) :
      (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det * ((∏ i ∈ U, w i) - 1) ≤
        (2 / (n : ℝ)) ^ k * H * W ^ k * ∑ i ∈ U, (w i - 1) := by
    have hcard := (Finset.mem_powersetCard.mp hU).2
    have hd : (principalWeightMatrix T U).det ≤ H := by
      simpa only [hcard, H] using principal_weight_le_rpow T U
    have hp := prod_excess_le_card_power U w W hW (fun i _ => hw1 i) (fun i _ => hwW i)
    rw [hcard] at hp ⊢
    have hm := mul_le_mul (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ (2 / (n : ℝ)) ^ k))
      hp (by
        have hprod : 1 ≤ ∏ i ∈ U, w i := Finset.one_le_prod₀ (fun i _ => hw1 i)
        linarith) (by dsimp [H]; positivity)
    convert hm using 1
    ring
  calc
    _ ≤ ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (2 / (n : ℝ)) ^ k * H * W ^ k * ∑ i ∈ U, (w i - 1) := Finset.sum_le_sum hloc
    _ = (2 / (n : ℝ)) ^ k * H * W ^ k *
        (((n - 1).choose (k - 1) : ℝ) * ∑ i, (w i - 1)) := by
      rw [← Finset.mul_sum, powersetCard_sum_vertex_weights _ hk0]
    _ ≤ (2 / (n : ℝ)) ^ k * H * W ^ k *
        (((k : ℝ) / n * ((n : ℝ) ^ k / k.factorial)) * ∑ i, (w i - 1)) := by
      rw [choose_predecessor_normalization n k hn hk0]
      have hc : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k n
      apply mul_le_mul_of_nonneg_left _ (by dsimp [H]; positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) hsum
    _ = ((∑ i, (w i - 1)) / n) * subsetMoment W 1 k := by
      rw [subsetMoment, subsetWeight_eq, pow_one, div_pow]
      dsimp [H]
      field_simp

noncomputable def weightedPrincipalMoment (W : ℝ) : ℝ := ∑' k, subsetMoment W 1 k

theorem weightedPrincipalMoment_nonneg (W : ℝ) (hW : 0 ≤ W) : 0 ≤ weightedPrincipalMoment W :=
  tsum_nonneg (fun k => subsetMoment_nonneg hW 1 k)

noncomputable def weightedPrincipalMass {n : ℕ} (T : Tournament n) (w : Fin n → ℝ) : ℝ :=
  ∑ U : Finset (Fin n), (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det * ∏ i ∈ U, w i

theorem weightedPrincipalMass_le {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (w : Fin n → ℝ) (W : ℝ) (hW : 1 ≤ W) (hw1 : ∀ i, 1 ≤ w i) (hwW : ∀ i, w i ≤ W) :
    weightedPrincipalMass T w ≤
      ((1 : Matrix (Fin n) (Fin n) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T)).det +
        ((∑ i, (w i - 1)) / n) * weightedPrincipalMoment W := by
  have hexcess : weightedPrincipalMass T w -
      ((1 : Matrix (Fin n) (Fin n) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T)).det =
        ∑ U : Finset (Fin n), (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det *
          ((∏ i ∈ U, w i) - 1) := by
    rw [weightedPrincipalMass, principalWeight_generating_det, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro U _
    ring
  have hD : 0 ≤ (∑ i, (w i - 1)) / (n : ℝ) := by
    apply div_nonneg (Finset.sum_nonneg (fun i _ => by linarith [hw1 i])) (by positivity)
  have hs : Summable (subsetMoment W 1) := subsetMoment_summable (by linarith) 1
  have hfinite := hs.sum_le_tsum (Finset.range (n + 1)) (fun k _ => subsetMoment_nonneg (by linarith) 1 k)
  have hbound : weightedPrincipalMass T w -
      ((1 : Matrix (Fin n) (Fin n) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T)).det ≤
        ((∑ i, (w i - 1)) / n) * weightedPrincipalMoment W := by
    rw [hexcess, sum_finsets_by_card]
    calc
      _ ≤ ∑ k ∈ Finset.range (n + 1), ((∑ i, (w i - 1)) / n) * subsetMoment W 1 k :=
        Finset.sum_le_sum (fun k _ => weighted_principal_card_excess_le T k hn w W hW hw1 hwW)
      _ = ((∑ i, (w i - 1)) / n) * ∑ k ∈ Finset.range (n + 1), subsetMoment W 1 k := by
        rw [Finset.mul_sum]
      _ ≤ ((∑ i, (w i - 1)) / n) * weightedPrincipalMoment W :=
        mul_le_mul_of_nonneg_left hfinite hD
  linarith

theorem weightedPrincipalMass_le_kernel {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (w : Fin n → ℝ) (W : ℝ) (hW : 1 ≤ W) (hw1 : ∀ i, 1 ≤ w i) (hwW : ∀ i, w i ≤ W) :
    weightedPrincipalMass T w ≤
      2 * Real.exp 1 * ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det +
        ((∑ i, (w i - 1)) / n) * weightedPrincipalMoment W :=
  (weightedPrincipalMass_le T hn w W hW hw1 hwW).trans
    (add_le_add (tournament_generating_det_le T n hn le_rfl) (le_refl _))

theorem weighted_principal_powerMoment_le {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (r : ℕ) (w : Fin n → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw0 : ∀ i, 0 ≤ w i) (hwW : ∀ i, w i ≤ W) :
    (∑ U : Finset (Fin n), (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det *
      (U.card : ℝ) ^ r * ∏ i ∈ U, w i) ≤ ∑' k, subsetMoment W r k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hloc (k : ℕ) (U : Finset (Fin n)) (hU : U ∈ (Finset.univ : Finset (Fin n)).powersetCard k) :
      (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det * (U.card : ℝ) ^ r * ∏ i ∈ U, w i ≤
        (2 / (n : ℝ)) ^ k * (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2) * (k : ℝ) ^ r * W ^ k := by
    have hc := (Finset.mem_powersetCard.mp hU).2
    have hp : (∏ i ∈ U, w i) ≤ W ^ k := by
      have h := Finset.prod_le_prod₀ (s := U) (fun i _ => hw0 i) (fun i _ => hwW i)
      simpa only [Finset.prod_const, hc] using h
    have hd := principal_weight_le_rpow T U
    rw [hc] at hd ⊢
    apply mul_le_mul _ hp (Finset.prod_nonneg (fun i _ => hw0 i)) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) (by positivity)
  have hcard (k : ℕ) :
      (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det * (U.card : ℝ) ^ r * ∏ i ∈ U, w i) ≤
        subsetMoment W r k := by
    calc
      _ ≤ ∑ _U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          (2 / (n : ℝ)) ^ k * (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2) * (k : ℝ) ^ r * W ^ k :=
        Finset.sum_le_sum (fun U hU => hloc k U hU)
      _ = (n.choose k : ℝ) * ((2 / (n : ℝ)) ^ k * (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2) *
          (k : ℝ) ^ r * W ^ k) := by simp
      _ ≤ ((n : ℝ) ^ k / k.factorial) * ((2 / (n : ℝ)) ^ k *
          (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2) * (k : ℝ) ^ r * W ^ k) :=
        mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div k n) (by positivity)
      _ = subsetMoment W r k := by rw [subsetMoment, subsetWeight_eq, div_pow]; field_simp
  rw [sum_finsets_by_card]
  apply (Finset.sum_le_sum (fun k _ => hcard k)).trans
  exact (subsetMoment_summable hW r).sum_le_tsum _ (fun k _ => subsetMoment_nonneg hW r k)

end TournamentHamiltonian
