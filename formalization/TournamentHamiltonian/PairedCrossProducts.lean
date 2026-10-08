import TournamentHamiltonian.CrossPermanentBounds

/-! Paired suppression factors and weighted cross-neighbor estimates. -/

namespace TournamentHamiltonian

open scoped Classical

variable {α : Type*} [DecidableEq α]

theorem retained_cross_product_le (F R C : Finset α) (hR : R ⊆ F) (hC : C ⊆ F)
    (u v : α → ℝ) (c L : ℝ) (hc : 0 < c) (_hL : 0 ≤ L) (hcL : c ≤ L ^ 2)
    (hu0 : ∀ x ∈ F, 0 ≤ u x) (hv0 : ∀ x ∈ F, 0 ≤ v x)
    (huL : ∀ x ∈ F, u x ≤ L) (hvL : ∀ x ∈ F, v x ≤ L)
    (huv : ∀ x ∈ F, u x * v x ≤ c) :
    (∏ x ∈ F \ R, u x) * (∏ x ∈ F \ C, v x) ≤
      c ^ F.card * (L / c) ^ (R.card + C.card) := by
  have hpoint (x : α) (hx : x ∈ F) :
      (if x ∈ R then 1 else u x) * (if x ∈ C then 1 else v x) ≤
        c * (L / c) ^ (if x ∈ R then 1 else 0) * (L / c) ^ (if x ∈ C then 1 else 0) := by
    by_cases hxr : x ∈ R <;> by_cases hxc : x ∈ C <;> simp only [hxr, hxc,
      ite_true, ite_false, pow_zero, pow_one, mul_one, one_mul]
    · have hh : 1 ≤ L ^ 2 / c := (le_div_iff₀ hc).mpr (by simpa using hcL)
      calc
        _ ≤ L ^ 2 / c := hh
        _ = _ := by field_simp
    · rw [mul_div_cancel₀ L hc.ne']
      exact hvL x hx
    · rw [mul_div_cancel₀ L hc.ne']
      exact huL x hx
    · exact huv x hx
  have h := Finset.prod_le_prod₀ (s := F)
    (fun x hx => mul_nonneg (by split_ifs <;> first | positivity | exact hu0 x hx)
      (by split_ifs <;> first | positivity | exact hv0 x hx)) hpoint
  have hu : (∏ x ∈ F, if x ∈ R then (1 : ℝ) else u x) = ∏ x ∈ F \ R, u x := by
    simp [Finset.prod_ite, Finset.sdiff_eq_filter]
  have hv : (∏ x ∈ F, if x ∈ C then (1 : ℝ) else v x) = ∏ x ∈ F \ C, v x := by
    simp [Finset.prod_ite, Finset.sdiff_eq_filter]
  have hpR : (∏ x ∈ F, (L / c) ^ (if x ∈ R then 1 else 0)) = (L / c) ^ R.card := by
    simp [Finset.inter_eq_right.mpr hR, div_pow]
  have hpC : (∏ x ∈ F, (L / c) ^ (if x ∈ C then 1 else 0)) = (L / c) ^ C.card := by
    simp [Finset.inter_eq_right.mpr hC, div_pow]
  rw [Finset.prod_mul_distrib, hu, hv] at h
  simp only [Finset.prod_mul_distrib, Finset.prod_const, hpR, hpC] at h
  convert h using 1
  rw [pow_add]
  ring

theorem cross_pair_bounds (q eps beta : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (heps : 0 ≤ eps) (hb : 0 ≤ beta) (hq : q ≤ 1 / 20 + eps ∨ 19 / 20 - eps ≤ q) :
    0 ≤ 2 * (q + beta) ∧ 0 ≤ 2 * (1 - q + beta) ∧
      2 * (q + beta) ≤ 2 + 2 * beta ∧ 2 * (1 - q + beta) ≤ 2 + 2 * beta ∧
      (2 * (q + beta)) * (2 * (1 - q + beta)) ≤ 19 / 100 + 4 * eps + 4 * beta + 4 * beta ^ 2 := by
  have hprod : q * (1 - q) ≤ 19 / 400 + eps := by
    rcases hq with hq | hq
    · nlinarith [sq_nonneg (q - 1 / 20)]
    · nlinarith [sq_nonneg (q - 19 / 20)]
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

omit [DecidableEq α] in
theorem weighted_neighbor_sum_le (F : Finset α) (a w : α → ℝ) (beta : ℝ)
    (ha0 : ∀ x ∈ F, 0 ≤ a x) (ha1 : ∀ x ∈ F, a x ≤ 1)
    (hdisp : (∑ x ∈ F, |w x - 1|) ≤ F.card * beta) :
    (∑ x ∈ F, a x * w x) ≤ (∑ x ∈ F, a x) + F.card * beta := by
  have hlocal (x : α) (hx : x ∈ F) : a x * w x ≤ a x + |w x - 1| := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self (w x - 1)) (ha0 x hx)
    have h2 := mul_le_mul_of_nonneg_right (ha1 x hx) (abs_nonneg (w x - 1))
    nlinarith
  have h := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib] at h
  linarith

end TournamentHamiltonian
