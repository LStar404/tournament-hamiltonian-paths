import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
The finite spectral packing argument in manuscript §2.3.
The input is an arbitrary finite list of squared frequencies, not a list
assumed to be realizable by a tournament. The matrix spectral cap and the
asymptotic permanent/path arguments are separate obligations.
-/

namespace TournamentHamiltonian

/-- The contribution of a paired skew frequency to the spectral ratio. -/
noncomputable def ratio (x : ℝ) : ℝ := (1 + x) / (1 - x)

lemma ratio_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) : 0 ≤ ratio x := by
  unfold ratio
  positivity

lemma ratio_mono {x y : ℝ} (hxy : x ≤ y) (hy : y < 1) : ratio x ≤ ratio y := by
  have hx : x < 1 := lt_of_le_of_lt hxy hy
  unfold ratio
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

/-- Combining two nonnegative frequencies whose sum is below one increases
the ratio. This is an algebraic version of the convex mass transfer step. -/
lemma ratio_merge {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y < 1) :
    ratio x * ratio y ≤ ratio (x + y) := by
  have hx1 : 0 < 1 - x := by linarith
  have hy1 : 0 < 1 - y := by linarith
  have hs : 0 < 1 - (x + y) := by linarith
  unfold ratio
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos hx1 hy1) hs).2
  nlinarith [mul_nonneg hx hy, mul_nonneg (mul_nonneg hx hy) (by linarith : 0 ≤ x + y)]

/-- If two frequencies exceed one cap in total, transferring mass to that
cap and the remainder increases the ratio. -/
lemma ratio_transfer {x y a : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxa : x ≤ a) (hya : y ≤ a) (ha : a < 1)
    (_hs : a ≤ x + y) (_hsmall : x + y < 1) :
    ratio x * ratio y ≤ ratio a * ratio (x + y - a) := by
  have hx1 : 0 < 1 - x := by linarith
  have hy1 : 0 < 1 - y := by linarith
  have ha1 : 0 < 1 - a := by linarith
  have hr1 : 0 < 1 - (x + y - a) := by linarith
  have hd : 0 ≤ (a - x) * (a - y) := mul_nonneg (by linarith) (by linarith)
  have hprod : a * (x + y - a) ≤ x * y := by nlinarith
  have hs0 : 0 ≤ x + y := by linarith
  unfold ratio
  rw [div_mul_div_comm, div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos hx1 hy1) (mul_pos ha1 hr1)).2
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hprod)]

/-- The packed upper bound at total mass `t`, with individual cap `a`. -/
noncomputable def packed (a t : ℝ) : ℝ :=
  if t ≤ a then ratio t else ratio a * ratio (t - a)

lemma ratio_product_nonneg (xs : List ℝ) (h0 : ∀ x ∈ xs, 0 ≤ x)
    (h1 : ∀ x ∈ xs, x < 1) : 0 ≤ (xs.map ratio).prod := by
  apply List.prod_nonneg
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact ratio_nonneg (h0 y hy) (h1 y hy)

/-- Full finite packing, including the empty list, zero frequencies, and
total mass strictly below the relaxed maximum. -/
theorem spectral_packing_at_mass (xs : List ℝ) (a : ℝ)
    (ha0 : (1 : ℝ) / 4 ≤ a) (ha1 : a < 1 / 2)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ a) (hs : xs.sum ≤ 1 / 2) :
    (xs.map ratio).prod ≤ packed a xs.sum := by
  induction xs with
  | nil => simp [packed, ratio, show (0 : ℝ) ≤ a by linarith]
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have htail : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ a := by
      intro y hy
      exact hxs y (by simp [hy])
    have ht0 : 0 ≤ xs.sum := List.sum_nonneg (fun y hy => (htail y hy).1)
    have ht : xs.sum ≤ 1 / 2 := by simp only [List.sum_cons] at hs; linarith
    have hi := ih htail ht
    have htotal : x + xs.sum ≤ 1 / 2 := by simpa using hs
    have hrx : 0 ≤ ratio x := ratio_nonneg hx.1 (by linarith)
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    calc
      ratio x * (xs.map ratio).prod ≤ ratio x * packed a xs.sum :=
        mul_le_mul_of_nonneg_left hi hrx
      _ ≤ packed a (x + xs.sum) := by
        by_cases hta : xs.sum ≤ a
        · rw [packed, ite_eq_left hta]
          by_cases hxa : x + xs.sum ≤ a
          · rw [packed, ite_eq_left hxa]
            exact ratio_merge hx.1 ht0 (by linarith)
          · rw [packed, ite_eq_right hxa]
            exact ratio_transfer hx.1 ht0 hx.2 hta (by linarith)
              (by linarith) (by linarith)
        · have hsum : ¬x + xs.sum ≤ a := by linarith
          rw [packed, ite_eq_right hta, packed, ite_eq_right hsum]
          have hr := ratio_merge hx.1 (by linarith : 0 ≤ xs.sum - a)
            (by linarith : x + (xs.sum - a) < 1)
          have hra : 0 ≤ ratio a := ratio_nonneg (by linarith) (by linarith)
          calc
            ratio x * (ratio a * ratio (xs.sum - a)) =
                ratio a * (ratio x * ratio (xs.sum - a)) := by ring
            _ ≤ ratio a * ratio (x + (xs.sum - a)) :=
              mul_le_mul_of_nonneg_left hr hra
            _ = ratio a * ratio (x + xs.sum - a) := by congr 2; ring

/-- The two-coordinate relaxation used in the paper, with no assumption
that the maximizing packed vector is a tournament spectrum. -/
theorem spectral_packing (xs : List ℝ) (a : ℝ)
    (ha0 : (1 : ℝ) / 4 ≤ a) (ha1 : a < 1 / 2)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ a) (hs : xs.sum ≤ 1 / 2) :
    (xs.map ratio).prod ≤ ratio a * ratio (1 / 2 - a) := by
  have ht0 : 0 ≤ xs.sum := List.sum_nonneg (fun x hx => (hxs x hx).1)
  apply le_trans (spectral_packing_at_mass xs a ha0 ha1 hxs hs)
  unfold packed
  split_ifs with h
  · have hra := ratio_mono h (by linarith : a < 1)
    have hr : 1 ≤ ratio (1 / 2 - a) := by
      simpa [ratio] using (ratio_mono (by linarith : (0 : ℝ) ≤ 1 / 2 - a)
        (by linarith : 1 / 2 - a < 1))
    have ha := ratio_nonneg (by linarith : 0 ≤ a) (by linarith : a < 1)
    exact le_trans hra (by nlinarith)
  · exact mul_le_mul_of_nonneg_left
      (ratio_mono (by linarith : xs.sum - a ≤ 1 / 2 - a) (by linarith))
      (ratio_nonneg (by linarith) (by linarith))

/-- The squared singular-value cap used in the manuscript. -/
noncomputable def spectralCap : ℝ := 4 / Real.pi ^ 2

/-- The published upper constant, in its expanded rational form. -/
noncomputable def upperConstant : ℝ :=
  (3 * Real.pi ^ 4 + 4 * Real.pi ^ 2 - 32) /
    (Real.pi ^ 4 + 4 * Real.pi ^ 2 - 32)

lemma spectralCap_bounds : (1 : ℝ) / 4 ≤ spectralCap ∧ spectralCap < 1 / 2 := by
  have hp0 := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hp4 := Real.pi_lt_four
  have hp2 : 0 < Real.pi ^ 2 := sq_pos_of_pos hp0
  unfold spectralCap
  constructor
  · apply (le_div_iff₀ hp2).2
    nlinarith
  · apply (div_lt_iff₀ hp2).2
    nlinarith

lemma upperConstant_eq_packed :
    upperConstant = ratio spectralCap * ratio (1 / 2 - spectralCap) := by
  have hb := spectralCap_bounds
  have hp2 : Real.pi ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos Real.pi_pos)
  have hden : Real.pi ^ 4 + 4 * Real.pi ^ 2 - 32 ≠ 0 := by
    have hp3 := Real.pi_gt_three
    have hsq : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_pos]
    have hfour : 81 < Real.pi ^ 4 := by nlinarith [sq_nonneg (Real.pi ^ 2 - 9)]
    nlinarith
  unfold upperConstant ratio spectralCap
  field_simp
  ring

/-- Conditional on the cap and total paired mass, the spectral ratio has
the exact upper constant stated in the paper. No asymptotics are assumed. -/
theorem spectral_product_le_upperConstant (xs : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ spectralCap) (hs : xs.sum ≤ 1 / 2) :
    (xs.map ratio).prod ≤ upperConstant := by
  rw [upperConstant_eq_packed]
  exact spectral_packing xs spectralCap spectralCap_bounds.1 spectralCap_bounds.2 hxs hs

lemma upperConstant_den_pos : 0 < Real.pi ^ 4 + 4 * Real.pi ^ 2 - 32 := by
  have hp3 := Real.pi_gt_three
  have hsq : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_pos]
  have hfour : 81 < Real.pi ^ 4 := by nlinarith [sq_nonneg (Real.pi ^ 2 - 9)]
  nlinarith

theorem upperConstant_bounds : 1 < upperConstant ∧ upperConstant < 3 := by
  have hp3 := Real.pi_gt_three
  have hsq : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_pos]
  have hfour : 0 < Real.pi ^ 4 := pow_pos Real.pi_pos 4
  unfold upperConstant
  constructor
  · apply (lt_div_iff₀ upperConstant_den_pos).2
    nlinarith
  · apply (div_lt_iff₀ upperConstant_den_pos).2
    nlinarith

end TournamentHamiltonian
