import TournamentHamiltonian.HomogeneousGeometricBound

open scoped BigOperators MatrixOrder ComplexOrder

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem inverse_geometric_le_exp (x q : ℝ) (hx : 0 ≤ x) (hxq : x ≤ q) (hq : q < 1) :
    (1 - x)⁻¹ ≤ Real.exp (x / (1 - q)) := by
  have hpos : 0 < 1 - x := by linarith
  have hqpos : 0 < 1 - q := by linarith
  rw [← Real.exp_log (inv_pos.mpr hpos)]
  apply Real.exp_le_exp.mpr
  calc
    Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    _ = x / (1 - x) := by field_simp; ring
    _ ≤ x / (1 - q) := div_le_div_of_nonneg_left hx hqpos (by linarith)

theorem geometric_product_le_exp (d : ι → ℝ) (q : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hdq : ∀ i, d i ≤ q) (hq : q < 1) :
    (∏ i, (1 - d i)⁻¹) ≤ Real.exp ((∑ i, d i) / (1 - q)) := by
  calc
    _ ≤ ∏ i, Real.exp (d i / (1 - q)) := Finset.prod_le_prod₀
      (fun i _ => inv_nonneg.mpr (by linarith [hdq i]))
      (fun i _ => inverse_geometric_le_exp _ _ (hd i) (hdq i) hq)
    _ = _ := by rw [← Real.exp_sum, Finset.sum_div]

theorem geometric_product_le_exp_sqrt (d : ι → ℝ) (q C : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hdq : ∀ i, d i ≤ q) (hq : q < 1)
    (hC : 0 ≤ C) (hL2 : ∑ i, (d i) ^ 2 ≤ C ^ 2) :
    (∏ i, (1 - d i)⁻¹) ≤
      Real.exp (C * Real.sqrt (Fintype.card ι) / (1 - q)) := by
  have hsum : (∑ i, d i) ≤ C * Real.sqrt (Fintype.card ι) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : ι => (1 : ℝ)) d
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    have hs : Real.sqrt (∑ i, d i ^ 2) ≤ C := by
      rw [← Real.sqrt_sq hC]
      exact Real.sqrt_le_sqrt hL2
    exact h.trans (by nlinarith [Real.sqrt_nonneg (Fintype.card ι)])
  exact (geometric_product_le_exp d q hd hdq hq).trans
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hsum (by linarith)))

theorem complex_posSemidef_permanent_le_exponential (H : Matrix ι ι ℂ)
    (hH : H.PosSemidef) (i₀ : ι) (h₀ : hH.isHermitian.eigenvalues i₀ = 1)
    (q C : ℝ) (hq : q < 1) (hC : 0 ≤ C)
    (hgap : ∀ i, i ≠ i₀ → hH.isHermitian.eigenvalues i ≤ q)
    (hL2 : ∑ i : {i : ι // i ≠ i₀}, (hH.isHermitian.eigenvalues i.val) ^ 2 ≤ C ^ 2) :
    H.permanent.re ≤ (Fintype.card ι).factorial /
      (Fintype.card ι : ℝ) ^ Fintype.card ι *
        Real.exp (C * Real.sqrt (Fintype.card {i : ι // i ≠ i₀}) / (1 - q)) := by
  exact (complex_posSemidef_permanent_le_geometric H hH i₀ h₀
    (fun i hi => (hgap i hi).trans_lt hq)).trans
      (mul_le_mul_of_nonneg_left
        (geometric_product_le_exp_sqrt _ q C (fun i => hH.eigenvalues_nonneg i.val)
          (fun i => hgap i.val i.property) hq hC hL2) (by positivity))

end TournamentHamiltonian
