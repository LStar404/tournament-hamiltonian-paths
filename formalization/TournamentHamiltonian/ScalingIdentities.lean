import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Exact permanent scaling identities underlying §§4.1 and 4.4. These
identities do not assert existence of balancing potentials or an asymptotic
approximation. Those are separate analytic proof obligations. -/

namespace TournamentHamiltonian

theorem permanent_row_column_scaling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (r c : ι → ℝ) :
    Matrix.permanent (fun i j => r i * A i j * c j) =
      (∏ i, r i) * (∏ j, c j) * A.permanent := by
  have hp (σ : Equiv.Perm ι) : (∏ i, r (σ i)) = ∏ i, r i := by
    apply Fintype.prod_equiv σ
    intro i
    rfl
  unfold Matrix.permanent
  simp_rw [Finset.prod_mul_distrib, hp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem permanent_exp_scaling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    Matrix.permanent (fun i j => Real.exp (x i) * A i j * Real.exp (y j)) =
      Real.exp ((∑ i, x i) + ∑ j, y j) * A.permanent := by
  rw [permanent_row_column_scaling, Real.exp_add, Real.exp_sum, Real.exp_sum]

/-- Restore the original permanent after any finite exponential scaling,
without requiring positivity or equal row/column deletion sets. -/
theorem permanent_exp_restoration {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    A.permanent = Real.exp (-((∑ i, x i) + ∑ j, y j)) *
      Matrix.permanent (fun i j => Real.exp (x i) * A i j * Real.exp (y j)) := by
  rw [permanent_exp_scaling, ← mul_assoc, ← Real.exp_add]
  simp

/-- Separate row and column selectors preserve their respective factors.
This is the exact nonprincipal scaling identity, with arbitrary selectors. -/
theorem permanent_submatrix_scaling {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (r c : ι → ℝ) (rows cols : κ → ι) :
    Matrix.permanent (Matrix.submatrix (fun i j => r i * A i j * c j) rows cols) =
      (∏ i, r (rows i)) * (∏ j, c (cols j)) * (A.submatrix rows cols).permanent := by
  exact permanent_row_column_scaling (A.submatrix rows cols) (r ∘ rows) (c ∘ cols)

theorem prod_compl_restoration {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, f i ≠ 0) :
    (∏ i ∈ sᶜ, f i) = (∏ i, f i) * ∏ i ∈ s, (f i)⁻¹ := by
  rw [← Finset.prod_mul_prod_compl s f, Finset.prod_inv_distrib]
  have hp : (∏ i ∈ s, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)
  field_simp

/-- Deleted rows restore the (1+a) inverse factors; deleted columns restore
the (1-a) inverse factors. No equality between I and J is assumed. -/
theorem paired_deleted_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (I J : Finset ι) (ha : ∀ i, -1 < a i ∧ a i < 1) :
    (∏ i ∈ Iᶜ, (1 + a i)) * (∏ j ∈ Jᶜ, (1 - a j)) =
      (∏ i, (1 - a i ^ 2)) * (∏ i ∈ I, (1 + a i)⁻¹) *
        (∏ j ∈ J, (1 - a j)⁻¹) := by
  have hp : (∏ i, (1 - a i ^ 2)) = (∏ i, (1 + a i)) * ∏ i, (1 - a i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [prod_compl_restoration I (fun i => 1 + a i) (fun i => by linarith [(ha i).1]),
    prod_compl_restoration J (fun i => 1 - a i) (fun i => by linarith [(ha i).2]), hp]
  ring

/-- The whole-score product retained throughout the global reduction. -/
theorem score_product_le_exp {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i ^ 2 ≤ 1) :
    (∏ i, (1 - a i ^ 2)) ≤ Real.exp (-(∑ i, a i ^ 2)) := by
  calc
    (∏ i, (1 - a i ^ 2)) ≤ ∏ i, Real.exp (-(a i ^ 2)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        linarith [ha i]
      · intro i _
        have h := Real.add_one_le_exp (-(a i ^ 2))
        linarith
    _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]

end TournamentHamiltonian
