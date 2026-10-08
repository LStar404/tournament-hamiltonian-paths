import TournamentHamiltonian.Hadamard
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Actual principal-minor generating identities over any finite matrix. -/
namespace TournamentHamiltonian
open scoped Classical
open Polynomial
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_principal_generating_det (M : Matrix ι ι ℝ) (z : ℝ) :
    ((1 : Matrix ι ι ℝ) + z • M).det = ∑ s : Finset ι,
      z ^ s.card * (M.submatrix (Subtype.val : s → ι) Subtype.val).det := by
  have hpu : (Finset.univ : Finset ι).powerset = Finset.univ := by ext s; simp
  have hp : ((1 : Matrix ι ι ℝ[X]) + (X : ℝ[X]) • M.map C).det =
      ∑ s : Finset ι, C (M.submatrix (Subtype.val : s → ι) Subtype.val).det * X ^ s.card := by
    ext k
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    simp only [Finset.powersetCard_eq_filter, hpu, Finset.sum_filter,
      Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    apply Finset.sum_congr rfl
    intro s _
    simp only [eq_comm]
  have hm := (Polynomial.evalRingHom z).map_det ((1 : Matrix ι ι ℝ[X]) + (X : ℝ[X]) • M.map C)
  have heq : (((1 : Matrix ι ι ℝ[X]) + (X : ℝ[X]) • M.map C).map (Polynomial.evalRingHom z)) =
      (1 : Matrix ι ι ℝ) + z • M := by
    ext i j
    change Polynomial.eval z ((if i = j then (1 : ℝ[X]) else 0) + (X : ℝ[X]) * C (M i j)) = (if i = j then (1 : ℝ) else 0) + z * M i j
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    split_ifs <;> simp only [Polynomial.eval_one, Polynomial.eval_zero]
  change Polynomial.eval z ((1 : Matrix ι ι ℝ[X]) + (X : ℝ[X]) • M.map C).det =
    (((1 : Matrix ι ι ℝ[X]) + (X : ℝ[X]) • M.map C).map (Polynomial.evalRingHom z)).det at hm
  rw [heq, hp] at hm
  rw [← hm]
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact mul_comm _ _

theorem principalWeight_generating_det {n : ℕ} (T : Tournament n) (z : ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + z • (1 + adjacency T)).det =
      ∑ U : Finset (Fin n), z ^ U.card * (principalWeightMatrix T U).det := by
  rw [matrix_principal_generating_det]
  apply Finset.sum_congr rfl
  intro U _
  have heq : ((1 : Matrix (Fin n) (Fin n) ℝ) + adjacency T).submatrix (Subtype.val : U → Fin n) Subtype.val = principalWeightMatrix T U := by
    ext i j
    simp only [principalWeightMatrix, Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, Subtype.ext_iff]
  rw [heq]

end TournamentHamiltonian
