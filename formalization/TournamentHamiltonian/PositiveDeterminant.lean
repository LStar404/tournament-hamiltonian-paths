import TournamentHamiltonian.Definitions
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Positivity of the determinant weights in the exact path convolution.
Quadratic positivity suffices; the matrix need not be symmetric. The proof
uses principal-submatrix induction and an adjugate column, at every order. -/

namespace TournamentHamiltonian

def QuadraticPositive {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, x ≠ 0 → 0 < dotProduct x (M.mulVec x)

private theorem det_pos_fin (n : ℕ) :
    ∀ M : Matrix (Fin n) (Fin n) ℝ, QuadraticPositive M → 0 < M.det := by
  induction n with
  | zero => intro M _; simp
  | succ n ih =>
    intro N hN
    let M := N.submatrix Fin.succ Fin.succ
    have hM : QuadraticPositive M := by
      intro x hx
      let y : Fin (n + 1) → ℝ := Fin.cons 0 x
      have hy : y ≠ 0 := by
        intro h
        apply hx
        funext i
        have hi := congrArg (fun f : Fin (n + 1) → ℝ => f i.succ) h
        simpa [y] using hi
      have h := hN y hy
      simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, y, M] using h
    have hd : 0 < M.det := ih M hM
    let v := N.adjugate.col 0
    have hvM : v 0 = M.det := by
      simp [v, M, Matrix.adjugate_fin_succ_eq_det_submatrix]
    have hNv : N.mulVec v = fun i => if i = 0 then N.det else 0 := by
      ext i
      simp [v, ← Matrix.col_mul_eq_mulVec_col, Matrix.mul_adjugate, Matrix.one_apply]
    have hv : v ≠ 0 := by
      intro h
      have hz : v 0 = 0 := congrArg (fun f : Fin (n + 1) → ℝ => f 0) h
      rw [hvM] at hz
      exact hd.ne' hz
    have hpos : 0 < M.det * N.det := by
      simpa [hNv, dotProduct, hvM] using hN v hv
    exact (mul_pos_iff_of_pos_left hd).mp hpos

lemma quadratic_reindex_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι ι ℝ) (e : κ ≃ ι) (x : κ → ℝ) :
    dotProduct x ((M.submatrix e e).mulVec x) =
      dotProduct (x ∘ e.symm) (M.mulVec (x ∘ e.symm)) := by
  unfold dotProduct Matrix.mulVec
  apply Fintype.sum_equiv e
  intro i
  simp only [Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply]
  congr 1
  apply Fintype.sum_equiv e
  intro j
  simp

/-- A real square matrix with a strictly positive quadratic form has positive
determinant, including the empty matrix. Symmetry is not required. -/
theorem det_pos_of_quadraticPositive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : QuadraticPositive M) : 0 < M.det := by
  let e := (Fintype.equivFin ι).symm
  rw [← Matrix.det_submatrix_equiv_self e M]
  apply det_pos_fin
  intro x hx
  rw [quadratic_reindex_equiv]
  apply hM
  intro h
  apply hx
  funext i
  have hi := congrArg (fun f : ι → ℝ => f (e i)) h
  simpa using hi

theorem skew_quadratic_zero {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ)
    (hS : ∀ i j, S i j = -S j i) (x : ι → ℝ) :
    dotProduct x (S.mulVec x) = 0 := by
  let q : ℝ := ∑ i, ∑ j, x i * S i j * x j
  have heq : dotProduct x (S.mulVec x) = q := by
    simp [q, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hq : q = -q := by
    calc
      q = ∑ j, ∑ i, x i * S i j * x j := Finset.sum_comm
      _ = ∑ j, ∑ i, -(x j * S j i * x i) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [hS i j]
        ring
      _ = -q := by simp [q]
  rw [heq]
  linarith

theorem identity_ones_skew_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : ∀ i j, S i j = -S j i) (x : ι → ℝ) :
    dotProduct x (((1 : Matrix ι ι ℝ) + Matrix.of (fun _ _ => 1) + S).mulVec x) =
      (∑ i, x i ^ 2) + (∑ i, x i) ^ 2 := by
  have hones : dotProduct x (Matrix.mulVec (Matrix.of (fun _ _ => (1 : ℝ))) x) =
      (∑ i, x i) ^ 2 := by
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul]
    rw [← Finset.sum_mul]
    ring
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec, hones,
    skew_quadratic_zero S hS, add_zero]
  simp [dotProduct, pow_two]

theorem det_pos_of_twice_eq_identity_ones_skew {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W S : Matrix ι ι ℝ) (hS : ∀ i j, S i j = -S j i)
    (hW : (2 : ℝ) • W = (1 : Matrix ι ι ℝ) + Matrix.of (fun _ _ => 1) + S) :
    0 < W.det := by
  apply det_pos_of_quadraticPositive
  intro x hx
  have hq := congrArg (fun M : Matrix ι ι ℝ => dotProduct x (M.mulVec x)) hW
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    identity_ones_skew_quadratic S hS] at hq
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    simpa using (not_exists.mp h i)
  have hsum : 0 < ∑ j, x j ^ 2 :=
    Finset.sum_pos' (fun j _ => sq_nonneg (x j))
      ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  nlinarith [sq_nonneg (∑ i, x i)]

/-- Every determinant weight in the tournament path convolution is strictly
positive, including the empty principal submatrix. -/
theorem principal_weight_pos {n : ℕ} (T : Tournament n) (U : Finset (Fin n)) :
    0 < ((1 : Matrix U U ℝ) + (adjacency T).submatrix Subtype.val Subtype.val).det := by
  let S : Matrix U U ℝ := (signMatrix T).submatrix Subtype.val Subtype.val
  apply det_pos_of_twice_eq_identity_ones_skew _ S
  · intro i j
    exact signMatrix_skew T i.val j.val
  · ext i j
    have h := twice_adjacency T i.val j.val
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply,
      Matrix.of_apply, Matrix.submatrix_apply, S, Subtype.ext_iff]
    nlinarith

end TournamentHamiltonian
