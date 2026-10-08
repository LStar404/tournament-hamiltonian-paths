import TournamentHamiltonian.Definitions
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Ring.GeomSum

namespace TournamentHamiltonian

section Field

variable {K : Type*} [Field K]

/-- The ordered transitive tournament's skew matrix, with the manuscript's
positive-above-diagonal sign convention. -/
def transitiveSkew (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i < j then 1 else if j < i then -1 else 0

noncomputable def transitiveKernel (n : ℕ) (z : K) : Matrix (Fin n) (Fin n) K :=
  1 + z • transitiveSkew n

private noncomputable def triangularPart (n : ℕ) (z : K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i = j then 1 + z else if i < j then 2 * z else 0

private theorem triangularPart_det (n : ℕ) (z : K) :
    (triangularPart n z).det = (1 + z) ^ n := by
  have htri : (triangularPart n z).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    have hne : i ≠ j := ne_of_gt hij
    simp [triangularPart, hne, not_lt_of_ge hij.le]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [triangularPart]

private theorem sum_reverse_powers (r : K) (n : ℕ) :
    (∑ i : Fin n, r ^ (n - 1 - i.val)) = ∑ i ∈ Finset.range n, r ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have ht : (∑ i : Fin n, r ^ (n + 1 - 1 - i.succ.val)) =
        ∑ i : Fin n, r ^ (n - 1 - i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      simp only [Fin.val_succ]
      omega
    rw [ht, ih, geom_sum_succ']
    simp [add_comm]

private noncomputable def geometricVector (n : ℕ) (z : K) : Fin n → K :=
  fun i => ((1 - z) / (1 + z)) ^ (n - 1 - i.val) / (1 + z)

private theorem geometricVector_sum (n : ℕ) (z : K) :
    (∑ i : Fin n, geometricVector n z i) =
      (∑ i ∈ Finset.range n, ((1 - z) / (1 + z)) ^ i) / (1 + z) := by
  simp only [geometricVector, ← Finset.sum_div, sum_reverse_powers]

private theorem triangularPart_mulVec (n : ℕ) (z : K) (hz : 1 + z ≠ 0) :
    (triangularPart n z).mulVec (geometricVector n z) = fun _ => 1 := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · have hv : ∀ j : Fin n, geometricVector (n + 1) z j.succ = geometricVector n z j := by
        intro j
        unfold geometricVector
        congr 2
        simp only [Fin.val_succ]
        omega
      have hd : ∀ j : Fin n, triangularPart (n + 1) z 0 j.succ = 2 * z := by
        intro j
        have h0 : (0 : Fin (n + 1)) < j.succ := by
          simp only [Fin.lt_def, Fin.val_zero, Fin.val_succ]
          omega
        simp [triangularPart, ne_of_lt h0, h0]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hv, hd]
      simp only [triangularPart, ite_true, geometricVector, Fin.val_zero, Nat.sub_zero,
        Nat.add_sub_cancel]
      rw [← Finset.mul_sum]
      change (1 + z) * (((1 - z) / (1 + z)) ^ n / (1 + z)) +
        2 * z * (∑ j : Fin n, geometricVector n z j) = 1
      rw [geometricVector_sum]
      have hg := geom_sum_mul_neg ((1 - z) / (1 + z)) n
      have hcoeff : 1 - (1 - z) / (1 + z) = 2 * z / (1 + z) := by field_simp; ring
      rw [hcoeff] at hg
      field_simp at hg ⊢
      linear_combination hg
    · have hd : triangularPart (n + 1) z i.succ 0 = 0 := by
        simp [triangularPart, Fin.succ_ne_zero]
      have hD : ∀ j : Fin n, triangularPart (n + 1) z i.succ j.succ = triangularPart n z i j := by
        intro j
        simp [triangularPart]
      have hv : ∀ j : Fin n, geometricVector (n + 1) z j.succ = geometricVector n z j := by
        intro j
        unfold geometricVector
        congr 2
        simp only [Fin.val_succ]
        omega
      have h := congrFun ih i
      simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hd, hv, hD, zero_mul, zero_add] using h

private theorem kernel_eq_rank_one (n : ℕ) (z : K) :
    transitiveKernel n z = triangularPart n z +
      Matrix.replicateCol Unit (fun _ : Fin n => -z) *
        Matrix.replicateRow Unit (fun _ : Fin n => (1 : K)) := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [transitiveKernel, triangularPart, transitiveSkew, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, hij, ne_of_lt hij]
    ring
  · simp [transitiveKernel, triangularPart, transitiveSkew, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply]
  · simp [transitiveKernel, triangularPart, transitiveSkew, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, hji, ne_of_gt hji, not_lt_of_ge hji.le]

variable [CharZero K]

private theorem transitiveKernel_det_of_ne (n : ℕ) (z : K) (hz : 1 + z ≠ 0) :
    (transitiveKernel n z).det = ((1 + z) ^ n + (1 - z) ^ n) / 2 := by
  have hd : IsUnit (triangularPart n z).det := by
    rw [triangularPart_det]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hz)
  have hinv : (triangularPart n z)⁻¹.mulVec (fun _ => (1 : K)) = geometricVector n z := by
    have h := congrArg (Matrix.mulVec (triangularPart n z)⁻¹) (triangularPart_mulVec n z hz)
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec] at h
    exact h.symm
  have hneg : (triangularPart n z)⁻¹.mulVec (fun _ => -z) = (-z) • geometricVector n z := by
    have heq : (fun _ : Fin n => -z) = (-z) • (fun _ : Fin n => (1 : K)) := by
      ext i
      simp
    rw [heq, Matrix.mulVec_smul, hinv]
  rw [kernel_eq_rank_one, Matrix.det_add_replicateCol_mul_replicateRow hd,
    Matrix.mul_assoc, ← Matrix.replicateCol_mulVec, hneg, Matrix.det_unique (n := Unit)]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.replicateRow_mul_replicateCol_apply,
    dotProduct, Pi.smul_apply, smul_eq_mul, one_mul, ← Finset.mul_sum]
  rw [geometricVector_sum, triangularPart_det]
  have hg := geom_sum_mul_neg ((1 - z) / (1 + z)) n
  have hcoeff : 1 - (1 - z) / (1 + z) = 2 * z / (1 + z) := by field_simp; ring
  rw [hcoeff] at hg
  have hrec : 1 + (-z) * ((∑ i ∈ Finset.range n, ((1 - z) / (1 + z)) ^ i) / (1 + z)) =
      (1 + ((1 - z) / (1 + z)) ^ n) / 2 := by
    field_simp at hg ⊢
    linear_combination -hg
  rw [hrec, div_pow]
  field_simp

omit [CharZero K] in
theorem transitiveSkew_skew (n : ℕ) (i j : Fin n) :
    (transitiveSkew n : Matrix (Fin n) (Fin n) K) i j = -transitiveSkew n j i := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [transitiveSkew, hij, not_lt_of_ge hij.le]
  · simp [transitiveSkew]
  · simp [transitiveSkew, hji, not_lt_of_ge hji.le]

omit [CharZero K] in
theorem transitiveKernel_transpose (n : ℕ) (z : K) :
    (transitiveKernel n z).transpose = transitiveKernel n (-z) := by
  have hS : (transitiveSkew n : Matrix (Fin n) (Fin n) K).transpose = -transitiveSkew n := by
    ext i j
    exact transitiveSkew_skew n j i
  simp only [transitiveKernel, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_smul, hS, smul_neg, neg_smul]

/-- The exact all-order transitive determinant formula in Section 2.3.
The singular triangular parameter z=-1 is covered by transposition. -/
theorem transitiveKernel_det (n : ℕ) (z : K) :
    (transitiveKernel n z).det = ((1 + z) ^ n + (1 - z) ^ n) / 2 := by
  by_cases hz : 1 + z = 0
  · calc
      _ = (transitiveKernel n (-z)).det := by
        rw [← Matrix.det_transpose, transitiveKernel_transpose]
      _ = ((1 + (-z)) ^ n + (1 - (-z)) ^ n) / 2 :=
        transitiveKernel_det_of_ne n (-z) (by
          intro h
          have htwo : (2 : K) = 0 := by linear_combination hz + h
          exact two_ne_zero htwo)
      _ = _ := by simp only [← sub_eq_add_neg, sub_neg_eq_add]; rw [add_comm]
  · exact transitiveKernel_det_of_ne n z hz

end Field

def transitiveTournament (n : ℕ) : Tournament n :=
  ⟨(fun i j => decide (i < j)), by
    constructor
    · intro i
      simp
    · intro i j hne
      rcases lt_or_gt_of_ne hne with hij | hji
      · simp [hij, not_lt_of_ge hij.le]
      · simp [hji, not_lt_of_ge hji.le]⟩

theorem signMatrix_transitiveTournament (n : ℕ) :
    signMatrix (transitiveTournament n) = transitiveSkew n := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [signMatrix, transitiveTournament, transitiveSkew, hij, ne_of_lt hij]
  · simp [signMatrix, transitiveSkew]
  · simp [signMatrix, transitiveTournament, transitiveSkew, hji, ne_of_gt hji,
      not_lt_of_ge hji.le]

theorem transitiveTournament_det (n : ℕ) (z : ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + z • signMatrix (transitiveTournament n)).det =
      ((1 + z) ^ n + (1 - z) ^ n) / 2 := by
  rw [signMatrix_transitiveTournament]
  exact transitiveKernel_det n z

end TournamentHamiltonian
