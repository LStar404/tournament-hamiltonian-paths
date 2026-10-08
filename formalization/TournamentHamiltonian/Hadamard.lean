import TournamentHamiltonian.PositiveDeterminant
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.MeanInequalities

namespace TournamentHamiltonian

private theorem hadamard_fin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    |M.det| ≤ ∏ i, Real.sqrt (∑ j, M i j ^ 2) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (M.row i)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  have h := b.toBasis.orientation.abs_volumeForm_apply_le v
  rw [b.toBasis.orientation.volumeForm_robust' b] at h
  have hm : b.toBasis.toMatrix v = M.transpose := by
    ext i j
    simp [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      b, v, EuclideanSpace.basisFun_repr, Matrix.row, Matrix.transpose_apply]
  rw [Module.Basis.det_apply, hm, Matrix.det_transpose] at h
  simpa [v, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Matrix.row] using h

/-- Hadamard's row bound for every finite real square matrix. -/
theorem hadamard {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    |M.det| ≤ ∏ i, Real.sqrt (∑ j, M i j ^ 2) := by
  let e := (Fintype.equivFin ι).symm
  have h := hadamard_fin (M.submatrix e e)
  rw [Matrix.det_submatrix_equiv_self] at h
  convert h using 1
  symm
  apply Fintype.prod_equiv e
  intro i
  congr 1
  apply Fintype.sum_equiv e
  intro j
  rfl

theorem prod_le_mean_pow {ι : Type*} [Fintype ι] (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    (∏ i, z i) ≤ ((∑ i, z i) / Fintype.card ι) ^ Fintype.card ι := by
  classical
  by_cases hc : Fintype.card ι = 0
  · let := Fintype.card_eq_zero_iff.mp hc
    simp
  have hcR : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : ι => 1) z
    (fun _ _ => zero_le_one) (by simpa only [Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using hcR)
    (fun i _ => hz i)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, one_mul] at h
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => hz i)) _) h
    (Fintype.card ι)
  rwa [Real.rpow_inv_natCast_pow (Finset.prod_nonneg (fun i _ => hz i)) hc] at hp

noncomputable def principalWeightMatrix {n : ℕ} (T : Tournament n) (U : Finset (Fin n)) :
    Matrix U U ℝ := 1 + (adjacency T).submatrix Subtype.val Subtype.val

theorem principalWeightMatrix_sq {n : ℕ} (T : Tournament n) (U : Finset (Fin n))
    (i j : U) : principalWeightMatrix T U i j ^ 2 = principalWeightMatrix T U i j := by
  classical
  by_cases hij : i = j
  · subst j
    simp [principalWeightMatrix, adjacency, T.property.1]
  · cases he : T.val i.val j.val <;>
      simp [principalWeightMatrix, hij, adjacency, he]

theorem principalWeightMatrix_total_sq {n : ℕ} (T : Tournament n) (U : Finset (Fin n)) :
    (∑ i : U, ∑ j : U, principalWeightMatrix T U i j ^ 2) =
      (U.card : ℝ) * (U.card + 1) / 2 := by
  classical
  have hs : (∑ i : U, ∑ j : U, signMatrix T i.val j.val) = 0 := by
    simpa only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, one_mul, mul_one] using
      skew_quadratic_zero ((signMatrix T).submatrix (Subtype.val : U → Fin n) Subtype.val)
        (fun i j => signMatrix_skew T i.val j.val) (fun _ => 1)
  have hw : ∀ i j : U, 2 * principalWeightMatrix T U i j =
      (if i = j then 1 else 0) + 1 + signMatrix T i.val j.val := by
    intro i j
    have h := twice_adjacency T i.val j.val
    simp only [principalWeightMatrix, Matrix.add_apply, Matrix.one_apply,
      Matrix.submatrix_apply, Subtype.ext_iff]
    nlinarith
  have heq : 2 * (∑ i : U, ∑ j : U, principalWeightMatrix T U i j) =
      (U.card : ℝ) + (U.card : ℝ) * U.card := by
    simp_rw [Finset.mul_sum, hw, Finset.sum_add_distrib]
    rw [hs]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe]
    ring
  simp_rw [principalWeightMatrix_sq]
  nlinarith

/-- The manuscript's degree/Hadamard bound, in a square-root form valid also
for the empty subset. -/
theorem principal_weight_le {n : ℕ} (T : Tournament n) (U : Finset (Fin n)) :
    (principalWeightMatrix T U).det ≤ Real.sqrt (((U.card + 1 : ℝ) / 2) ^ U.card) := by
  classical
  by_cases hc : U.card = 0
  · have hU : U = ∅ := Finset.card_eq_zero.mp hc
    subst U
    simp [principalWeightMatrix]
  have hcR : (U.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have h := hadamard (principalWeightMatrix T U)
  have hp := prod_le_mean_pow (fun i : U => ∑ j : U, principalWeightMatrix T U i j ^ 2)
    (fun i => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hmean : (∑ i : U, ∑ j : U, principalWeightMatrix T U i j ^ 2) / Fintype.card U =
      (U.card + 1 : ℝ) / 2 := by
    rw [principalWeightMatrix_total_sq, Fintype.card_coe]
    field_simp
  have hprod : (∏ i : U, Real.sqrt (∑ j : U, principalWeightMatrix T U i j ^ 2)) ^ 2 =
      ∏ i : U, ∑ j : U, principalWeightMatrix T U i j ^ 2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    exact Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hd : 0 < (principalWeightMatrix T U).det := principal_weight_pos T U
  rw [abs_of_pos hd] at h
  have hh := pow_le_pow_left₀ hd.le h 2
  rw [hprod] at hh
  apply (Real.le_sqrt hd.le (by positivity)).mpr
  rw [hmean, Fintype.card_coe] at hp
  exact hh.trans hp

/-- The exact `h_k` notation of the manuscript, with real exponent `k/2`. -/
theorem principal_weight_le_rpow {n : ℕ} (T : Tournament n) (U : Finset (Fin n)) :
    (principalWeightMatrix T U).det ≤
      ((U.card + 1 : ℝ) / 2) ^ ((U.card : ℝ) / 2) := by
  have heq : Real.sqrt (((U.card + 1 : ℝ) / 2) ^ U.card) =
      ((U.card + 1 : ℝ) / 2) ^ ((U.card : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (U.card + 1 : ℝ) / 2)]
    congr 1
    ring
  simpa only [heq] using principal_weight_le T U

end TournamentHamiltonian
