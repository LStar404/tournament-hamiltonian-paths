import TournamentHamiltonian.GramDeletion

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

section RealMatrices

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem posDef_logdet_le_trace_sub_card (A : Matrix n n ℝ) (hA : A.PosDef) :
    Real.log A.det ≤ A.trace - Fintype.card n := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues]
  change Real.log (∏ i, hA.isHermitian.eigenvalues i) ≤
    (∑ i, hA.isHermitian.eigenvalues i) - Fintype.card n
  rw [Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')]
  calc
    _ ≤ ∑ i, (hA.isHermitian.eigenvalues i - 1) :=
      Finset.sum_le_sum (fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
    _ = _ := by simp [Finset.sum_sub_distrib]

/-- The supporting-plane inequality for log det, proved by positive
square-root conjugation and the scalar log(x) <= x-1 inequality. -/
theorem posDef_logdet_difference_le_trace (A B : Matrix n n ℝ)
    (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det - Real.log A.det ≤ (A⁻¹ * (B - A)).trace := by
  let R := CFC.sqrt A⁻¹
  let Q := R * B * R
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A⁻¹)
  have hR2 : R * R = A⁻¹ := CFC.sqrt_mul_sqrt_self A⁻¹ hA.inv.posSemidef.nonneg
  have hRT : R.transpose = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have hQ : Q.PosSemidef := by
    simpa only [Q, Matrix.conjTranspose_eq_transpose_of_trivial, hRT] using
      hB.posSemidef.mul_mul_conjTranspose_same R
  have hdet : Q.det = B.det / A.det := by
    calc
      _ = (R * R).det * B.det := by simp only [Q, Matrix.det_mul]; ring
      _ = A⁻¹.det * B.det := by rw [hR2]
      _ = _ := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; ring
  have hpos : 0 < Q.det := by rw [hdet]; exact div_pos hB.det_pos hA.det_pos
  have hQpd : Q.PosDef := hQ.posDef_iff_det_ne_zero.mpr hpos.ne'
  have htrace : Q.trace = (A⁻¹ * B).trace := by
    change (R * B * R).trace = _
    rw [Matrix.trace_mul_cycle R B R, hR2]
  have hlog : Real.log Q.det = Real.log B.det - Real.log A.det := by
    rw [hdet, Real.log_div hB.det_pos.ne' hA.det_pos.ne']
  have h := posDef_logdet_le_trace_sub_card Q hQpd
  rw [hlog, htrace] at h
  simpa only [Matrix.mul_sub, Matrix.trace_sub, Matrix.nonsing_inv_mul A
    (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), Matrix.trace_one] using h

theorem inverse_opNorm_le_of_quadratic_lower (A : Matrix n n ℝ) (hA : A.PosDef)
    (gap : ℝ) (hg : 0 < gap)
    (hbound : ∀ y : n → ℝ, gap * (∑ i, y i ^ 2) ≤ dotProduct y (A *ᵥ y)) :
    ‖A⁻¹‖ ≤ gap⁻¹ := by
  let hM := hA.inv.isHermitian
  have hf (i : n) : hM.eigenvalues i ≤ gap⁻¹ := by
    let v := hM.eigenvectorBasis i
    have hv : (∑ j, v j ^ 2) = 1 := by
      have h := v.norm_sq_eq
      rw [hM.eigenvectorBasis.orthonormal.1 i] at h
      simpa only [one_pow, Real.norm_eq_abs, sq_abs] using h.symm
    have h := inverse_quadratic_upper_of_lower A hA gap hg hbound (fun j => v j)
    rw [hv] at h
    have he : hM.eigenvalues i = dotProduct (fun j => v j) (A⁻¹ *ᵥ (fun j => v j)) := by
      simpa only [RCLike.re_to_real, Pi.star_apply, star_trivial] using hM.eigenvalues_eq i
    rw [← he] at h
    simpa only [one_div] using h
  rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hg.le)).mpr
  intro i
  have hi := hA.inv.eigenvalues_pos i
  change ‖hM.eigenvalues i‖ ≤ gap⁻¹
  rw [Real.norm_eq_abs, abs_of_pos hi]
  exact hf i

/-- An explicit Frobenius norm, independent of the ambient operator-norm
instance used in the Gaussian gap assumptions. -/
noncomputable def realFrobeniusNorm (Z : Matrix m n ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, Z i j ^ 2)

omit [DecidableEq m] [DecidableEq n] in
theorem realFrobeniusNorm_nonneg (Z : Matrix m n ℝ) : 0 ≤ realFrobeniusNorm Z :=
  Real.sqrt_nonneg _

omit [DecidableEq m] [DecidableEq n] in
theorem realFrobeniusNorm_sq (Z : Matrix m n ℝ) :
    realFrobeniusNorm Z ^ 2 = ∑ i, ∑ j, Z i j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

omit [DecidableEq m] [DecidableEq n] in
theorem realFrobeniusNorm_neg (Z : Matrix m n ℝ) :
    realFrobeniusNorm (-Z) = realFrobeniusNorm Z := by
  simp [realFrobeniusNorm]

omit [DecidableEq m] [DecidableEq n] in
theorem realFrobeniusNorm_transpose (Z : Matrix m n ℝ) :
    realFrobeniusNorm Z.transpose = realFrobeniusNorm Z := by
  unfold realFrobeniusNorm
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]

omit [DecidableEq m] [DecidableEq n] in
theorem trace_transpose_mul_abs_le_frobenius (U V : Matrix m n ℝ) :
    |(U.transpose * V).trace| ≤ realFrobeniusNorm U * realFrobeniusNorm V := by
  let u : EuclideanSpace ℝ (m × n) := WithLp.toLp 2 (fun ij => U ij.1 ij.2)
  let v : EuclideanSpace ℝ (m × n) := WithLp.toLp 2 (fun ij => V ij.1 ij.2)
  have hu : ‖u‖ = realFrobeniusNorm U := by
    rw [← Real.sqrt_sq (norm_nonneg u), EuclideanSpace.norm_sq_eq]
    simp [u, realFrobeniusNorm, Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]
  have hv : ‖v‖ = realFrobeniusNorm V := by
    rw [← Real.sqrt_sq (norm_nonneg v), EuclideanSpace.norm_sq_eq]
    simp [v, realFrobeniusNorm, Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]
  have heq : inner ℝ u v = (U.transpose * V).trace := by
    simp only [u, v, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [← heq, ← hu, ← hv]
  exact abs_real_inner_le_norm _ _

omit [DecidableEq m] in
theorem realFrobeniusNorm_mul_le_opNorm_right (X : Matrix m n ℝ) (A : Matrix n n ℝ) :
    realFrobeniusNorm (X * A) ≤ realFrobeniusNorm X * ‖A‖ := by
  apply (sq_le_sq₀ (realFrobeniusNorm_nonneg _)
    (mul_nonneg (realFrobeniusNorm_nonneg _) (norm_nonneg _))).mp
  rw [realFrobeniusNorm_sq, mul_pow, realFrobeniusNorm_sq, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have h := rectangular_gram_action_sq_le A.transpose (X i)
  have heq : A.transpose *ᵥ X i = (X * A) i := by
    ext j
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, mul_comm]
  rw [heq] at h
  have ht : ‖A.transpose‖ = ‖A‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose A
  rw [ht] at h
  simpa only [mul_comm] using h

omit [DecidableEq m] in
theorem gram_trace_difference_bound (U V : Matrix m n ℝ) (A : Matrix n n ℝ)
    (gap : ℝ) (_hg : 0 < gap) (hA : ‖A‖ ≤ gap⁻¹) :
    (A * (U.transpose * U - V.transpose * V)).trace ≤
      (realFrobeniusNorm U + realFrobeniusNorm V) * realFrobeniusNorm (U - V) / gap := by
  let D := U - V
  have hd : U.transpose * U - V.transpose * V = U.transpose * D + D.transpose * V := by
    dsimp [D]
    rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]
    abel
  have h1 : (A * (U.transpose * D)).trace = (U.transpose * (D * A)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle A U.transpose D,
      Matrix.trace_mul_cycle D A U.transpose, Matrix.mul_assoc]
  have h2 : (A * (D.transpose * V)).trace = (D.transpose * (V * A)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle A D.transpose V,
      Matrix.trace_mul_cycle V A D.transpose, Matrix.mul_assoc]
  have hn (X : Matrix m n ℝ) : realFrobeniusNorm (X * A) ≤ realFrobeniusNorm X / gap :=
    (realFrobeniusNorm_mul_le_opNorm_right X A).trans (by
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hA (realFrobeniusNorm_nonneg X))
  rw [hd, Matrix.mul_add, Matrix.trace_add, h1, h2]
  calc
    _ ≤ |(U.transpose * (D * A)).trace| + |(D.transpose * (V * A)).trace| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤ realFrobeniusNorm U * realFrobeniusNorm (D * A) +
        realFrobeniusNorm D * realFrobeniusNorm (V * A) :=
      add_le_add (trace_transpose_mul_abs_le_frobenius _ _) (trace_transpose_mul_abs_le_frobenius _ _)
    _ ≤ realFrobeniusNorm U * (realFrobeniusNorm D / gap) +
        realFrobeniusNorm D * (realFrobeniusNorm V / gap) :=
      add_le_add (mul_le_mul_of_nonneg_left (hn D) (realFrobeniusNorm_nonneg U))
        (mul_le_mul_of_nonneg_left (hn V) (realFrobeniusNorm_nonneg D))
    _ = _ := by dsimp [D]; ring

omit [DecidableEq m] in
/-- The one-sided Gaussian comparison for actual rectangular real kernels. -/
theorem gramGaussian_log_difference_le (U V : Matrix m n ℝ) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hU : ‖U‖ ≤ q) (hV : ‖V‖ ≤ q) :
    Real.log (gramGaussian U) - Real.log (gramGaussian V) ≤
      (realFrobeniusNorm U + realFrobeniusNorm V) * realFrobeniusNorm (U - V) /
        (2 * (1 - q ^ 2)) := by
  let A := (1 : Matrix n n ℝ) - U.transpose * U
  let B := (1 : Matrix n n ℝ) - V.transpose * V
  have hA : A.PosDef := gram_complement_posDef U q hq hq1 hU
  have hB : B.PosDef := gram_complement_posDef V q hq hq1 hV
  have hg : 0 < 1 - q ^ 2 := by nlinarith
  have hn : ‖A⁻¹‖ ≤ (1 - q ^ 2)⁻¹ := inverse_opNorm_le_of_quadratic_lower A hA
    (1 - q ^ 2) hg (gram_complement_quadratic_lower U q hq hU)
  have hlog := posDef_logdet_difference_le_trace A B hA hB
  have hd : B - A = U.transpose * U - V.transpose * V := by dsimp [A, B]; abel
  rw [hd] at hlog
  have ht := gram_trace_difference_bound U V A⁻¹ (1 - q ^ 2) hg hn
  rw [gramGaussian_log U hA.det_pos, gramGaussian_log V hB.det_pos]
  have h := hlog.trans ht
  dsimp [A, B] at h
  have he : (realFrobeniusNorm U + realFrobeniusNorm V) * realFrobeniusNorm (U - V) /
      (2 * (1 - q ^ 2)) = (1 / 2 : ℝ) *
      ((realFrobeniusNorm U + realFrobeniusNorm V) * realFrobeniusNorm (U - V) /
        (1 - q ^ 2)) := by field_simp [hg.ne']
  rw [he]
  linarith

omit [DecidableEq m] in
/-- The full two-kernel logarithmic Lipschitz estimate, with no assumed
derivative or determinant monotonicity bound. -/
theorem gramGaussian_log_lipschitz (U V : Matrix m n ℝ) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hU : ‖U‖ ≤ q) (hV : ‖V‖ ≤ q) :
    |Real.log (gramGaussian U) - Real.log (gramGaussian V)| ≤
      (realFrobeniusNorm U + realFrobeniusNorm V) * realFrobeniusNorm (U - V) /
        (2 * (1 - q ^ 2)) := by
  apply abs_le.mpr
  constructor
  · have h := gramGaussian_log_difference_le V U q hq hq1 hV hU
    have he : realFrobeniusNorm (V - U) = realFrobeniusNorm (U - V) := by
      rw [show V - U = -(U - V) by abel, realFrobeniusNorm_neg]
    rw [he, add_comm (realFrobeniusNorm V)] at h
    linarith
  · exact gramGaussian_log_difference_le U V q hq hq1 hU hV

end RealMatrices

end TournamentHamiltonian
