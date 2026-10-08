import TournamentHamiltonian.SkewOperatorNorm
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

section RealMatrices

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The rectangular Gaussian spectral factor in Section 4.2. -/
noncomputable def gramGaussian (Z : Matrix m n ℝ) : ℝ :=
  (Real.sqrt ((1 : Matrix n n ℝ) - Z.transpose * Z).det)⁻¹

theorem gramGaussian_transpose (Z : Matrix m n ℝ) :
    gramGaussian Z.transpose = gramGaussian Z := by
  unfold gramGaussian
  rw [Matrix.transpose_transpose, Matrix.det_one_sub_mul_comm]

private theorem real_hermitian_one_add_det (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    ((1 : Matrix n n ℝ) + A).det = ∏ i, (1 + hA.eigenvalues i) := by
  have heq : (1 : Matrix n n ℝ) + A =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (1 + Matrix.diagonal hA.eigenvalues) := by
    rw [map_add, map_one]
    exact congrArg (fun X => 1 + X) hA.spectral_theorem
  rw [heq, Unitary.conjStarAlgAut_apply, Matrix.det_mul_right_comm,
    ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul]
  have hd : (1 : Matrix n n ℝ) + Matrix.diagonal hA.eigenvalues =
      Matrix.diagonal (fun i => 1 + hA.eigenvalues i) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  rw [hd, Matrix.det_diagonal]

theorem posSemidef_logdet_one_add_bounds (D : Matrix n n ℝ) (hD : D.PosSemidef) :
    0 ≤ Real.log ((1 : Matrix n n ℝ) + D).det ∧
      Real.log ((1 : Matrix n n ℝ) + D).det ≤ D.trace := by
  rw [real_hermitian_one_add_det D hD.isHermitian, hD.isHermitian.trace_eq_sum_eigenvalues]
  change 0 ≤ Real.log (∏ i, (1 + hD.isHermitian.eigenvalues i)) ∧
    Real.log (∏ i, (1 + hD.isHermitian.eigenvalues i)) ≤ ∑ i, hD.isHermitian.eigenvalues i
  have hp : ∀ i : n, 0 < 1 + hD.isHermitian.eigenvalues i := by
    intro i
    have hi := hD.eigenvalues_nonneg i
    linarith
  have hprod : 0 < ∏ i, (1 + hD.isHermitian.eigenvalues i) :=
    Finset.prod_pos (fun i _ => hp i)
  rw [Real.log_prod (fun i _ => (hp i).ne')]
  constructor
  · exact Finset.sum_nonneg (fun i _ => Real.log_nonneg (by linarith [hD.eigenvalues_nonneg i]))
  · apply Finset.sum_le_sum
    intro i _
    have h := Real.log_le_sub_one_of_pos (hp i)
    linarith

omit [DecidableEq m] in
theorem gramGaussian_log (Z : Matrix m n ℝ)
    (hp : 0 < ((1 : Matrix n n ℝ) - Z.transpose * Z).det) :
    Real.log (gramGaussian Z) = -(1 / 2 : ℝ) *
      Real.log ((1 : Matrix n n ℝ) - Z.transpose * Z).det := by
  rw [gramGaussian, Real.log_inv, Real.log_sqrt hp.le]
  ring

omit [DecidableEq m] [DecidableEq n] in
theorem real_gram_quadratic (Z : Matrix m n ℝ) (x : n → ℝ) :
    dotProduct x ((Z.transpose * Z) *ᵥ x) = ∑ i, (Z *ᵥ x) i ^ 2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  change dotProduct (Z *ᵥ x) (Z *ᵥ x) = _
  simp [dotProduct, pow_two]

omit [DecidableEq m] in
theorem rectangular_gram_action_sq_le (Z : Matrix m n ℝ) (x : n → ℝ) :
    (∑ i, (Z *ᵥ x) i ^ 2) ≤ ‖Z‖ ^ 2 * (∑ j, x j ^ 2) := by
  let v : EuclideanSpace ℝ n := WithLp.toLp 2 x
  have h := pow_le_pow_left₀ (norm_nonneg _) (Matrix.l2_opNorm_mulVec Z v) 2
  rw [mul_pow] at h
  simpa [EuclideanSpace.norm_sq_eq, v, Real.norm_eq_abs, sq_abs] using h

omit [DecidableEq m] in
theorem gram_complement_quadratic_lower (Z : Matrix m n ℝ) (q : ℝ)
    (_hq : 0 ≤ q) (hZ : ‖Z‖ ≤ q) (x : n → ℝ) :
    (1 - q ^ 2) * (∑ i, x i ^ 2) ≤
      dotProduct x (((1 : Matrix n n ℝ) - Z.transpose * Z) *ᵥ x) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, real_gram_quadratic]
  have h := rectangular_gram_action_sq_le Z x
  have hn := pow_le_pow_left₀ (norm_nonneg Z) hZ 2
  have ht := mul_le_mul_of_nonneg_right hn
    (show 0 ≤ ∑ i, x i ^ 2 from Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))
  simp only [dotProduct, ← pow_two]
  nlinarith

omit [DecidableEq m] in
theorem gram_complement_posDef (Z : Matrix m n ℝ) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) :
    ((1 : Matrix n n ℝ) - Z.transpose * Z).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_one.sub (by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.isHermitian_conjTranspose_mul_self Z)
  · intro x hx
    have hxs : 0 < ∑ i, x i ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      have hsum := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      have hi' : x i ≠ 0 := by simpa using hi
      exact (sq_pos_of_ne_zero hi').trans_le hsum
    have hgap : 0 < 1 - q ^ 2 := by nlinarith
    exact (mul_pos hgap hxs).trans_le (gram_complement_quadratic_lower Z q hq hZ x)

theorem inverse_quadratic_upper_of_lower (A : Matrix n n ℝ) (hA : A.PosDef)
    (gap : ℝ) (hg : 0 < gap)
    (hbound : ∀ y : n → ℝ, gap * (∑ i, y i ^ 2) ≤ dotProduct y (A *ᵥ y))
    (x : n → ℝ) :
    dotProduct x (A⁻¹ *ᵥ x) ≤ (∑ i, x i ^ 2) / gap := by
  let y := A⁻¹ *ᵥ x
  have hAy : A *ᵥ y = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
      Matrix.one_mulVec]
  have hlow := hbound y
  rw [hAy, dotProduct_comm] at hlow
  have hnonneg : 0 ≤ ∑ i, (x i - gap * y i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hexpand : (∑ i, (x i - gap * y i) ^ 2) =
      (∑ i, x i ^ 2) - 2 * gap * dotProduct x y + gap ^ 2 * (∑ i, y i ^ 2) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hexpand] at hnonneg
  apply (le_div_iff₀ hg).mpr
  change dotProduct x y * gap ≤ _
  have hmul := mul_le_mul_of_nonneg_left hlow hg.le
  nlinarith

omit [DecidableEq m] in
theorem trace_inverse_conjugate_bound (A : Matrix n n ℝ) (hA : A.PosDef)
    (gap : ℝ) (hg : 0 < gap)
    (hbound : ∀ y : n → ℝ, gap * (∑ i, y i ^ 2) ≤ dotProduct y (A *ᵥ y))
    (R : Matrix m n ℝ) :
    (R * A⁻¹ * R.transpose).trace ≤ (R.transpose * R).trace / gap := by
  have htrace : (R * A⁻¹ * R.transpose).trace =
      ∑ i, dotProduct (R i) (A⁻¹ *ᵥ R i) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have htrace' : (R.transpose * R).trace = ∑ i, ∑ j, R i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, ← pow_two]
    rw [Finset.sum_comm]
  rw [htrace, htrace', Finset.sum_div]
  exact Finset.sum_le_sum (fun i _ => inverse_quadratic_upper_of_lower A hA gap hg hbound (R i))

/-- A genuine finite-dimensional logarithmic determinant bound. The only
gap input is the displayed quadratic lower bound for A. No derivative or
determinant monotonicity is assumed. -/
theorem posDef_logdet_increment_bound (A D : Matrix n n ℝ)
    (hA : A.PosDef) (hD : D.PosSemidef) (gap : ℝ) (hg : 0 < gap)
    (hbound : ∀ y : n → ℝ, gap * (∑ i, y i ^ 2) ≤ dotProduct y (A *ᵥ y)) :
    0 ≤ Real.log (A + D).det - Real.log A.det ∧
      Real.log (A + D).det - Real.log A.det ≤ D.trace / gap := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hD.nonneg
  have hDfactor : D = R.transpose * R := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hR
  let Q : Matrix n n ℝ := R * A⁻¹ * R.transpose
  have hQ : Q.PosSemidef := by
    simpa only [Q, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.inv.posSemidef.mul_mul_conjTranspose_same R
  have hdet : (A + D).det = A.det * ((1 : Matrix n n ℝ) + Q).det := by
    have heq : A + D = A * (1 + A⁻¹ * D) := by
      rw [mul_add, mul_one, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), one_mul]
    rw [heq, Matrix.det_mul, hDfactor]
    congr 1
    rw [← Matrix.mul_assoc, Matrix.det_one_add_mul_comm]
    simp only [Q, Matrix.mul_assoc]
  have hpos : 0 < ((1 : Matrix n n ℝ) + Q).det :=
    (Matrix.PosDef.one.add_posSemidef hQ).det_pos
  have hlog : Real.log (A + D).det - Real.log A.det =
      Real.log ((1 : Matrix n n ℝ) + Q).det := by
    rw [hdet, Real.log_mul hA.det_pos.ne' hpos.ne']
    ring
  rw [hlog]
  have h := posSemidef_logdet_one_add_bounds Q hQ
  refine ⟨h.1, h.2.trans ?_⟩
  rw [hDfactor]
  exact trace_inverse_conjugate_bound A hA gap hg hbound R

omit [Fintype n] [DecidableEq n] in
theorem row_gram_decomposition (Z : Matrix m n ℝ) (R : Finset m) :
    Z.transpose * Z =
      (Z.submatrix (fun i : R => i.val) id).transpose * Z.submatrix (fun i : R => i.val) id +
      (Z.submatrix (fun i : (Rᶜ : Finset m) => i.val) id).transpose *
        Z.submatrix (fun i : (Rᶜ : Finset m) => i.val) id := by
  classical
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    id_eq]
  simp only [Finset.univ_eq_attach]
  rw [Finset.sum_attach R (fun k => Z k i * Z k j),
    Finset.sum_attach (Rᶜ : Finset m) (fun k => Z k i * Z k j)]
  exact (Finset.sum_add_sum_compl R (fun k => Z k i * Z k j)).symm

omit [DecidableEq n] in
theorem row_deleted_gram_trace (Z : Matrix m n ℝ) (R : Finset m) :
    ((Z.submatrix (fun i : (Rᶜ : Finset m) => i.val) id).transpose *
      Z.submatrix (fun i : (Rᶜ : Finset m) => i.val) id).trace =
        ∑ i : (Rᶜ : Finset m), ∑ j, Z i.val j ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, id_eq, ← pow_two]
  rw [Finset.sum_comm]

/-- Actual deletion of arbitrary rows, including the empty/full retained
set and rectangular remaining matrices. -/
theorem gramGaussian_row_deletion_bound (Z : Matrix m n ℝ) (R : Finset m)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) :
    0 ≤ Real.log (gramGaussian Z) -
      Real.log (gramGaussian (Z.submatrix (fun i : R => i.val) id)) ∧
    Real.log (gramGaussian Z) -
      Real.log (gramGaussian (Z.submatrix (fun i : R => i.val) id)) ≤
      (∑ i : (Rᶜ : Finset m), ∑ j, Z i.val j ^ 2) / (2 * (1 - q ^ 2)) := by
  classical
  let A : Matrix n n ℝ := 1 - Z.transpose * Z
  let D : Matrix n n ℝ :=
    (Z.submatrix (fun i : (Rᶜ : Finset m) => i.val) id).transpose *
      Z.submatrix (fun i : (Rᶜ : Finset m) => i.val) id
  have hA : A.PosDef := gram_complement_posDef Z q hq hq1 hZ
  have hD : D.PosSemidef := by
    simpa only [D, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self
        (Z.submatrix (fun i : (Rᶜ : Finset m) => i.val) id)
  have hgap : 0 < 1 - q ^ 2 := by nlinarith
  have hB : A + D = (1 : Matrix n n ℝ) -
      (Z.submatrix (fun i : R => i.val) id).transpose * Z.submatrix (fun i : R => i.val) id := by
    dsimp only [A, D]
    rw [row_gram_decomposition Z R]
    abel
  have hposB := hA.add_posSemidef hD
  have h := posDef_logdet_increment_bound A D hA hD (1 - q ^ 2) hgap
    (gram_complement_quadratic_lower Z q hq hZ)
  have hlog : Real.log (gramGaussian Z) -
      Real.log (gramGaussian (Z.submatrix (fun i : R => i.val) id)) =
      (Real.log (A + D).det - Real.log A.det) / 2 := by
    rw [gramGaussian_log Z hA.det_pos]
    rw [gramGaussian_log _ (hB ▸ hposB.det_pos)]
    rw [← hB]
    dsimp only [A]
    ring
  rw [hlog]
  constructor
  · exact div_nonneg h.1 (by norm_num)
  · have h' := div_le_div_of_nonneg_right h.2 (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [D, row_deleted_gram_trace, div_div, mul_comm] using h'

set_option maxHeartbeats 1000000 in
omit [DecidableEq m] in
theorem row_submatrix_opNorm_le (Z : Matrix m n ℝ) (R : Finset m) :
    ‖Z.submatrix (fun i : R => i.val) id‖ ≤ ‖Z‖ := by
  classical
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Z) ?_
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have h := pow_le_pow_left₀ (norm_nonneg _) (Matrix.l2_opNorm_mulVec Z v) 2
  rw [mul_pow] at h
  have hsubset : (∑ i : R, (Z *ᵥ v) i.val ^ 2) ≤ ∑ i, (Z *ᵥ v) i ^ 2 := by
    simp only [Finset.univ_eq_attach]
    rw [Finset.sum_attach R (fun i => (Z *ᵥ v) i ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
      (fun i _ _ => sq_nonneg _)
  have hsq : ‖((Matrix.toEuclideanLin (𝕜 := ℝ)).trans LinearMap.toContinuousLinearMap
      (Z.submatrix (fun i : R => i.val) id)) v‖ ^ 2 =
      ∑ i : R, (Z *ᵥ v) i.val ^ 2 := by
    change ‖WithLp.toLp 2 ((Z.submatrix (fun i : R => i.val) id) *ᵥ v)‖ ^ 2 = _
    simp [EuclideanSpace.norm_sq_eq, Matrix.mulVec, dotProduct, Real.norm_eq_abs, sq_abs]
  rw [hsq, mul_pow]
  apply hsubset.trans
  simpa [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using h

theorem gramGaussian_column_deletion_bound (Z : Matrix m n ℝ) (C : Finset n)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) :
    0 ≤ Real.log (gramGaussian Z) -
      Real.log (gramGaussian (Z.submatrix id (fun j : C => j.val))) ∧
    Real.log (gramGaussian Z) -
      Real.log (gramGaussian (Z.submatrix id (fun j : C => j.val))) ≤
      (∑ j : (Cᶜ : Finset n), ∑ i, Z i j.val ^ 2) / (2 * (1 - q ^ 2)) := by
  have ht : ‖Z.transpose‖ ≤ q := by
    simpa only [← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.l2_opNorm_conjTranspose] using hZ
  have h := gramGaussian_row_deletion_bound Z.transpose C q hq hq1 ht
  rw [gramGaussian_transpose] at h
  have heq : Z.transpose.submatrix (fun j : C => j.val) id =
      (Z.submatrix id (fun j : C => j.val)).transpose := by ext i j; rfl
  rw [heq, gramGaussian_transpose] at h
  exact h

theorem gramGaussian_deletion_bound (Z : Matrix m n ℝ) (R : Finset m) (C : Finset n)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) :
    0 ≤ Real.log (gramGaussian Z) -
      Real.log (gramGaussian (Z.submatrix (fun i : R => i.val) (fun j : C => j.val))) ∧
    Real.log (gramGaussian Z) -
      Real.log (gramGaussian (Z.submatrix (fun i : R => i.val) (fun j : C => j.val))) ≤
      ((∑ i : (Rᶜ : Finset m), ∑ j, Z i.val j ^ 2) +
        ∑ j : (Cᶜ : Finset n), ∑ i, Z i j.val ^ 2) / (2 * (1 - q ^ 2)) := by
  classical
  let W := Z.submatrix (fun i : R => i.val) id
  have hr := gramGaussian_row_deletion_bound Z R q hq hq1 hZ
  have hc := gramGaussian_column_deletion_bound W C q hq hq1
    ((row_submatrix_opNorm_le Z R).trans hZ)
  have heq : W.submatrix id (fun j : C => j.val) =
      Z.submatrix (fun i : R => i.val) (fun j : C => j.val) := by ext i j; rfl
  rw [heq] at hc
  have hmass : (∑ j : (Cᶜ : Finset n), ∑ i : R, W i j.val ^ 2) ≤
      ∑ j : (Cᶜ : Finset n), ∑ i, Z i j.val ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    change (∑ i : R, Z i.val j.val ^ 2) ≤ ∑ i, Z i j.val ^ 2
    simp only [Finset.univ_eq_attach]
    rw [Finset.sum_attach R (fun i => Z i j.val ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
      (fun i _ _ => sq_nonneg _)
  have hd : 0 < 2 * (1 - q ^ 2) := by nlinarith
  have hmass' := div_le_div_of_nonneg_right hmass hd.le
  constructor
  · dsimp only [W] at hc
    linarith [hr.1, hc.1]
  · rw [add_div]
    dsimp only [W] at hc
    linarith [hr.2, hc.2]

end RealMatrices

end TournamentHamiltonian
