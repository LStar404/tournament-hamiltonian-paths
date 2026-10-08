import TournamentHamiltonian.GramDeletion

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

section RealProjection

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def rankOneComplement (u : m → ℝ) : Matrix m m ℝ :=
  1 - Matrix.vecMulVec u u

omit [Fintype m] in
theorem rankOneComplement_transpose (u : m → ℝ) :
    (rankOneComplement u).transpose = rankOneComplement u := by
  simp [rankOneComplement, Matrix.transpose_vecMulVec]

theorem rankOneComplement_mulVec (u x : m → ℝ) :
    rankOneComplement u *ᵥ x = fun i => x i - u i * dotProduct u x := by
  rw [rankOneComplement, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp [mul_comm]

theorem rankOneComplement_action_sq (u x : m → ℝ) (hu : (∑ i, u i ^ 2) = 1) :
    (∑ i, (rankOneComplement u *ᵥ x) i ^ 2) =
      (∑ i, x i ^ 2) - dotProduct u x ^ 2 := by
  rw [rankOneComplement_mulVec]
  have hexpand : (∑ i, (x i - u i * dotProduct u x) ^ 2) =
      (∑ i, x i ^ 2) - 2 * dotProduct u x * (∑ i, u i * x i) +
        dotProduct u x ^ 2 * (∑ i, u i ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hexpand, hu]
  simp only [dotProduct]
  ring

theorem rankOneComplement_opNorm_le_one (u : m → ℝ) (hu : (∑ i, u i ^ 2) = 1) :
    ‖rankOneComplement u‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro v
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Matrix.toEuclideanCLM_toLp]
  have h := rankOneComplement_action_sq u (fun i => v i) hu
  simpa [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using
    h.le.trans (sub_le_self _ (sq_nonneg _))

theorem rankOneComplement_idempotent (u : m → ℝ) (hu : (∑ i, u i ^ 2) = 1) :
    rankOneComplement u * rankOneComplement u = rankOneComplement u := by
  have hdot : dotProduct u u = 1 := by simpa [dotProduct, pow_two] using hu
  have houter : Matrix.vecMulVec u u * Matrix.vecMulVec u u = Matrix.vecMulVec u u := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hdot, one_smul]
  simp only [rankOneComplement, sub_mul, mul_sub, one_mul, mul_one, houter]
  abel

omit [Fintype n] [DecidableEq n] in
theorem rankOneComplement_left_gram_difference (Z : Matrix m n ℝ) (u : m → ℝ)
    (hu : (∑ i, u i ^ 2) = 1) :
    Z.transpose * Z - (rankOneComplement u * Z).transpose * (rankOneComplement u * Z) =
      Matrix.vecMulVec (Z.transpose *ᵥ u) (Z.transpose *ᵥ u) := by
  have houter : Z.transpose * Matrix.vecMulVec u u * Z =
      Matrix.vecMulVec (Z.transpose *ᵥ u) (Z.transpose *ᵥ u) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    have huv : u ᵥ* Z = Z.transpose *ᵥ u := by
      simpa only [Matrix.transpose_transpose] using Matrix.vecMul_transpose Z.transpose u
    rw [huv]
  rw [Matrix.transpose_mul, rankOneComplement_transpose, ← Matrix.mul_assoc,
    Matrix.mul_assoc Z.transpose, rankOneComplement_idempotent u hu]
  rw [rankOneComplement, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  rw [houter]
  abel

omit [DecidableEq n] in
theorem vecMulVec_self_posSemidef (v : n → ℝ) :
    (Matrix.vecMulVec v v).PosSemidef := by
  have heq : Matrix.vecMulVec v v =
      (Matrix.replicateRow Unit v).transpose * Matrix.replicateRow Unit v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.replicateRow, Matrix.transpose_apply, Matrix.vecMulVec]
  rw [heq]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (Matrix.replicateRow Unit v)

omit [DecidableEq n] in
theorem vecMulVec_self_trace (v : n → ℝ) :
    (Matrix.vecMulVec v v).trace = ∑ i, v i ^ 2 := by
  simp [Matrix.trace, Matrix.diag, Matrix.vecMulVec, pow_two]

theorem rankOneComplement_left_opNorm_le (Z : Matrix m n ℝ) (u : m → ℝ)
    (hu : (∑ i, u i ^ 2) = 1) : ‖rankOneComplement u * Z‖ ≤ ‖Z‖ := by
  calc
    _ ≤ ‖rankOneComplement u‖ * ‖Z‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * ‖Z‖ := mul_le_mul_of_nonneg_right (rankOneComplement_opNorm_le_one u hu) (norm_nonneg _)
    _ = _ := one_mul _

theorem gramGaussian_left_projection_bound (Z : Matrix m n ℝ) (u : m → ℝ)
    (hu : (∑ i, u i ^ 2) = 1) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) :
    0 ≤ Real.log (gramGaussian Z) - Real.log (gramGaussian (rankOneComplement u * Z)) ∧
      Real.log (gramGaussian Z) - Real.log (gramGaussian (rankOneComplement u * Z)) ≤
        (∑ j, (Z.transpose *ᵥ u) j ^ 2) / (2 * (1 - q ^ 2)) := by
  let A : Matrix n n ℝ := 1 - Z.transpose * Z
  let D : Matrix n n ℝ := Matrix.vecMulVec (Z.transpose *ᵥ u) (Z.transpose *ᵥ u)
  have hA : A.PosDef := gram_complement_posDef Z q hq hq1 hZ
  have hD : D.PosSemidef := vecMulVec_self_posSemidef _
  have hgap : 0 < 1 - q ^ 2 := by nlinarith
  have hB : A + D = (1 : Matrix n n ℝ) -
      (rankOneComplement u * Z).transpose * (rankOneComplement u * Z) := by
    dsimp only [A, D]
    rw [← rankOneComplement_left_gram_difference Z u hu]
    abel
  have hposB := hA.add_posSemidef hD
  have h := posDef_logdet_increment_bound A D hA hD (1 - q ^ 2) hgap
    (gram_complement_quadratic_lower Z q hq hZ)
  have hlog : Real.log (gramGaussian Z) - Real.log (gramGaussian (rankOneComplement u * Z)) =
      (Real.log (A + D).det - Real.log A.det) / 2 := by
    rw [gramGaussian_log Z hA.det_pos,
      gramGaussian_log _ (hB ▸ hposB.det_pos), ← hB]
    dsimp only [A]
    ring
  rw [hlog]
  constructor
  · exact div_nonneg h.1 (by norm_num)
  · have h' := div_le_div_of_nonneg_right h.2 (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [D, vecMulVec_self_trace, div_div, mul_comm] using h'

theorem gramGaussian_right_projection_bound (Z : Matrix m n ℝ) (v : n → ℝ)
    (hv : (∑ j, v j ^ 2) = 1) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) :
    0 ≤ Real.log (gramGaussian Z) - Real.log (gramGaussian (Z * rankOneComplement v)) ∧
      Real.log (gramGaussian Z) - Real.log (gramGaussian (Z * rankOneComplement v)) ≤
        (∑ i, (Z *ᵥ v) i ^ 2) / (2 * (1 - q ^ 2)) := by
  have ht : ‖Z.transpose‖ ≤ q := by
    simpa only [← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.l2_opNorm_conjTranspose] using hZ
  have h := gramGaussian_left_projection_bound Z.transpose v hv q hq hq1 ht
  have heq : rankOneComplement v * Z.transpose = (Z * rankOneComplement v).transpose := by
    rw [Matrix.transpose_mul, rankOneComplement_transpose]
  rw [heq, gramGaussian_transpose, gramGaussian_transpose, Matrix.transpose_transpose] at h
  exact h

/-- Two-sided centering along arbitrary unit directions. The cost of the
second projection is bounded using the original kernel's action. -/
theorem gramGaussian_two_projection_bound (Z : Matrix m n ℝ) (u : m → ℝ) (v : n → ℝ)
    (hu : (∑ i, u i ^ 2) = 1) (hv : (∑ j, v j ^ 2) = 1)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) :
    0 ≤ Real.log (gramGaussian Z) - Real.log (gramGaussian (rankOneComplement u * Z * rankOneComplement v)) ∧
      Real.log (gramGaussian Z) - Real.log (gramGaussian (rankOneComplement u * Z * rankOneComplement v)) ≤
        ((∑ j, (Z.transpose *ᵥ u) j ^ 2) + (∑ i, (Z *ᵥ v) i ^ 2)) / (2 * (1 - q ^ 2)) := by
  have hl := gramGaussian_left_projection_bound Z u hu q hq hq1 hZ
  have hr := gramGaussian_right_projection_bound (rankOneComplement u * Z) v hv q hq hq1
    ((rankOneComplement_left_opNorm_le Z u hu).trans hZ)
  have hmass : (∑ i, ((rankOneComplement u * Z) *ᵥ v) i ^ 2) ≤ ∑ i, (Z *ᵥ v) i ^ 2 := by
    rw [← Matrix.mulVec_mulVec, rankOneComplement_action_sq u _ hu]
    exact sub_le_self _ (sq_nonneg _)
  have hd : 0 ≤ 2 * (1 - q ^ 2) := by nlinarith
  have hm := div_le_div_of_nonneg_right hmass hd
  constructor
  · linarith [hl.1, hr.1]
  · rw [add_div]
    linarith [hl.2, hr.2]

noncomputable def flatUnitVector (ι : Type*) [Fintype ι] : ι → ℝ :=
  fun _ => (Real.sqrt (Fintype.card ι : ℝ))⁻¹

theorem flatUnitVector_sum_sq (ι : Type*) [Fintype ι] (hn : 0 < Fintype.card ι) :
    (∑ i, flatUnitVector ι i ^ 2) = 1 := by
  have hnR : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hn
  simp only [flatUnitVector, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact mul_inv_cancel₀ hnR.ne'

noncomputable def centeringProjection (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℝ :=
  rankOneComplement (flatUnitVector ι)

theorem centeringProjection_eq (ι : Type*) [Fintype ι] [DecidableEq ι] :
    centeringProjection ι = (1 : Matrix ι ι ℝ) -
      ((Fintype.card ι : ℝ)⁻¹) • Matrix.of (fun _ _ => (1 : ℝ)) := by
  ext i j
  simp only [centeringProjection, rankOneComplement, Matrix.sub_apply, Matrix.vecMulVec_apply,
    flatUnitVector, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, mul_one]
  rw [← mul_inv_rev, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The manuscript's centering estimate for any rectangular kernel;
each side is projected off its own normalized all-one direction. -/
theorem gramGaussian_centering_bound (Z : Matrix m n ℝ)
    (hm : 0 < Fintype.card m) (hn : 0 < Fintype.card n)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) :
    0 ≤ Real.log (gramGaussian Z) - Real.log (gramGaussian (centeringProjection m * Z * centeringProjection n)) ∧
      Real.log (gramGaussian Z) - Real.log (gramGaussian (centeringProjection m * Z * centeringProjection n)) ≤
        ((∑ j, (Z.transpose *ᵥ flatUnitVector m) j ^ 2) +
          (∑ i, (Z *ᵥ flatUnitVector n) i ^ 2)) / (2 * (1 - q ^ 2)) :=
  gramGaussian_two_projection_bound Z (flatUnitVector m) (flatUnitVector n)
    (flatUnitVector_sum_sq m hm) (flatUnitVector_sum_sq n hn) q hq hq1 hZ

end RealProjection

end TournamentHamiltonian
