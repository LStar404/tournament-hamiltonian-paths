import TournamentHamiltonian.ProjectionPermanentEnvelope

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem unit_column_projection_idempotent (U : Matrix ι Unit ℂ)
    (hU : U.conjTranspose * U = 1) :
    (U * U.conjTranspose) * (U * U.conjTranspose) = U * U.conjTranspose := by
  calc
    _ = U * (U.conjTranspose * U) * U.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU]; simp

/-- The absolute value in polarization is controlled by the true centered
perturbation, without a normality assumption. -/
theorem centered_absolute_permanent_le_exponential (U : Matrix ι Unit ℂ)
    (hU : U.conjTranspose * U = 1) (B : Matrix ι ι ℂ)
    (hPB : (U * U.conjTranspose) * B = 0)
    (hBP : B * (U * U.conjTranspose) = 0) (hp : 0 < Fintype.card ι)
    (z : ℂ) (q C : ℝ) (hgap : ‖B‖ ≤ q) (hC : 0 ≤ C)
    (hL2 : complexFrobeniusSq B ≤ C ^ 2) (hzq : ‖z‖ * q < 1) :
    (CFC.abs (U * U.conjTranspose + z • B)).permanent.re ≤
      (Fintype.card ι).factorial / (Fintype.card ι : ℝ) ^ Fintype.card ι *
        Real.exp (‖z‖ * C * Real.sqrt (Fintype.card ι) / (1 - ‖z‖ * q)) := by
  have hP := Matrix.posSemidef_self_mul_conjTranspose U
  rw [abs_projection_add_smul _ B hP (unit_column_projection_idempotent U hU) hPB hBP z]
  apply rankOne_projection_permanent_le_exponential U hU _
    (Matrix.nonneg_iff_posSemidef.mp (smul_nonneg (norm_nonneg z) (CFC.abs_nonneg B)))
    (by rw [mul_smul_comm, projection_mul_abs_eq_zero _ B hP hBP]; simp)
    hp (‖z‖ * q) (‖z‖ * C) hzq (mul_nonneg (norm_nonneg z) hC)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), CFC.norm_abs]
    exact mul_le_mul_of_nonneg_left hgap (norm_nonneg z)
  · rw [complexFrobeniusSq_real_smul, complexFrobeniusSq_abs, mul_pow]
    exact mul_le_mul_of_nonneg_left hL2 (sq_nonneg ‖z‖)

/-- The actual complex permanent circle majorant for a doubly centered
perturbation of an arbitrary unit rank-one projection. -/
theorem centered_complex_permanent_le_exponential (U : Matrix ι Unit ℂ)
    (hU : U.conjTranspose * U = 1) (B : Matrix ι ι ℂ)
    (hPB : (U * U.conjTranspose) * B = 0)
    (hBP : B * (U * U.conjTranspose) = 0) (hp : 0 < Fintype.card ι)
    (z : ℂ) (q C : ℝ) (hgap : ‖B‖ ≤ q) (hC : 0 ≤ C)
    (hL2 : complexFrobeniusSq B ≤ C ^ 2) (hzq : ‖z‖ * q < 1) :
    ‖(U * U.conjTranspose + z • B).permanent‖ ≤
      (Fintype.card ι).factorial / (Fintype.card ι : ℝ) ^ Fintype.card ι *
        Real.exp (‖z‖ * C * Real.sqrt (Fintype.card ι) / (1 - ‖z‖ * q)) := by
  let Z := U * U.conjTranspose + z • B
  let L := (Fintype.card ι).factorial / (Fintype.card ι : ℝ) ^ Fintype.card ι *
    Real.exp (‖z‖ * C * Real.sqrt (Fintype.card ι) / (1 - ‖z‖ * q))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hleft : (CFC.abs Z).permanent.re ≤ L :=
    centered_absolute_permanent_le_exponential U hU B hPB hBP hp z q C hgap hC hL2 hzq
  have hPB' : (U * U.conjTranspose) * B.conjTranspose = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hBP
  have hBP' : B.conjTranspose * (U * U.conjTranspose) = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hPB
  have hright : (CFC.abs Z.conjTranspose).permanent.re ≤ L := by
    have h := centered_absolute_permanent_le_exponential U hU B.conjTranspose
      hPB' hBP' hp (star z) q C (by simpa only [← Matrix.star_eq_conjTranspose,
        norm_star] using hgap) hC (by rwa [complexFrobeniusSq_conjTranspose])
      (by simpa only [norm_star] using hzq)
    simpa only [Z, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul, norm_star] using h
  have hnonneg : 0 ≤ (CFC.abs Z.conjTranspose).permanent.re :=
    (Complex.nonneg_iff.mp (complex_posSemidef_permanent_nonnegative _
      (complex_abs_posSemidef Z.conjTranspose))).1
  have hsq := complex_permanent_block_cauchy _ Z _ (permanent_polarization_block_posSemidef Z)
  have hprod : (CFC.abs Z.conjTranspose).permanent.re * (CFC.abs Z).permanent.re ≤ L ^ 2 := by
    calc
      _ ≤ L * L := mul_le_mul hright hleft
        (Complex.nonneg_iff.mp (complex_posSemidef_permanent_nonnegative _
          (complex_abs_posSemidef Z))).1 hL
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg Z.permanent) hL).mp (hsq.trans hprod)

end TournamentHamiltonian
