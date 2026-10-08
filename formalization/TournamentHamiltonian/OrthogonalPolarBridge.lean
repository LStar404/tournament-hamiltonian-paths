import TournamentHamiltonian.PolarSpectralBound

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem abs_mul_projection_eq_zero (P B : Matrix ι ι ℂ) (hP : P.PosSemidef)
    (hBP : B * P = 0) : CFC.abs B * P = 0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  have hPs : star P = P := hP.isHermitian.isSelfAdjoint.star_eq
  have hAs : star (CFC.abs B) = CFC.abs B :=
    (complex_abs_posSemidef B).isHermitian.isSelfAdjoint.star_eq
  calc
    star (CFC.abs B * P) * (CFC.abs B * P) = P * (CFC.abs B * CFC.abs B) * P := by
      rw [star_mul, hPs, hAs]
      noncomm_ring
    _ = P * (star B * B) * P := by rw [CFC.abs_mul_abs]
    _ = P * star B * (B * P) := by noncomm_ring
    _ = 0 := by rw [hBP]; simp

theorem projection_mul_abs_eq_zero (P B : Matrix ι ι ℂ) (hP : P.PosSemidef)
    (hBP : B * P = 0) : P * CFC.abs B = 0 := by
  have h := congrArg star (abs_mul_projection_eq_zero P B hP hBP)
  have hPs : star P = P := hP.isHermitian.isSelfAdjoint.star_eq
  have hAs : star (CFC.abs B) = CFC.abs B :=
    (complex_abs_posSemidef B).isHermitian.isSelfAdjoint.star_eq
  simpa only [star_mul, hPs, hAs, star_zero] using h

theorem projection_smul_gram (P B : Matrix ι ι ℂ) (hP : P.PosSemidef)
    (hPP : P * P = P) (hPB : P * B = 0) (_hBP : B * P = 0) (z : ℂ) :
    star (P + z • B) * (P + z • B) = P + (‖z‖ ^ 2) • (star B * B) := by
  have hPs : star P = P := hP.isHermitian.isSelfAdjoint.star_eq
  have hBPs : star B * P = 0 := by
    simpa only [star_mul, hPs, star_zero] using congrArg star hPB
  have hz : z * star z = (‖z‖ ^ 2 : ℝ) := by
    change z * (starRingEnd ℂ) z = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [star_add, star_smul, hPs, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, smul_smul, hPP, hPB, hBPs,
    smul_zero, add_zero, zero_add, hz]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
  rfl

theorem projection_abs_square (P B : Matrix ι ι ℂ) (hP : P.PosSemidef)
    (hPP : P * P = P) (hBP : B * P = 0) (R : ℝ) :
    (P + R • CFC.abs B) * (P + R • CFC.abs B) =
      P + R ^ 2 • (star B * B) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    hPP, abs_mul_projection_eq_zero P B hP hBP,
    projection_mul_abs_eq_zero P B hP hBP, smul_zero, add_zero, zero_add,
    CFC.abs_mul_abs, pow_two]

/-- The manuscript's actual absolute-value identity for a centered perturbation
of a positive orthogonal projection, valid even when the perturbation is singular. -/
theorem abs_projection_add_smul (P B : Matrix ι ι ℂ) (hP : P.PosSemidef)
    (hPP : P * P = P) (hPB : P * B = 0) (hBP : B * P = 0) (z : ℂ) :
    CFC.abs (P + z • B) = P + ‖z‖ • CFC.abs B := by
  rw [CFC.abs, projection_smul_gram P B hP hPP hPB hBP z]
  apply (CFC.sqrt_eq_iff _ _ (by
    rw [← projection_smul_gram P B hP hPP hPB hBP z]
    exact star_mul_self_nonneg _) (add_nonneg hP.nonneg
      (smul_nonneg (norm_nonneg z) (CFC.abs_nonneg B)))).mpr
  exact projection_abs_square P B hP hPP hBP ‖z‖

end TournamentHamiltonian
