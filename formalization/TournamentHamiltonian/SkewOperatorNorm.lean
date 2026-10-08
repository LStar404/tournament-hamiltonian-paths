import TournamentHamiltonian.SkewSpectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix.Norms.L2Operator

namespace TournamentHamiltonian

/-- The Euclidean operator norm of the actual normalized skew matrix,
acting on complex vectors. -/
noncomputable def normalizedSkewOpNorm {n : ℕ} (T : Tournament n) : ℝ :=
  ‖((1 : ℂ) / n) • complexSignMatrix T‖

private theorem norm_unitary_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    ‖Unitary.conjStarAlgAut ℂ _ U M‖ = ‖M‖ := by
  rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul]

theorem normalizedSkew_unitary_diagonalization {n : ℕ} (T : Tournament n) :
    ((1 : ℂ) / n) • complexSignMatrix T =
      Unitary.conjStarAlgAut ℂ _ (skewHermitian_isHermitian T).eigenvectorUnitary
        (Matrix.diagonal (fun i => -Complex.I * ((skewFrequency T i : ℂ) / n))) := by
  conv_lhs => rw [complexSignMatrix_unitary_diagonalization, ← map_smul]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal]
    ring
  · simp [Matrix.diagonal, hij]

theorem normalizedSkewOpNorm_le_sqrt_pairedSum {n : ℕ} (T : Tournament n) :
    normalizedSkewOpNorm T ≤ Real.sqrt (pairedMasses T).sum := by
  rw [normalizedSkewOpNorm, normalizedSkew_unitary_diagonalization,
    norm_unitary_conjugation, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_div,
    Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs]
  have h := skewFrequency_normalized_sq_le_pairedSum T i
  have hs : 0 ≤ (pairedMasses T).sum := List.sum_nonneg (pairedMasses_nonneg T)
  have hsq := Real.sq_sqrt hs
  have hn : 0 < (n : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hdiv : (|skewFrequency T i| / (n : ℝ)) ^ 2 = skewFrequency T i ^ 2 / (n : ℝ) ^ 2 := by
    rw [div_pow, sq_abs]
  have hpos : 0 ≤ |skewFrequency T i| / (n : ℝ) := by positivity
  nlinarith [Real.sqrt_nonneg (pairedMasses T).sum]

/-- The exact generic gap used before the stronger cotangent cap. -/
theorem normalizedSkewOpNorm_sq_le {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    normalizedSkewOpNorm T ^ 2 ≤ (n - 1 : ℝ) / (2 * n) := by
  have h := normalizedSkewOpNorm_le_sqrt_pairedSum T
  have hs : 0 ≤ (pairedMasses T).sum := List.sum_nonneg (pairedMasses_nonneg T)
  have hnorm : 0 ≤ normalizedSkewOpNorm T := norm_nonneg _
  have hsqrt := Real.sq_sqrt hs
  rw [← pairedMasses_sum T hn]
  nlinarith [Real.sqrt_nonneg (pairedMasses T).sum]

theorem normalizedSkewOpNorm_sq_lt_half {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    normalizedSkewOpNorm T ^ 2 < 1 / 2 := by
  have h := normalizedSkewOpNorm_sq_le T hn
  have hs := pairedMasses_sum_lt_half T hn
  rw [pairedMasses_sum T hn] at hs
  exact h.trans_lt hs

private def complexifyVector {ι : Type*} (x : EuclideanSpace ℝ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => (x i : ℂ))

private theorem complexifyVector_norm {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖complexifyVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, complexifyVector, Complex.norm_real]

private theorem complexifyVector_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    complexifyVector (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M x) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Complex.ofRealHom.mapMatrix M) (complexifyVector x) := by
  apply PiLp.ext
  intro i
  change ((∑ j, M i j * x j : ℝ) : ℂ) = _
  simp [complexifyVector, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct,
    RingHom.mapMatrix_apply]

set_option maxHeartbeats 1000000 in
theorem real_matrix_opNorm_le_complexification {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : ‖M‖ ≤ ‖Complex.ofRealHom.mapMatrix M‖ := by
  rw [Matrix.cstar_norm_def (n := ι) (𝕜 := ℝ) M]
  apply ContinuousLinearMap.opNorm_le_bound
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) (norm_nonneg _)
  intro x
  calc
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M x‖ =
        ‖complexifyVector (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M x)‖ :=
      (complexifyVector_norm _).symm
    _ = ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Complex.ofRealHom.mapMatrix M) (complexifyVector x)‖ := by
      rw [complexifyVector_mul]
    _ ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Complex.ofRealHom.mapMatrix M)‖ * ‖complexifyVector x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by
      rw [← Matrix.cstar_norm_def (n := ι) (𝕜 := ℂ) (Complex.ofRealHom.mapMatrix M),
        complexifyVector_norm]

noncomputable def normalizedRealSkewOpNorm {n : ℕ} (T : Tournament n) : ℝ :=
  ‖((1 : ℝ) / n) • signMatrix T‖

theorem normalizedRealSkewOpNorm_le_complex {n : ℕ} (T : Tournament n) :
    normalizedRealSkewOpNorm T ≤ normalizedSkewOpNorm T := by
  have hmap : Complex.ofRealHom.mapMatrix (((1 : ℝ) / n) • signMatrix T) =
      ((1 : ℂ) / n) • complexSignMatrix T := by
    ext i j
    simp [RingHom.mapMatrix_apply, complexSignMatrix]
  have h := real_matrix_opNorm_le_complexification (((1 : ℝ) / n) • signMatrix T)
  rwa [hmap] at h

theorem normalizedRealSkewOpNorm_sq_le {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    normalizedRealSkewOpNorm T ^ 2 ≤ (n - 1 : ℝ) / (2 * n) := by
  have h := normalizedRealSkewOpNorm_le_complex T
  have hc := normalizedSkewOpNorm_sq_le T hn
  have hreal : 0 ≤ normalizedRealSkewOpNorm T := norm_nonneg _
  have hcomplex : 0 ≤ normalizedSkewOpNorm T := norm_nonneg _
  nlinarith

theorem normalizedRealSkewOpNorm_sq_lt_half {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    normalizedRealSkewOpNorm T ^ 2 < 1 / 2 := by
  have h := normalizedRealSkewOpNorm_sq_le T hn
  have hs := pairedMasses_sum_lt_half T hn
  rw [pairedMasses_sum T hn] at hs
  exact h.trans_lt hs

theorem skewGram_eq_identity_sub_normalized_gram {n : ℕ} (T : Tournament n) :
    skewGram T = 1 -
      ((((1 : ℝ) / n) • signMatrix T).transpose * (((1 : ℝ) / n) • signMatrix T)) := by
  simp only [skewGram, Matrix.transpose_smul, smul_mul_assoc, Matrix.mul_smul,
    smul_smul]
  congr 2
  simp [pow_two]

theorem skewGram_quadratic_eq {n : ℕ} (T : Tournament n)
    (x : EuclideanSpace ℝ (Fin n)) :
    dotProduct x ((skewGram T).mulVec x) = ‖x‖ ^ 2 -
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (((1 : ℝ) / n) • signMatrix T) x‖ ^ 2 := by
  rw [skewGram_eq_identity_sub_normalized_gram, Matrix.sub_mulVec, Matrix.one_mulVec,
    dotProduct_sub, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  simp only [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, Matrix.ofLp_toEuclideanCLM, Matrix.smul_mulVec, pow_two]

/-- A uniform lower quadratic bound for the actual Gaussian Gram matrix. -/
theorem skewGram_quadratic_lower_bound {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ dotProduct x ((skewGram T).mulVec x) := by
  rw [skewGram_quadratic_eq]
  have hnorm : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (((1 : ℝ) / n) • signMatrix T) x‖ ≤ normalizedRealSkewOpNorm T * ‖x‖ := by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM, normalizedRealSkewOpNorm] using
      (ContinuousLinearMap.le_opNorm
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
          (((1 : ℝ) / n) • signMatrix T)) x)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [mul_pow] at hsquare
  have hcap := normalizedRealSkewOpNorm_sq_lt_half T hn
  have hmul := mul_le_mul_of_nonneg_right hcap.le (sq_nonneg ‖x‖)
  linarith

theorem skewGram_isHermitian {n : ℕ} (T : Tournament n) : (skewGram T).IsHermitian := by
  rw [skewGram_eq_identity_sub_normalized_gram]
  apply Matrix.isHermitian_one.sub
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_self (((1 : ℝ) / n) • signMatrix T)

theorem skewGram_quadraticPositive {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    QuadraticPositive (skewGram T) := by
  intro x hx
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have hy : y ≠ 0 := by
    intro h
    apply hx
    have he := congrArg WithLp.ofLp h
    simpa [y] using he
  have hypos : 0 < ‖y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hy)
  have h := skewGram_quadratic_lower_bound T hn y
  change (1 / 2 : ℝ) * ‖y‖ ^ 2 ≤ dotProduct x ((skewGram T).mulVec x) at h
  linarith

theorem skewGram_posDef {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    (skewGram T).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (skewGram_isHermitian T)
  intro x hx
  simpa only [star_trivial] using skewGram_quadraticPositive T hn x hx

end TournamentHamiltonian
