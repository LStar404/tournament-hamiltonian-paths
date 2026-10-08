import TournamentHamiltonian.SkewOperatorNorm

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem euclidean_complex_norm_sq_split (x : EuclideanSpace ℂ ι) :
    ‖x‖ ^ 2 = ‖(WithLp.toLp 2 (fun i => (x i).re) : EuclideanSpace ℝ ι)‖ ^ 2 +
      ‖(WithLp.toLp 2 (fun i => (x i).im) : EuclideanSpace ℝ ι)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply, Real.norm_eq_abs, sq_abs, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem real_matrix_complex_mul_re (M : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    (WithLp.toLp 2 (fun i => (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
      (Complex.ofRealHom.mapMatrix M) x i).re) : EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M (WithLp.toLp 2 (fun i => (x i).re)) := by
  apply PiLp.ext
  intro i
  change (∑ j, (M i j : ℂ) * x j).re = ∑ j, M i j * (x j).re
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem real_matrix_complex_mul_im (M : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    (WithLp.toLp 2 (fun i => (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
      (Complex.ofRealHom.mapMatrix M) x i).im) : EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M (WithLp.toLp 2 (fun i => (x i).im)) := by
  apply PiLp.ext
  intro i
  change (∑ j, (M i j : ℂ) * x j).im = ∑ j, M i j * (x j).im
  simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]

theorem complexification_opNorm_le_real (M : Matrix ι ι ℝ) :
    ‖Complex.ofRealHom.mapMatrix M‖ ≤ ‖M‖ := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg M)
  intro x
  have hr := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M).le_opNorm
    (WithLp.toLp 2 (fun i => (x i).re))
  have hi := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M).le_opNorm
    (WithLp.toLp 2 (fun i => (x i).im))
  rw [← Matrix.cstar_norm_def] at hr hi
  have hrs := pow_le_pow_left₀ (norm_nonneg _) hr 2
  have his := pow_le_pow_left₀ (norm_nonneg _) hi 2
  have hnorm : ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Complex.ofRealHom.mapMatrix M) x‖ ^ 2 ≤
      (‖M‖ * ‖x‖) ^ 2 := by
    rw [euclidean_complex_norm_sq_split, real_matrix_complex_mul_re, real_matrix_complex_mul_im]
    rw [mul_pow, euclidean_complex_norm_sq_split x, mul_add]
    simpa only [mul_pow] using add_le_add hrs his
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hnorm

theorem real_matrix_opNorm_eq_complexification (M : Matrix ι ι ℝ) :
    ‖M‖ = ‖Complex.ofRealHom.mapMatrix M‖ :=
  le_antisymm (real_matrix_opNorm_le_complexification M) (complexification_opNorm_le_real M)

end TournamentHamiltonian
