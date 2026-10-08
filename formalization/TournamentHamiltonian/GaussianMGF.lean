import TournamentHamiltonian.GaussianWick
import TournamentHamiltonian.GramDeletion
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Actual Gaussian conditional integration and the determinant generating factor. -/

namespace TournamentHamiltonian

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

theorem gaussian_quadratic_integral (a : ℝ) (ha : a < 1) :
    (∫ x : ℝ, Real.exp (a * x ^ 2 / 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - a))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hfun (x : ℝ) : gaussianPDFReal 0 1 x • Real.exp (a * x ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 - a) / 2) * x ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hfun]
  rw [integral_const_mul, integral_gaussian]
  rw [mul_comm, ← div_eq_mul_inv, ← Real.sqrt_div (by positivity : 0 ≤ Real.pi / ((1 - a) / 2))]
  rw [← Real.sqrt_inv]
  congr 1
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h1a : 1 - a ≠ 0 := ne_of_gt (sub_pos.mpr ha)
  field_simp

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ]

theorem standardGaussian_linear_exp_integral (v : ι → ℝ) :
    (∫ x : ι → ℝ, Real.exp (∑ i : ι, v i * x i)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) = Real.exp ((∑ i : ι, (v i) ^ 2) / 2) := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun (i : ι) (s : ℝ) => Real.exp (v i * s))]
  have hi (i : ι) : (∫ x : ℝ, Real.exp (v i * x) ∂gaussianReal 0 1) =
      Real.exp ((v i) ^ 2 / 2) := by
    have h := mgf_gaussianReal (μ := 0) (v := 1) (X := id)
      (p := gaussianReal 0 1) (by simp) (v i)
    simpa [mgf, NNReal.coe_one] using h
  simp_rw [hi]
  rw [← Real.exp_sum, Finset.sum_div]

noncomputable def gaussianBilinearMGF (Z : Matrix ι ρ ℝ) (t : ℝ) : ℝ :=
  ∫ x : ι → ℝ, ∫ y : ρ → ℝ,
    Real.exp (t * (∑ a : ι, ∑ b : ρ, x a * Z a b * y b))
      ∂Measure.pi (fun _ => gaussianReal 0 1)
    ∂Measure.pi (fun _ => gaussianReal 0 1)

theorem gaussianBilinearMGF_conditional (Z : Matrix ι ρ ℝ) (t : ℝ) :
    gaussianBilinearMGF Z t =
      ∫ x : ι → ℝ, Real.exp ((∑ b : ρ, (t * ∑ a : ι, x a * Z a b) ^ 2) / 2)
        ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  unfold gaussianBilinearMGF
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have he (y : ρ → ℝ) : t * (∑ a : ι, ∑ b : ρ, x a * Z a b * y b) =
      ∑ b : ρ, (t * ∑ a : ι, x a * Z a b) * y b := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_assoc t (∑ a : ι, x a * Z a b) (y b), Finset.sum_mul, Finset.mul_sum]
  simp_rw [he]
  exact standardGaussian_linear_exp_integral _

theorem hermitian_quadratic_eigenbasis {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x : ι → ℝ) :
    inner ℝ (∑ i : ι, x i • hA.eigenvectorBasis i)
      (Matrix.toEuclideanLin A (∑ i : ι, x i • hA.eigenvectorBasis i)) =
        ∑ i : ι, hA.eigenvalues i * (x i) ^ 2 := by
  have he (i : ι) : Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext a
    exact congrFun (hA.mulVec_eigenvectorBasis i) a
  rw [map_sum]
  simp_rw [map_smul, he, smul_smul, inner_sum, real_inner_smul_right,
    hA.eigenvectorBasis.orthonormal.inner_left_fintype]
  simp only [starRingEnd_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hermitian_one_sub_det {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    ((1 : Matrix ι ι ℝ) - A).det = ∏ i : ι, (1 - hA.eigenvalues i) := by
  have he : (1 : Matrix ι ι ℝ) - A =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (1 - Matrix.diagonal hA.eigenvalues) := by
    rw [map_sub, map_one]
    simpa using
      congrArg (fun X : Matrix ι ι ℝ => 1 - X) hA.spectral_theorem
  rw [he, Unitary.conjStarAlgAut_apply, Matrix.det_mul_right_comm,
    ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul]
  have hd : (1 : Matrix ι ι ℝ) - Matrix.diagonal hA.eigenvalues =
      Matrix.diagonal (fun i => 1 - hA.eigenvalues i) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub]
  rw [hd, Matrix.det_diagonal]

/-- The actual Gaussian quadratic integral for arbitrary Hermitian matrices, including zero eigenvalues. -/
theorem hermitian_gaussian_quadratic_integral {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hEig : ∀ i : ι, hA.eigenvalues i < 1) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (inner ℝ x (Matrix.toEuclideanLin A x) / 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) =
        (Real.sqrt ((1 : Matrix ι ι ℝ) - A).det)⁻¹ := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis hA.eigenvectorBasis]
  rw [integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simp_rw [hermitian_quadratic_eigenbasis, Finset.sum_div, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod
    (fun (i : ι) (s : ℝ) => Real.exp (hA.eigenvalues i * s ^ 2 / 2))]
  simp_rw [gaussian_quadratic_integral _ (hEig _)]
  rw [Finset.prod_inv_distrib, ← Real.sqrt_prod _ (fun i _ => (sub_pos.mpr (hEig i)).le),
    ← hermitian_one_sub_det hA]

theorem hermitian_eigenvalues_lt_one_of_complement_posDef {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hpos : ((1 : Matrix ι ι ℝ) - A).PosDef) (i : ι) :
    hA.eigenvalues i < 1 := by
  let b : EuclideanSpace ℝ ι := hA.eigenvectorBasis i
  have hbne : (b : ι → ℝ) ≠ 0 := by
    intro h
    have hb0 : b = 0 := by ext a; exact congrFun h a
    exact hA.eigenvectorBasis.orthonormal.ne_zero i hb0
  have hb : dotProduct (b : ι → ℝ) (b : ι → ℝ) = 1 := by
    have hn := hA.eigenvectorBasis.orthonormal.1 i
    have hi : inner ℝ b b = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hi
  have h := hpos.dotProduct_mulVec_pos hbne
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    hA.mulVec_eigenvectorBasis i, dotProduct_smul] at h
  have hh : 0 < 1 - hA.eigenvalues i := by
    have hb' : dotProduct (b : ι → ℝ) (hA.eigenvectorBasis i : ι → ℝ) = 1 := hb
    simpa only [star_trivial, hb, hb', smul_eq_mul, mul_one] using h
  exact sub_pos.mp hh

theorem hermitian_gaussian_quadratic_integral_posDef {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hpos : ((1 : Matrix ι ι ℝ) - A).PosDef) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (inner ℝ x (Matrix.toEuclideanLin A x) / 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) =
        (Real.sqrt ((1 : Matrix ι ι ℝ) - A).det)⁻¹ :=
  hermitian_gaussian_quadratic_integral hA
    (hermitian_eigenvalues_lt_one_of_complement_posDef hA hpos)

theorem gaussianBilinearMGF_eq_gramGaussian {Z : Matrix ι ρ ℝ}
    (hpos : ((1 : Matrix ι ι ℝ) - Z * Z.transpose).PosDef) :
    gaussianBilinearMGF Z 1 = gramGaussian Z := by
  rw [gaussianBilinearMGF_conditional]
  simp only [one_mul]
  have hquad (x : ι → ℝ) :
      (∑ b : ρ, (∑ a : ι, x a * Z a b) ^ 2) =
        inner ℝ (WithLp.toLp 2 x) (Matrix.toEuclideanLin (Z * Z.transpose) (WithLp.toLp 2 x)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    change _ = dotProduct ((Z * Z.transpose) *ᵥ x) x
    rw [dotProduct_comm]
    have hr := real_gram_quadratic Z.transpose x
    rw [Matrix.transpose_transpose] at hr
    rw [hr]
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [hquad]
  have him :
      (∫ x : ι → ℝ, Real.exp (inner ℝ (WithLp.toLp 2 x)
        (Matrix.toEuclideanLin (Z * Z.transpose) (WithLp.toLp 2 x)) / 2)
          ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ x : EuclideanSpace ℝ ι, Real.exp (inner ℝ x
        (Matrix.toEuclideanLin (Z * Z.transpose) x) / 2) ∂stdGaussian (EuclideanSpace ℝ ι) := by
    rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  rw [him, hermitian_gaussian_quadratic_integral_posDef _ hpos]
  · rw [gramGaussian, Matrix.det_one_sub_mul_comm]
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_conjTranspose_self Z

theorem gaussianBilinearMGF_smul (Z : Matrix ι ρ ℝ) (t : ℝ) :
    gaussianBilinearMGF Z t = gaussianBilinearMGF (t • Z) 1 := by
  have he (x : ι → ℝ) (y : ρ → ℝ) :
      t * (∑ a : ι, ∑ b : ρ, x a * Z a b * y b) =
        ∑ a : ι, ∑ b : ρ, x a * (t • Z) a b * y b := by
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [gaussianBilinearMGF, one_mul, he]

/-- The actual bilinear Gaussian MGF on precisely the singular-value gap domain. -/
theorem gaussianBilinearMGF_eq_gramGaussian_smul (Z : Matrix ι ρ ℝ) (t : ℝ)
    (hgap : |t| * ‖Z‖ < 1) :
    gaussianBilinearMGF Z t = gramGaussian (t • Z) := by
  rw [gaussianBilinearMGF_smul]
  have hn : ‖t • Z‖ < 1 := by simpa only [norm_smul, Real.norm_eq_abs] using hgap
  have hnt : ‖(t • Z).transpose‖ ≤ ‖t • Z‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
  have hp := gram_complement_posDef (t • Z).transpose ‖t • Z‖ (norm_nonneg _) hn hnt
  rw [Matrix.transpose_transpose] at hp
  exact gaussianBilinearMGF_eq_gramGaussian hp

theorem gaussian_quadratic_integrable (a : ℝ) (ha : a < 1) :
    Integrable (fun x : ℝ => Real.exp (a * x ^ 2 / 2)) (gaussianReal 0 1) := by
  by_contra h
  have hi := gaussian_quadratic_integral a ha
  rw [integral_undef h] at hi
  have hs : Real.sqrt (1 - a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr ha))
  exact (inv_ne_zero hs) hi.symm

theorem standardGaussian_quadratic_product_integrable (a : ℝ) (ha : a < 1) :
    Integrable (fun x : ι → ℝ => Real.exp (a * (∑ i : ι, x i ^ 2) / 2))
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have he (x : ι → ℝ) : Real.exp (a * (∑ i : ι, x i ^ 2) / 2) =
      ∏ i : ι, Real.exp (a * x i ^ 2 / 2) := by
    rw [Finset.mul_sum, Finset.sum_div, Real.exp_sum]
  simp_rw [he]
  exact Integrable.fintype_prod (fun _ => gaussian_quadratic_integrable a ha)

end TournamentHamiltonian
