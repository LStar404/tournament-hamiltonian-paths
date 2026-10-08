import TournamentHamiltonian.GaussianMGF

/-! The determinant generating factor has the actual bilinear Gaussian moments as derivatives. -/

namespace TournamentHamiltonian

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ]

noncomputable def independentStandardGaussian : Measure ((ι → ℝ) × (ρ → ℝ)) :=
  (Measure.pi (fun _ : ι => gaussianReal 0 1)).prod
    (Measure.pi (fun _ : ρ => gaussianReal 0 1))

noncomputable def gaussianBilinearVariable (Z : Matrix ι ρ ℝ)
    (p : (ι → ℝ) × (ρ → ℝ)) : ℝ :=
  ∑ a : ι, ∑ b : ρ, p.1 a * Z a b * p.2 b

theorem gaussianBilinear_pow_integrable (Z : Matrix ι ρ ℝ) (k : ℕ) :
    Integrable (fun p => gaussianBilinearVariable Z p ^ k) independentStandardGaussian := by
  have hs : Integrable (fun p : (ι → ℝ) × (ρ → ℝ) =>
      ∑ r : Fin k → ι, ∑ c : Fin k → ρ,
        (∏ e : Fin k, Z (r e) (c e)) * (∏ e : Fin k, p.1 (r e)) *
          (∏ e : Fin k, p.2 (c e))) independentStandardGaussian := by
    apply integrable_finsetSum
    intro r _
    apply integrable_finsetSum
    intro c _
    have h := ((standardGaussianTuple_integrable r).mul_prod
      (standardGaussianTuple_integrable c)).const_mul (∏ e : Fin k, Z (r e) (c e))
    change Integrable _ ((Measure.pi (fun _ : ι => gaussianReal 0 1)).prod
      (Measure.pi (fun _ : ρ => gaussianReal 0 1)))
    convert h using 1
    ext p
    ring
  apply hs.congr
  apply ae_of_all
  intro p
  exact (bilinear_pow_coordinate_expansion Z k p.1 p.2).symm

theorem gaussianBilinearMoment_eq_joint_integral (Z : Matrix ι ρ ℝ) (k : ℕ) :
    gaussianBilinearMoment Z k =
      ∫ p, gaussianBilinearVariable Z p ^ k ∂independentStandardGaussian := by
  exact (integral_prod _ (gaussianBilinear_pow_integrable Z k)).symm

theorem gaussianBilinearVariable_eq_inner (Z : Matrix ι ρ ℝ) (p : (ι → ℝ) × (ρ → ℝ)) :
    gaussianBilinearVariable Z p =
      inner ℝ (WithLp.toLp 2 p.1) (Matrix.toEuclideanLin Z (WithLp.toLp 2 p.2)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  change (∑ a : ι, ∑ b : ρ, p.1 a * Z a b * p.2 b) = dotProduct (Z *ᵥ p.2) p.1
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem gaussianBilinearVariable_abs_le (Z : Matrix ι ρ ℝ) (p : (ι → ℝ) × (ρ → ℝ)) :
    |gaussianBilinearVariable Z p| ≤
      ‖(WithLp.toLp 2 p.1 : EuclideanSpace ℝ ι)‖ * ‖Z‖ *
        ‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ ρ)‖ := by
  rw [gaussianBilinearVariable_eq_inner]
  calc
    _ ≤ ‖(WithLp.toLp 2 p.1 : EuclideanSpace ℝ ι)‖ *
        ‖Matrix.toEuclideanLin Z (WithLp.toLp 2 p.2)‖ := abs_real_inner_le_norm _ _
    _ ≤ _ := by
      rw [mul_assoc]
      have hb : ‖Matrix.toEuclideanLin Z (WithLp.toLp 2 p.2)‖ ≤
          ‖Z‖ * ‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ ρ)‖ := by
        rw [Matrix.l2_opNorm_def]
        exact ((Matrix.toEuclideanLin Z).toContinuousLinearMap).le_opNorm _
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

theorem gaussianBilinearVariable_young_bound (Z : Matrix ι ρ ℝ) (t : ℝ)
    (p : (ι → ℝ) × (ρ → ℝ)) :
    t * gaussianBilinearVariable Z p ≤
      (|t| * ‖Z‖) * ((∑ a : ι, p.1 a ^ 2) + (∑ b : ρ, p.2 b ^ 2)) / 2 := by
  let nx : ℝ := ‖(WithLp.toLp 2 p.1 : EuclideanSpace ℝ ι)‖
  let ny : ℝ := ‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ ρ)‖
  have hy : nx * ny ≤ (nx ^ 2 + ny ^ 2) / 2 := by nlinarith [sq_nonneg (nx - ny)]
  have ha : 0 ≤ |t| * ‖Z‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hb := mul_le_mul_of_nonneg_left (gaussianBilinearVariable_abs_le Z p) (abs_nonneg t)
  have hh := mul_le_mul_of_nonneg_left hy ha
  have ht : t * gaussianBilinearVariable Z p ≤ |t| * |gaussianBilinearVariable Z p| := by
    rw [← abs_mul]
    exact le_abs_self _
  have h : t * gaussianBilinearVariable Z p ≤ (|t| * ‖Z‖) * (nx ^ 2 + ny ^ 2) / 2 := by
    calc
      _ ≤ |t| * |gaussianBilinearVariable Z p| := ht
      _ ≤ (|t| * ‖Z‖) * (nx * ny) := by convert hb using 1; ring
      _ ≤ _ := by convert hh using 1; ring
  simpa only [nx, ny, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using h

theorem gaussianBilinear_exp_integrable (Z : Matrix ι ρ ℝ) (t : ℝ)
    (hgap : |t| * ‖Z‖ < 1) :
    Integrable (fun p => Real.exp (t * gaussianBilinearVariable Z p)) independentStandardGaussian := by
  have h := (standardGaussian_quadratic_product_integrable (ι := ι) (|t| * ‖Z‖) hgap).mul_prod
    (standardGaussian_quadratic_product_integrable (ι := ρ) (|t| * ‖Z‖) hgap)
  apply h.mono' (Measurable.aestronglyMeasurable (by unfold gaussianBilinearVariable; fun_prop))
  apply ae_of_all
  intro p
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert gaussianBilinearVariable_young_bound Z t p using 1
  ring

theorem gaussianBilinear_mgf_eq (Z : Matrix ι ρ ℝ) (t : ℝ) (hgap : |t| * ‖Z‖ < 1) :
    mgf (gaussianBilinearVariable Z) independentStandardGaussian t = gramGaussian (t • Z) := by
  rw [mgf]
  change (∫ p, Real.exp (t * gaussianBilinearVariable Z p)
    ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)).prod
      (Measure.pi (fun _ : ρ => gaussianReal 0 1))) = _
  rw [integral_prod _ (gaussianBilinear_exp_integrable Z t hgap)]
  exact gaussianBilinearMGF_eq_gramGaussian_smul Z t hgap

theorem gaussianBilinear_zero_mem_interior (Z : Matrix ι ρ ℝ) :
    0 ∈ interior (integrableExpSet (gaussianBilinearVariable Z) independentStandardGaussian) := by
  have hopen : IsOpen {t : ℝ | |t| * ‖Z‖ < 1} :=
    isOpen_lt (continuous_abs.mul continuous_const) continuous_const
  have hs : {t : ℝ | |t| * ‖Z‖ < 1} ⊆
      integrableExpSet (gaussianBilinearVariable Z) independentStandardGaussian := by
    intro t ht
    exact gaussianBilinear_exp_integrable Z t ht
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hopen.mem_nhds (by simp)) hs)

/-- Every Taylor derivative of the actual Gram determinant factor is the corresponding Gaussian moment. -/
theorem gramGaussian_iteratedDeriv_zero (Z : Matrix ι ρ ℝ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => gramGaussian (t • Z)) 0 = gaussianBilinearMoment Z k := by
  have hopen : IsOpen {t : ℝ | |t| * ‖Z‖ < 1} :=
    isOpen_lt (continuous_abs.mul continuous_const) continuous_const
  have he : mgf (gaussianBilinearVariable Z) independentStandardGaussian =ᶠ[nhds (0 : ℝ)]
      (fun t : ℝ => gramGaussian (t • Z)) := by
    filter_upwards [hopen.mem_nhds (by simp)] with t ht
    exact gaussianBilinear_mgf_eq Z t ht
  have hi := he.iteratedDeriv_eq k
  rw [iteratedDeriv_mgf_zero (gaussianBilinear_zero_mem_interior Z)] at hi
  rw [gaussianBilinearMoment_eq_joint_integral]
  exact hi.symm

noncomputable def bilinearGaussianCoefficient (Z : Matrix ι ρ ℝ) (k : ℕ) : ℝ :=
  gaussianBilinearMoment Z k / (k.factorial : ℝ)

theorem bilinearGaussianCoefficient_eq_derivative (Z : Matrix ι ρ ℝ) (k : ℕ) :
    bilinearGaussianCoefficient Z k =
      iteratedDeriv k (fun t : ℝ => gramGaussian (t • Z)) 0 / (k.factorial : ℝ) := by
  rw [gramGaussian_iteratedDeriv_zero]
  rfl

theorem bilinearGaussianCoefficient_pairings (Z : Matrix ι ρ ℝ) (k : ℕ) :
    bilinearGaussianCoefficient Z k =
      (∑ P ∈ Finset.univ.filter (fun P : Setoid (Fin k) => IsPairingPartition P),
        ∑ Q ∈ Finset.univ.filter (fun Q : Setoid (Fin k) => IsPairingPartition Q),
          rectangularPartitionContraction Z P Q) / (k.factorial : ℝ) := by
  rw [bilinearGaussianCoefficient, gaussianBilinearMoment_pairing_expansion]

theorem bilinearGaussianCoefficient_odd (Z : Matrix ι ρ ℝ) (k : ℕ) :
    bilinearGaussianCoefficient Z (2 * k + 1) = 0 := by
  rw [bilinearGaussianCoefficient, gaussianBilinearMoment_odd, zero_div]

theorem bilinearGaussianCoefficient_nonneg (Z : Matrix ι ρ ℝ) (k : ℕ) :
    0 ≤ bilinearGaussianCoefficient Z k := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j = 2 * j by omega, bilinearGaussianCoefficient]
    exact div_nonneg (gaussianBilinearMoment_even_nonneg Z j) (Nat.cast_nonneg _)
  · rw [bilinearGaussianCoefficient_odd]

end TournamentHamiltonian
