import TournamentHamiltonian.GaussianCoreCoefficients
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Convergence of the actual Wick coefficient series throughout the operator norm gap. -/

namespace TournamentHamiltonian

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ]

theorem bilinearGaussianCoefficient_hasSum (Z : Matrix ι ρ ℝ) (t : ℝ)
    (hgap : |t| * ‖Z‖ < 1) :
    HasSum (fun k => bilinearGaussianCoefficient Z k * t ^ k) (gramGaussian (t • Z)) := by
  let X := gaussianBilinearVariable Z
  let μ := independentStandardGaussian (ι := ι) (ρ := ρ)
  have hpos : Integrable (fun p => Real.exp (t * X p)) μ :=
    gaussianBilinear_exp_integrable Z t hgap
  have hneg : Integrable (fun p => Real.exp (-t * X p)) μ :=
    gaussianBilinear_exp_integrable Z (-t) (by simpa using hgap)
  have habs := integrable_exp_abs_mul_abs hpos hneg
  have hs := hasSum_integral_of_dominated_convergence
    (μ := μ) (F := fun k p => (t * X p) ^ k / (k.factorial : ℝ))
    (f := fun p => Real.exp (t * X p))
    (fun k p => |t * X p| ^ k / (k.factorial : ℝ))
    (fun k => ((gaussianBilinear_pow_integrable Z k).const_mul (t ^ k)).div_const
      (k.factorial : ℝ) |>.aestronglyMeasurable.congr (by
        filter_upwards [] with p
        simp [mul_pow, X]))
    (fun k => Filter.Eventually.of_forall (fun p => by
      simp [Real.norm_eq_abs]))
    (Filter.Eventually.of_forall (fun p => (NormedSpace.expSeries_div_hasSum_exp |t * X p|).summable))
    (by
      simpa only [(NormedSpace.expSeries_div_hasSum_exp _).tsum_eq,
        ← Real.exp_eq_exp_ℝ, abs_mul] using habs)
    (Filter.Eventually.of_forall (fun p => by
      simpa only [← Real.exp_eq_exp_ℝ] using
        NormedSpace.expSeries_div_hasSum_exp (t * X p)))
  have heq : (fun k => ∫ p, (t * X p) ^ k / (k.factorial : ℝ) ∂μ) =
      (fun k => bilinearGaussianCoefficient Z k * t ^ k) := by
    funext k
    rw [integral_div, show (fun p => (t * X p) ^ k) =
      (fun p => t ^ k * X p ^ k) by funext p; rw [mul_pow], integral_const_mul]
    rw [bilinearGaussianCoefficient, gaussianBilinearMoment_eq_joint_integral]
    dsimp [X, μ]
    ring
  rw [heq] at hs
  change HasSum _ (mgf (gaussianBilinearVariable Z) independentStandardGaussian t) at hs
  rwa [gaussianBilinear_mgf_eq Z t hgap] at hs

theorem bilinearGaussianCoefficient_tsum (Z : Matrix ι ρ ℝ) (t : ℝ)
    (hgap : |t| * ‖Z‖ < 1) :
    (∑' k, bilinearGaussianCoefficient Z k * t ^ k) = gramGaussian (t • Z) :=
  (bilinearGaussianCoefficient_hasSum Z t hgap).tsum_eq

theorem bilinearGaussianCoefficient_finite_sum_le (Z : Matrix ι ρ ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hgap : R * ‖Z‖ < 1) (s : Finset ℕ) :
    (∑ k ∈ s, bilinearGaussianCoefficient Z k * R ^ k) ≤ gramGaussian (R • Z) := by
  exact sum_le_hasSum s (fun k _ => mul_nonneg (bilinearGaussianCoefficient_nonneg Z k)
    (pow_nonneg hR k)) (bilinearGaussianCoefficient_hasSum Z R (by simpa [abs_of_nonneg hR] using hgap))

theorem bilinearGaussianCoefficient_abs_hasSum (Z : Matrix ι ρ ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hgap : R * ‖Z‖ < 1) :
    HasSum (fun k => |bilinearGaussianCoefficient Z k| * R ^ k) (gramGaussian (R • Z)) := by
  simpa only [abs_of_nonneg (bilinearGaussianCoefficient_nonneg Z _)] using
    bilinearGaussianCoefficient_hasSum Z R (by simpa [abs_of_nonneg hR] using hgap)

end TournamentHamiltonian

