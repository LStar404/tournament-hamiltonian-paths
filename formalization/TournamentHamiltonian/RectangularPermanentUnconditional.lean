import TournamentHamiltonian.ActualCoreActivityPredicate
import TournamentHamiltonian.RectangularPermanentRelative

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem rectangularPermanentKernel_actualCoreActivities (Y : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (hentry : ∀ i j, |Y i j| ≤ K / Fintype.card ι)
    (hgap : ‖Y - rectangularAverageMatrix ι κ‖ ≤ q) :
    ActualCoreActivities (rectangularPermanentKernel Y e) (K + 1) q := by
  apply actualCoreActivities_of_matrix_bounds _ (K + 1) q hp (by linarith) hq hq1
  · exact rectangularPermanentKernel_entry_bound Y e hp K hentry
  · exact (matrix_l2_opNorm_submatrix_equiv _ (Equiv.refl ι) e).trans_le hgap

/-- Uniform approximation for a genuine rectangular doubly stochastic matrix.
All graph activities are proved from entry density and the actual L2 gap. -/
theorem rectangularPermanent_approximation_from_matrix_bounds (Y : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (hrow : ∀ i, ∑ j, Y i j = 1) (hcol : ∀ j, ∑ i, Y i j = 1)
    (hentry : ∀ i j, |Y i j| ≤ K / Fintype.card ι)
    (hgap : ‖Y - rectangularAverageMatrix ι κ‖ ≤ q) :
    |(Fintype.card ι : ℝ) ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ) *
        rectangularPermanent Y e - gramGaussian (Y - rectangularAverageMatrix ι κ)| ≤
      uniformPermanentActivityConstant (K + 1) q / Fintype.card ι :=
  rectangularPermanent_approximation_of_activities Y e hp K q hK hq hq1 hrow hcol
    hentry hgap (rectangularPermanentKernel_actualCoreActivities Y e hp K q hK hq hq1 hentry hgap)

theorem rectangularPermanent_relative_from_matrix_bounds (Y : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (hrow : ∀ i, ∑ j, Y i j = 1) (hcol : ∀ j, ∑ i, Y i j = 1)
    (hentry : ∀ i j, |Y i j| ≤ K / Fintype.card ι)
    (hgap : ‖Y - rectangularAverageMatrix ι κ‖ ≤ q) :
    |((Fintype.card ι : ℝ) ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ) *
        rectangularPermanent Y e) / gramGaussian (Y - rectangularAverageMatrix ι κ) - 1| ≤
      uniformPermanentActivityConstant (K + 1) q / Fintype.card ι :=
  rectangularPermanent_relative_of_activities Y e hp K q hK hq hq1 hrow hcol
    hentry hgap (rectangularPermanentKernel_actualCoreActivities Y e hp K q hK hq hq1 hentry hgap)

theorem rectangularScaling_actualCoreActivities (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K C q eps : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (x : ι → ℝ) (y : κ → ℝ) (hxy : RectangularScalingWitness X e K C q eps x y) :
    ActualCoreActivities (rectangularPermanentKernel (rectangularExpScaling X x y) e)
      (2 * K + 1) ((1 + q) / 2) :=
  rectangularPermanentKernel_actualCoreActivities _ e hp (2 * K) ((1 + q) / 2)
    (by positivity) (by positivity) (by linarith) hxy.density hxy.gap

theorem rectangularScaling_permanent_relative_from_matrix_bounds (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K C q eps : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (x : ι → ℝ) (y : κ → ℝ) (hxy : RectangularScalingWitness X e K C q eps x y) :
    |((Fintype.card ι : ℝ) ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ) *
        rectangularPermanent (rectangularExpScaling X x y) e) /
          gramGaussian (rectangularExpScaling X x y - rectangularAverageMatrix ι κ) - 1| ≤
      uniformPermanentActivityConstant (2 * K + 1) ((1 + q) / 2) / Fintype.card ι :=
  rectangularScaling_permanent_relative_of_activities X e hp K C q eps hK hq hq1 x y hxy
    (rectangularScaling_actualCoreActivities X e hp K C q eps hK hq hq1 x y hxy)

theorem rectangularScaling_permanent_upper_from_actual_log_cost (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K C q eps : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (x : ι → ℝ) (y : κ → ℝ) (hxy : RectangularScalingWitness X e K C q eps x y)
    (D δ : ℝ) (hD : 0 < D)
    (hcost : |Real.log (gramGaussian (rectangularExpScaling X x y - rectangularAverageMatrix ι κ)) -
      Real.log D| ≤ δ) :
    rectangularPermanent (rectangularExpScaling X x y) e ≤ ((Fintype.card ι).factorial : ℝ) /
      (Fintype.card ι : ℝ) ^ Fintype.card ι * D *
        Real.exp (δ + uniformPermanentActivityConstant (2 * K + 1) ((1 + q) / 2) / Fintype.card ι) :=
  rectangularScaling_permanent_upper_from_log_cost X e hp K C q eps hK hq hq1 x y hxy
    (rectangularScaling_actualCoreActivities X e hp K C q eps hK hq hq1 x y hxy) D δ hD hcost

end TournamentHamiltonian
