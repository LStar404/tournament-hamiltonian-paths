import TournamentHamiltonian.RectangularPermanentApproximation

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

theorem positive_le_exp_log_difference (G D δ : ℝ) (hG : 0 < G) (hD : 0 < D)
    (hlog : |Real.log G - Real.log D| ≤ δ) : G ≤ D * Real.exp δ := by
  nth_rw 1 [← Real.exp_log hG]
  rw [← Real.exp_log hD, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hlog).2])

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem rectangularScaling_permanent_upper_of_activities (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K C q eps : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (x : ι → ℝ) (y : κ → ℝ) (hxy : RectangularScalingWitness X e K C q eps x y)
    (hactivity : ActualCoreActivities (rectangularPermanentKernel (rectangularExpScaling X x y) e)
      (2 * K + 1) ((1 + q) / 2)) :
    rectangularPermanent (rectangularExpScaling X x y) e ≤ ((Fintype.card ι).factorial : ℝ) /
      (Fintype.card ι : ℝ) ^ Fintype.card ι *
        gramGaussian (rectangularExpScaling X x y - rectangularAverageMatrix ι κ) *
          (1 + uniformPermanentActivityConstant (2 * K + 1) ((1 + q) / 2) / Fintype.card ι) := by
  exact rectangularPermanent_upper_of_activities _ e hp (2 * K) ((1 + q) / 2)
    (by positivity) (by positivity) (by linarith) hxy.row_sum hxy.column_sum
    hxy.density hxy.gap hactivity

/-- The permanent and Gram estimates use exactly the same genuine scaling
potentials x,y; the graph obligation is displayed on that actual matrix. -/
theorem rectangularScaling_permanent_upper_from_log_cost (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K C q eps : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (x : ι → ℝ) (y : κ → ℝ) (hxy : RectangularScalingWitness X e K C q eps x y)
    (hactivity : ActualCoreActivities (rectangularPermanentKernel (rectangularExpScaling X x y) e)
      (2 * K + 1) ((1 + q) / 2)) (D δ : ℝ) (hD : 0 < D)
    (hcost : |Real.log (gramGaussian (rectangularExpScaling X x y - rectangularAverageMatrix ι κ)) -
      Real.log D| ≤ δ) :
    rectangularPermanent (rectangularExpScaling X x y) e ≤ ((Fintype.card ι).factorial : ℝ) /
      (Fintype.card ι : ℝ) ^ Fintype.card ι * D *
        Real.exp (δ + uniformPermanentActivityConstant (2 * K + 1) ((1 + q) / 2) / Fintype.card ι) := by
  let c := uniformPermanentActivityConstant (2 * K + 1) ((1 + q) / 2) / Fintype.card ι
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  have hG : 0 < gramGaussian (rectangularExpScaling X x y - rectangularAverageMatrix ι κ) :=
    lt_of_lt_of_le (by norm_num) (gramGaussian_one_le_of_gap _ (hxy.gap.trans_lt (by linarith)))
  have hGp := positive_le_exp_log_difference _ D δ hG hD hcost
  have hc : 0 ≤ c := div_nonneg
    (uniformPermanentActivityConstant_nonneg _ _ (by positivity) (by linarith)) hn.le
  have hupper := rectangularScaling_permanent_upper_of_activities X e hp K C q eps
    hK hq hq1 x y hxy hactivity
  calc
    _ ≤ ((Fintype.card ι).factorial : ℝ) / (Fintype.card ι : ℝ) ^ Fintype.card ι *
        gramGaussian (rectangularExpScaling X x y - rectangularAverageMatrix ι κ) * (1 + c) := hupper
    _ ≤ ((Fintype.card ι).factorial : ℝ) / (Fintype.card ι : ℝ) ^ Fintype.card ι *
        (D * Real.exp δ) * Real.exp c := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hGp (by positivity)
      · simpa only [add_comm] using Real.add_one_le_exp c
      · linarith
      · positivity
    _ = _ := by rw [Real.exp_add]; ring

end TournamentHamiltonian
