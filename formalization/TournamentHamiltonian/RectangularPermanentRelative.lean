import TournamentHamiltonian.ScaledPermanentGaussian

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

theorem relative_error_le_of_gaussian_one_le (N G c : ℝ) (hG : 1 ≤ G)
    (hc : 0 ≤ c) (herror : |N - G| ≤ c) : |N / G - 1| ≤ c := by
  have hGp : 0 < G := by linarith
  have hid : N / G - 1 = (N - G) / G := by field_simp
  rw [hid, abs_div, abs_of_pos hGp]
  exact (div_le_div_of_nonneg_right herror hGp.le).trans (div_le_self hc hG)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- An actual relative approximation: the Gaussian factor is at least one,
so the absolute coefficient error also bounds the relative permanent error. -/
theorem rectangularPermanent_relative_of_activities (Y : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (hrow : ∀ i, ∑ j, Y i j = 1) (hcol : ∀ j, ∑ i, Y i j = 1)
    (hentry : ∀ i j, |Y i j| ≤ K / Fintype.card ι)
    (hgap : ‖Y - rectangularAverageMatrix ι κ‖ ≤ q)
    (hactivity : ActualCoreActivities (rectangularPermanentKernel Y e) (K + 1) q) :
    |((Fintype.card ι : ℝ) ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ) *
        rectangularPermanent Y e) / gramGaussian (Y - rectangularAverageMatrix ι κ) - 1| ≤
      uniformPermanentActivityConstant (K + 1) q / Fintype.card ι := by
  apply relative_error_le_of_gaussian_one_le
  · exact gramGaussian_one_le_of_gap _ (hgap.trans_lt hq1)
  · exact div_nonneg (uniformPermanentActivityConstant_nonneg _ q hq hq1)
      (by exact_mod_cast hp.le)
  · exact rectangularPermanent_approximation_of_activities Y e hp K q hK hq hq1
      hrow hcol hentry hgap hactivity

theorem rectangularScaling_permanent_relative_of_activities (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K C q eps : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (x : ι → ℝ) (y : κ → ℝ) (hxy : RectangularScalingWitness X e K C q eps x y)
    (hactivity : ActualCoreActivities (rectangularPermanentKernel (rectangularExpScaling X x y) e)
      (2 * K + 1) ((1 + q) / 2)) :
    |((Fintype.card ι : ℝ) ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ) *
        rectangularPermanent (rectangularExpScaling X x y) e) /
          gramGaussian (rectangularExpScaling X x y - rectangularAverageMatrix ι κ) - 1| ≤
      uniformPermanentActivityConstant (2 * K + 1) ((1 + q) / 2) / Fintype.card ι := by
  exact rectangularPermanent_relative_of_activities _ e hp (2 * K) ((1 + q) / 2)
    (by positivity) (by positivity) (by linarith) hxy.row_sum hxy.column_sum
    hxy.density hxy.gap hactivity

theorem rectangularPermanent_lower_of_activities (Y : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (hrow : ∀ i, ∑ j, Y i j = 1) (hcol : ∀ j, ∑ i, Y i j = 1)
    (hentry : ∀ i j, |Y i j| ≤ K / Fintype.card ι)
    (hgap : ‖Y - rectangularAverageMatrix ι κ‖ ≤ q)
    (hactivity : ActualCoreActivities (rectangularPermanentKernel Y e) (K + 1) q) :
    ((Fintype.card ι).factorial : ℝ) / (Fintype.card ι : ℝ) ^ Fintype.card ι *
      gramGaussian (Y - rectangularAverageMatrix ι κ) *
        (1 - uniformPermanentActivityConstant (K + 1) q / Fintype.card ι) ≤
          rectangularPermanent Y e := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  have hf : (0 : ℝ) < (Fintype.card ι).factorial := by exact_mod_cast Nat.factorial_pos _
  have hG := gramGaussian_one_le_of_gap (Y - rectangularAverageMatrix ι κ) (hgap.trans_lt hq1)
  have hGp : 0 < gramGaussian (Y - rectangularAverageMatrix ι κ) := by linarith
  have h := (abs_le.mp (rectangularPermanent_relative_of_activities Y e hp K q
    hK hq hq1 hrow hcol hentry hgap hactivity)).1
  have hb := (le_div_iff₀ hGp).mp (show
    1 - uniformPermanentActivityConstant (K + 1) q / Fintype.card ι ≤
      ((Fintype.card ι : ℝ) ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ) *
        rectangularPermanent Y e) / gramGaussian (Y - rectangularAverageMatrix ι κ) by linarith)
  have hr : 0 < (Fintype.card ι : ℝ) ^ Fintype.card ι /
      ((Fintype.card ι).factorial : ℝ) := by positivity
  have hh : ((1 - uniformPermanentActivityConstant (K + 1) q / Fintype.card ι) *
      gramGaussian (Y - rectangularAverageMatrix ι κ)) /
        ((Fintype.card ι : ℝ) ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ)) ≤
          rectangularPermanent Y e := (div_le_iff₀ hr).mpr (by nlinarith [hb])
  convert hh using 1
  field_simp

end TournamentHamiltonian
