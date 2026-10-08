import TournamentHamiltonian.PermanentApproximationFromActivities

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

noncomputable def permanentAnalyticRadius (q : ℝ) : ℝ := (3 + q) / (2 * (1 + q))
noncomputable def permanentRecoveryRadius (q : ℝ) : ℝ := (1 + permanentAnalyticRadius q) / 2
noncomputable def permanentChainBudget (C q : ℝ) : ℝ :=
  max 1 (C * permanentAnalyticRadius q +
    C ^ 2 * permanentAnalyticRadius q ^ 2 / (1 - permanentAnalyticRadius q * q))
noncomputable def permanentExcessBudget (C q : ℝ) : ℝ := 710 * permanentChainBudget C q ^ 3
noncomputable def permanentFirstExcessBudget (C q : ℝ) : ℝ :=
  3 / 2 * permanentChainBudget C q ^ 2 + 10 / 3 * permanentChainBudget C q ^ 3
noncomputable def permanentWindowFraction (C q : ℝ) : ℝ :=
  min (1 / 4) (min (1 / (16 * permanentExcessBudget C q)) (Real.log (permanentRecoveryRadius q) / 2))

theorem permanentAnalyticRadius_one_lt (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    1 < permanentAnalyticRadius q := by
  unfold permanentAnalyticRadius
  apply (lt_div_iff₀ (by positivity : 0 < 2 * (1 + q))).mpr
  linarith

theorem permanentAnalyticRadius_gap (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    permanentAnalyticRadius q * q < 1 := by
  unfold permanentAnalyticRadius
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by positivity : 0 < 2 * (1 + q))).mpr
  nlinarith [sq_nonneg q]

theorem permanentRecoveryRadius_bounds (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    1 < permanentRecoveryRadius q ∧ permanentRecoveryRadius q < permanentAnalyticRadius q := by
  have h := permanentAnalyticRadius_one_lt q hq hq1
  unfold permanentRecoveryRadius
  constructor <;> linarith

theorem permanentChainBudget_one_le (C q : ℝ) : 1 ≤ permanentChainBudget C q := le_max_left _ _

theorem permanentExcessBudget_pos (C q : ℝ) : 0 < permanentExcessBudget C q := by
  have h := permanentChainBudget_one_le C q
  unfold permanentExcessBudget
  positivity

theorem permanentFirstExcessBudget_nonneg (C q : ℝ) : 0 ≤ permanentFirstExcessBudget C q := by
  have h := permanentChainBudget_one_le C q
  unfold permanentFirstExcessBudget
  positivity

theorem permanentWindowFraction_pos (C q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < permanentWindowFraction C q := by
  have hD := permanentExcessBudget_pos C q
  have hσ := (permanentRecoveryRadius_bounds q hq hq1).1
  have hlog := Real.log_pos hσ
  unfold permanentWindowFraction
  apply lt_min (by norm_num)
  exact lt_min (by positivity) (by positivity)

theorem permanentWindowFraction_quarter_le (C q : ℝ) :
    permanentWindowFraction C q ≤ 1 / 4 := min_le_left _ _

theorem permanentWindowFraction_excess_le (C q : ℝ) :
    16 * permanentExcessBudget C q * permanentWindowFraction C q ≤ 1 := by
  have hD := permanentExcessBudget_pos C q
  have hα : permanentWindowFraction C q ≤ 1 / (16 * permanentExcessBudget C q) :=
    (min_le_right _ _).trans (min_le_left _ _)
  exact (mul_le_mul_of_nonneg_left hα (by positivity)).trans_eq (by field_simp)

theorem permanentWindowFraction_log_le (C q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    permanentWindowFraction C q ≤ Real.log (permanentRecoveryRadius q) := by
  have hσ := (permanentRecoveryRadius_bounds q hq hq1).1
  have hα : permanentWindowFraction C q ≤ Real.log (permanentRecoveryRadius q) / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hlog := Real.log_pos hσ
  linarith

end TournamentHamiltonian
