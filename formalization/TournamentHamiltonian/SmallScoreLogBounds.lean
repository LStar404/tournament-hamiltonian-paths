import TournamentHamiltonian.RetainedMassPower

namespace TournamentHamiltonian

theorem abs_log_le_twice_sub_one (z : ℝ) (hz : 1 / 2 ≤ z) :
    |Real.log z| ≤ 2 * |z - 1| := by
  have hz0 : 0 < z := by linarith
  have hu := Real.log_le_sub_one_of_pos hz0
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hz0)
  rw [Real.log_inv] at hl
  have he : z⁻¹ - 1 = (1-z)/z := by field_simp
  rw [he] at hl
  have hnum : 1-z ≤ |z-1| := by simpa only [neg_sub] using neg_le_abs (z-1)
  have hdiv := div_le_div_of_nonneg_left (abs_nonneg (z-1)) (by norm_num : (0 : ℝ)<1/2) hz
  norm_num at hdiv
  have hn := (div_le_div_of_nonneg_right hnum hz0.le).trans hdiv
  exact abs_le.mpr ⟨by linarith, by linarith [le_abs_self (z-1),abs_nonneg (z-1)]⟩

theorem abs_log_one_sub_add_self_le (u : ℝ) (_hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    |Real.log (1-u)+u| ≤ 2*u^2 := by
  have hp : 0 < 1-u := by linarith
  have hu := Real.log_le_sub_one_of_pos hp
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hl
  have he : (1-u)⁻¹ - 1 = u/(1-u) := by field_simp; ring
  rw [he] at hl
  have hd : u/(1-u)-u = u^2/(1-u) := by field_simp; ring
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg u) (by norm_num : (0 : ℝ)<1/2)
    (by linarith : 1/2 ≤ 1-u)
  norm_num at hdiv
  exact abs_le.mpr ⟨by linarith, by nlinarith [sq_nonneg u]⟩

theorem pairedLeft_log_abs_le (a : ℝ) (ha : |a| ≤ 1/2) :
    |Real.log (pairedLeft a)| ≤ 2*|a| := by
  unfold pairedLeft
  rw [Real.log_inv,abs_neg]
  have h := abs_log_le_twice_sub_one (1+a) (by linarith [(abs_le.mp ha).1])
  simpa only [add_sub_cancel_left] using h

theorem pairedRight_log_abs_le (a : ℝ) (ha : |a| ≤ 1/2) :
    |Real.log (pairedRight a)| ≤ 2*|a| := by
  unfold pairedRight
  rw [Real.log_inv,abs_neg]
  have h := abs_log_le_twice_sub_one (1-a) (by linarith [(abs_le.mp ha).2])
  simpa only [sub_sub_cancel_left,abs_neg] using h

theorem pairedScoreProduct_log_abs_le {n : ℕ} (T : Tournament n)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ 1/2) :
    |Real.log (pairedScoreProduct T)| ≤ 2*scoreVariance T := by
  have hs (i : Fin n) : tournamentScorePotential T i ^ 2 ≤ 1/4 := by
    have h := sq_le_sq₀ (abs_nonneg (tournamentScorePotential T i)) (by norm_num : (0 : ℝ)≤1/2) |>.mpr (ha i)
    norm_num only [sq_abs] at h
    exact h
  unfold pairedScoreProduct
  rw [Real.log_prod (fun i _ => (show 0<1-tournamentScorePotential T i^2 by linarith [hs i]).ne')]
  calc
    _ ≤ ∑ i, |Real.log (1-tournamentScorePotential T i^2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2*tournamentScorePotential T i^2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := abs_log_le_twice_sub_one (1-tournamentScorePotential T i^2) (by linarith [hs i])
      simpa only [sub_sub_cancel_left,abs_neg,abs_of_nonneg (sq_nonneg (tournamentScorePotential T i))] using h
    _ = _ := by rw [← Finset.mul_sum]; rfl

end TournamentHamiltonian
