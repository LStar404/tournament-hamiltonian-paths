import TournamentHamiltonian.SmallScoreBudgets

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq

theorem pairedScoreProduct_pos_small_score {n : ℕ} (T : Tournament n)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ 1/2) : 0<pairedScoreProduct T := by
  unfold pairedScoreProduct
  apply Finset.prod_pos
  intro i _
  obtain ⟨hl,hr⟩ := abs_le.mp (ha i)
  nlinarith

theorem pairedLeft_deleted_log_bound {n : ℕ} (T : Tournament n) (I : Finset (Fin n)) (r : ℝ)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ 1/2)
    (hr : ∀ i, |tournamentScorePotential T i| ≤ r) :
    |Real.log (∏ i∈I,pairedLeft (tournamentScorePotential T i))| ≤ 2*(I.card : ℝ)*r := by
  have hp (i : Fin n) : 0<pairedLeft (tournamentScorePotential T i) := by
    unfold pairedLeft
    apply inv_pos.mpr
    linarith [(abs_le.mp (ha i)).1]
  rw [Real.log_prod (fun i _ => (hp i).ne')]
  calc
    _ ≤ ∑ i∈I,|Real.log (pairedLeft (tournamentScorePotential T i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i∈I,2*r := Finset.sum_le_sum (fun i _ =>
      (pairedLeft_log_abs_le _ (ha i)).trans (mul_le_mul_of_nonneg_left (hr i) (by norm_num)))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem pairedRight_deleted_log_bound {n : ℕ} (T : Tournament n) (J : Finset (Fin n)) (r : ℝ)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ 1/2)
    (hr : ∀ i, |tournamentScorePotential T i| ≤ r) :
    |Real.log (∏ i∈J,pairedRight (tournamentScorePotential T i))| ≤ 2*(J.card : ℝ)*r := by
  have hp (i : Fin n) : 0<pairedRight (tournamentScorePotential T i) := by
    unfold pairedRight
    apply inv_pos.mpr
    linarith [(abs_le.mp (ha i)).2]
  rw [Real.log_prod (fun i _ => (hp i).ne')]
  calc
    _ ≤ ∑ i∈J,|Real.log (pairedRight (tournamentScorePotential T i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i∈J,2*r := Finset.sum_le_sum (fun i _ =>
      (pairedRight_log_abs_le _ (ha i)).trans (mul_le_mul_of_nonneg_left (hr i) (by norm_num)))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem paired_restoration_score_log_bound {n t : ℕ} (T : Tournament n)
    (hn : 2≤n) (d : ℝ) (hd : 0≤d) (hs : ∀ i, |score T i|≤d)
    (ha : ∀ i, |tournamentScorePotential T i|≤1/2)
    (I J : Finset (Fin n)) (hI : I.card=t) (hJ : J.card=t) :
    |Real.log (pairedScoreProduct T*(∏ i∈I,pairedLeft (tournamentScorePotential T i))*
      (∏ j∈J,pairedRight (tournamentScorePotential T j)))| ≤
        8*(d+(t : ℝ)+1)^2/n := by
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0 : ℝ)<n := by linarith
  have ht : (0 : ℝ)≤t := Nat.cast_nonneg _
  have hleft : 0<∏ i∈I,pairedLeft (tournamentScorePotential T i) := by
    apply Finset.prod_pos
    intro i _
    unfold pairedLeft
    apply inv_pos.mpr
    linarith [(abs_le.mp (ha i)).1]
  have hright : 0<∏ j∈J,pairedRight (tournamentScorePotential T j) := by
    apply Finset.prod_pos
    intro j _
    unfold pairedRight
    apply inv_pos.mpr
    linarith [(abs_le.mp (ha j)).2]
  have hG := pairedScoreProduct_pos_small_score T ha
  rw [Real.log_mul (mul_pos hG hleft).ne' hright.ne',Real.log_mul hG.ne' hleft.ne']
  have hΓ := (pairedScoreProduct_log_abs_le T ha).trans
    (mul_le_mul_of_nonneg_left (scoreVariance_le_score_budget T hn d hd hs) (by norm_num : (0 : ℝ)≤2))
  have hL := pairedLeft_deleted_log_bound T I (2*d/n) ha (tournamentScorePotential_le_score_budget T hn d hd hs)
  have hR := pairedRight_deleted_log_bound T J (2*d/n) ha (tournamentScorePotential_le_score_budget T hn d hd hs)
  rw [hI] at hL
  rw [hJ] at hR
  have htri := (abs_add_le (Real.log (pairedScoreProduct T)+Real.log (∏ i∈I,pairedLeft (tournamentScorePotential T i)))
    (Real.log (∏ j∈J,pairedRight (tournamentScorePotential T j)))).trans
      (add_le_add (abs_add_le _ _) (le_rfl))
  apply htri.trans
  apply (add_le_add (add_le_add hΓ hL) hR).trans
  have he : 2*(4*d^2/n)+2*(t : ℝ)*(2*d/n)+2*(t : ℝ)*(2*d/n)=8*(d^2+(t : ℝ)*d)/n := by ring
  rw [he]
  apply div_le_div_of_nonneg_right _ hn0.le
  nlinarith [sq_nonneg (t : ℝ),mul_nonneg ht hd]

end TournamentHamiltonian
