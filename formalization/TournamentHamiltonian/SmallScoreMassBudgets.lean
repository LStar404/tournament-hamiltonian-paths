import TournamentHamiltonian.SmallScoreRelativeError

namespace TournamentHamiltonian

theorem pairedMassErrorBudget_le_bounded_variance (N tau c : ℝ)
    (hN : 1≤N) (ht0 : 0≤tau) (ht1 : tau≤1) (hc : 0≤c) :
    pairedMassErrorBudget N tau c ≤ 4*c*tau := by
  have hs : 1≤Real.sqrt N := by simpa using Real.sqrt_le_sqrt hN
  have ht2 : tau^2≤tau := by nlinarith
  calc
    _ ≤ 2*c*(tau+tau^2)/Real.sqrt N := pairedMassErrorBudget_coarse N tau c hN ht0 hc
    _ ≤ 2*c*(tau+tau^2) := by
      have h := div_le_div_of_nonneg_left (by positivity : 0≤2*c*(tau+tau^2)) (by norm_num : (0 : ℝ)<1) hs
      simpa only [div_one] using h
    _ ≤ _ := by nlinarith [mul_nonneg hc (sub_nonneg.mpr ht2)]

theorem preconditioned_mass_error_le_small_score {n : ℕ} (T : Tournament n)
    (hn : 2≤n) (d : ℝ) (hd : 0≤d) (hs : ∀ i, |score T i|≤d)
    (ha : ∀ i, |tournamentScorePotential T i|≤1/2) (htau : scoreVariance T≤1) :
    |matrixEntryMass (preconditionedTournamentDensity T)-n|≤128*d^2/n := by
  have hnR : (1 : ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have h := preconditioned_mass_error_bound T (by omega) (1/2) (by norm_num) (by norm_num) ha
  have hbudget := pairedMassErrorBudget_le_bounded_variance (n : ℝ) (scoreVariance T)
    (4/(1-(1/2 : ℝ)^2)^2) hnR (scoreVariance_nonneg T) htau (by positivity)
  change _ ≤ pairedMassErrorBudget _ _ _ at h
  have hvar := mul_le_mul_of_nonneg_left (scoreVariance_le_score_budget T hn d hd hs) (by norm_num : (0 : ℝ)≤32)
  apply (h.trans hbudget).trans
  have hc : 4*(4/(1-(1/2 : ℝ)^2)^2)≤32 := by norm_num
  have hm := mul_le_mul_of_nonneg_right hc (scoreVariance_nonneg T)
  apply hm.trans
  exact hvar.trans_eq (by ring)

theorem normalizedPreconditioned_marginal_small_score {n : ℕ} (T : Tournament n)
    (hn : 2≤n) (d : ℝ) (hd : 0≤d) (hdn : d≤n) (hs : ∀ i, |score T i|≤d)
    (ha : ∀ i, |tournamentScorePotential T i|≤1/2) (htau : scoreVariance T≤1)
    (hM : (n : ℝ)/2≤matrixEntryMass (preconditionedTournamentDensity T)) :
    (∀ i, |matrixRowError (normalizedPreconditionedDensity T) i|≤320*d/n) ∧
    (∀ j, |matrixColumnError (normalizedPreconditionedDensity T) j|≤320*d/n) := by
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0 : ℝ)<n := by linarith
  have hmass := preconditioned_mass_error_le_small_score T hn d hd hs ha htau
  have hsqrt := score_sqrt_le_score_budget T hn d hd hs
  have hbound : 8/(1-(1/2 : ℝ))^2*Real.sqrt (scoreVariance T/n)+
      2*|matrixEntryMass (preconditionedTournamentDensity T)-n|/n≤320*d/n := by
    have h1 := mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ)≤32)
    have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ)≤2)) hn0.le
    have hd2 : d^2≤d*n := by nlinarith
    have h3 : 2*(128*d^2/n)/n≤256*d/n := by
      apply (div_le_div_iff₀ hn0 hn0).mpr
      have h := mul_le_mul_of_nonneg_left hd2 (by norm_num : (0 : ℝ)≤256)
      field_simp
      nlinarith
    norm_num only at ⊢
    exact (add_le_add h1 (h2.trans h3)).trans_eq (by ring)
  constructor
  · intro i
    exact (normalizedPreconditionedDensity_row_error_abs_le T (by omega) (1/2) (by norm_num) ha hM i).trans hbound
  · intro j
    exact (normalizedPreconditionedDensity_column_error_abs_le T (by omega) (1/2) (by norm_num) ha hM j).trans hbound

theorem retained_preconditioned_mass_error_small_score {n t : ℕ} (T : Tournament n)
    (hn : 2≤n) (d : ℝ) (hd : 0≤d) (hdn : d≤n) (hs : ∀ i, |score T i|≤d)
    (ha : ∀ i, |tournamentScorePotential T i|≤1/2) (htau : scoreVariance T≤1)
    (hM : (n : ℝ)/2≤matrixEntryMass (preconditionedTournamentDensity T))
    (I J : Finset (Fin n)) (hI : I.card=t) (hJ : J.card=t) (ht : 2*t≤n) :
    |matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J)-(n-t : ℝ)|≤
      (1280*(t : ℝ)*d+66*(t : ℝ)^2)/n := by
  have hn0 : 0<n := by omega
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hnRp : (0 : ℝ)<n := by linarith
  obtain ⟨hr,hc⟩ := normalizedPreconditioned_marginal_small_score T hn d hd hdn hs ha htau hM
  have he (i j : Fin n) : 0≤normalizedPreconditionedDensity T i j ∧
      normalizedPreconditionedDensity T i j≤32/(n : ℝ) := by
    obtain ⟨h0,h1⟩ := normalizedPreconditionedDensity_entry_bounds T (by omega) (1/2) (by norm_num) (by norm_num) ha hM i j
    refine ⟨h0,h1.trans_eq ?_⟩
    norm_num
    ring
  have h := scaled_deleted_mass_error_bound (normalizedPreconditionedDensity T) hn0 I J hI hJ ht
    (normalizedPreconditionedDensity_mass T hn0 hM) 32 (320*d/n) (by norm_num) (by positivity) he hr hc
  exact h.trans_eq (by ring)

end TournamentHamiltonian
