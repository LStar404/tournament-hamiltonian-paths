import TournamentHamiltonian.SmallScoreMinorRestoration

namespace TournamentHamiltonian

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable def smallScoreRestorationConstant (C q : ℝ) : ℝ :=
  3008+524288*localScalingInverseBudget C q^2+2*preconditioningGaussianCostConstant (1/2)

theorem smallScoreRestorationConstant_pos (C q : ℝ) : 0<smallScoreRestorationConstant C q := by
  have hg := preconditioningGaussianCostConstant_pos (1/2)
  unfold smallScoreRestorationConstant
  positivity

theorem smallScoreRestorationConstant_lower (C q : ℝ) : 3008 ≤ smallScoreRestorationConstant C q := by
  have hg := (preconditioningGaussianCostConstant_pos (1/2)).le
  unfold smallScoreRestorationConstant
  nlinarith [sq_nonneg (localScalingInverseBudget C q)]

theorem nonprincipalRestorationLog_small_score {n t : ℕ} (T : Tournament n)
    (hn : 2≤n) (ht : t<n) (d : ℝ) (hd : 0≤d) (hdn : d≤n) (hs : ∀ i, |score T i|≤d)
    (ha : ∀ i, |tournamentScorePotential T i|≤1/2) (htau : scoreVariance T≤1)
    (I J : Finset (Fin n)) (hI : I.card=t) (hJ : J.card=t) (h2t : 2*t≤n)
    (hM : (n : ℝ)/2≤matrixEntryMass (preconditionedTournamentDensity T))
    (hQ : (n-t : ℝ)/2≤matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J))
    (K C q eps : ℝ) (x : (Iᶜ : Finset (Fin n))→ℝ) (y : (Jᶜ : Finset (Fin n))→ℝ)
    (hxy : RectangularScalingWitness (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J)
      (deletedComplementEquiv I J (hI.trans hJ.symm)) K C q eps x y)
    (hr : ∀ i, |matrixRowError (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) i|≤64*(d+(t : ℝ)+1)/n)
    (hc : ∀ j, |matrixColumnError (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) j|≤64*(d+(t : ℝ)+1)/n)
    (hcost : |Real.log (gramGaussian (rectangularExpScaling
      (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y-rectangularAverageMatrix _ _))-
      Real.log (gaussianFactor T)|≤preconditioningGaussianCostConstant (1/2)*
        (Real.sqrt (scoreVariance T/n)+((t : ℝ)+1)/n)) :
    |nonprincipalRestorationLog (t := t) T I J x y|≤smallScoreRestorationConstant C q*(d+(t : ℝ)+1)^2/n := by
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0 : ℝ)<n := by linarith
  have hcard : Fintype.card (Iᶜ : Finset (Fin n))=n-t := by
    rw [Fintype.card_coe,Finset.card_compl,Fintype.card_fin,hI]
  have hcn : (Fintype.card (Iᶜ : Finset (Fin n)) : ℝ)≤n := by rw [hcard]; exact_mod_cast Nat.sub_le n t
  have hS : 1≤d+(t : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) t]
  have hscore := paired_restoration_score_log_bound T hn d hd hs ha I J hI hJ
  change |Real.log (pairedDeletionScoreFactor T I J)|≤_ at hscore
  have hmass := preconditioning_mass_power_small_score T hn ht d hd hdn hs ha htau I J hI hJ h2t hM hQ
  rw [←Nat.cast_sub ht.le] at hmass
  change |Real.log (preconditioningDeletedMassPower (t := t) T I J)+1|≤_ at hmass
  have hcap := rectangularScaling_capacity_small_score _
    (deletedComplementEquiv I J (hI.trans hJ.symm)) K C q eps (64*(d+(t : ℝ)+1)/n)
    (d+(t : ℝ)+1) n hn0 hcn (by positivity) (by positivity) le_rfl x y hxy hr hc
  have hgauss := preconditioned_gaussian_cost_small_score T hn d hd hs _ hcost
  have hcap' : |(∑ i, x i) + ∑ j, y j| ≤
      524288 * |localScalingInverseBudget C q| ^ 2 * (d + (t : ℝ) + 1) ^ 2 / n := by
    simpa only [sq_abs] using hcap
  have hbound := small_score_combined_log_budget _ _ _ _ _ _
    (|localScalingInverseBudget C q|) _ hS hn0 (abs_nonneg _)
    (preconditioningGaussianCostConstant_pos _).le hscore hmass hcap' hgauss
  simpa only [sq_abs, smallScoreRestorationConstant, nonprincipalRestorationLog] using hbound

end TournamentHamiltonian
