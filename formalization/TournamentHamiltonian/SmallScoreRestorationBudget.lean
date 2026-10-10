import TournamentHamiltonian.SmallScoreMassBudgets

namespace TournamentHamiltonian

theorem preconditioning_mass_power_small_score {n t : ℕ} (T : Tournament n)
    (hn : 2≤n) (ht : t<n) (d : ℝ) (hd : 0≤d) (hdn : d≤n) (hs : ∀ i, |score T i|≤d)
    (ha : ∀ i, |tournamentScorePotential T i|≤1/2) (htau : scoreVariance T≤1)
    (I J : Finset (Fin n)) (hI : I.card=t) (hJ : J.card=t) (h2t : 2*t≤n)
    (hM : (n : ℝ)/2≤matrixEntryMass (preconditionedTournamentDensity T))
    (hQ : (n-t : ℝ)/2≤matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J)) :
    |Real.log (((n-1 : ℝ)/((n-t : ℝ)*preconditioningDeletionEta (t := t) T I J))^(n-t))+1|≤
      3000*(d+(t : ℝ)+1)^2/n := by
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0 : ℝ)<n := by linarith
  have ht0 : (0 : ℝ)≤t := Nat.cast_nonneg _
  have h1 := preconditioning_mass_power_log_error T hn ht I J hM hQ
  have h2 := preconditioned_mass_error_le_small_score T hn d hd hs ha htau
  have h3 := retained_preconditioned_mass_error_small_score T hn d hd hdn hs ha htau hM I J hI hJ h2t
  apply h1.trans
  apply (add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ)≤2)))
    (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ)≤2))).trans
  have he : ((t : ℝ)+2)/n+2*(128*d^2/n)+2*((1280*(t : ℝ)*d+66*(t : ℝ)^2)/n)=
      ((t : ℝ)+2+256*d^2+2560*(t : ℝ)*d+132*(t : ℝ)^2)/n := by ring
  rw [he]
  apply div_le_div_of_nonneg_right _ hn0.le
  nlinarith [sq_nonneg d,sq_nonneg (t : ℝ),mul_nonneg ht0 hd]

theorem small_score_combined_log_budget (s p theta g S n L Gc : ℝ)
    (hS : 1≤S) (hn : 0<n) (_hL : 0≤L) (hGc : 0≤Gc)
    (hs : |s|≤8*S^2/n) (hp : |p+1|≤3000*S^2/n)
    (ht : |theta|≤524288*L^2*S^2/n) (hg : |g|≤2*Gc*S/n) :
    |s+(p+1)-theta+g|≤(3008+524288*L^2+2*Gc)*S^2/n := by
  have hg2 : 2*Gc*S/n≤2*Gc*S^2/n := by
    apply div_le_div_of_nonneg_right _ hn.le
    have hS2 : S≤S^2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hS2 (by positivity)
  have htri := (abs_add_le (s+(p+1)-theta) g).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))) (le_refl _))
  exact htri.trans ((add_le_add (add_le_add (add_le_add hs hp) ht) (hg.trans hg2)).trans_eq (by ring))

theorem rectangularScaling_capacity_small_score {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι κ ℝ) (e : ι ≃ κ) (K C q eps delta S n : ℝ)
    (hn : 0<n) (hmn : (Fintype.card ι : ℝ)≤n) (hd : 0≤delta)
    (hS : 0≤S) (hdelta : delta≤64*S/n)
    (x : ι → ℝ) (y : κ → ℝ) (hxy : RectangularScalingWitness X e K C q eps x y)
    (hr : ∀ i, |matrixRowError X i|≤delta) (hc : ∀ j, |matrixColumnError X j|≤delta) :
    |(∑ i,x i)+(∑ j,y j)|≤524288*localScalingInverseBudget C q^2*S^2/n := by
  have hb := rectangularScaling_capacity_le_marginal_bound X e K C q eps delta hd x y hxy hr hc
  have hs := (sq_le_sq₀ hd (by positivity : 0≤64*S/n)).mpr hdelta
  apply hb.trans
  calc
    _ ≤ 128*localScalingInverseBudget C q^2*(Fintype.card ι : ℝ)*(64*S/n)^2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ 128*localScalingInverseBudget C q^2*n*(64*S/n)^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmn (by positivity : 0≤128*localScalingInverseBudget C q^2)) (sq_nonneg _)
    _ = _ := by field_simp; ring

theorem preconditioned_gaussian_cost_small_score {n t : ℕ} (T : Tournament n)
    (hn : 2≤n) (d : ℝ) (hd : 0≤d) (hs : ∀ i, |score T i|≤d)
    (G : ℝ) (hcost : |Real.log G-Real.log (gaussianFactor T)|≤
      preconditioningGaussianCostConstant (1/2)*(Real.sqrt (scoreVariance T/n)+((t : ℝ)+1)/n)) :
    |Real.log G-Real.log (gaussianFactor T)|≤
      2*preconditioningGaussianCostConstant (1/2)*(d+(t : ℝ)+1)/n := by
  have ht0 : (0 : ℝ)≤t := Nat.cast_nonneg _
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0 : ℝ)<n := by linarith
  apply hcost.trans
  calc
    _ ≤ preconditioningGaussianCostConstant (1/2)*(2*d/n+((t : ℝ)+1)/n) :=
      mul_le_mul_of_nonneg_left (add_le_add (score_sqrt_le_score_budget T hn d hd hs) le_rfl)
        (preconditioningGaussianCostConstant_pos _).le
    _ ≤ _ := by
      have hb : 2*d/n+((t : ℝ)+1)/n≤2*(d+(t : ℝ)+1)/n := by
        rw [←add_div]
        exact div_le_div_of_nonneg_right (by linarith) hn0.le
      convert mul_le_mul_of_nonneg_left hb (preconditioningGaussianCostConstant_pos _).le using 1; ring

end TournamentHamiltonian
