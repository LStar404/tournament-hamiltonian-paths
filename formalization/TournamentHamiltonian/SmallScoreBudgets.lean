import TournamentHamiltonian.SmallScoreMassPower
import TournamentHamiltonian.PreconditionedMarginalBudgets

namespace TournamentHamiltonian

theorem tournamentScorePotential_le_score_budget {n : ℕ} (T : Tournament n)
    (hn : 2 ≤ n) (d : ℝ) (hd : 0 ≤ d) (hs : ∀ i, |score T i| ≤ d) (i : Fin n) :
    |tournamentScorePotential T i| ≤ 2*d/n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : 0 < (n : ℝ)-1 := by linarith
  unfold tournamentScorePotential
  rw [abs_div,abs_of_pos hn1]
  calc
    _ ≤ d/((n : ℝ)-1) := div_le_div_of_nonneg_right (hs i) hn1.le
    _ ≤ _ := (div_le_div_iff₀ hn1 hn0).mpr (by nlinarith)

theorem scoreVariance_le_score_budget {n : ℕ} (T : Tournament n)
    (hn : 2 ≤ n) (d : ℝ) (hd : 0 ≤ d) (hs : ∀ i, |score T i| ≤ d) :
    scoreVariance T ≤ 4*d^2/n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  unfold scoreVariance
  calc
    _ ≤ ∑ _i : Fin n, (2*d/n)^2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := (sq_le_sq₀ (abs_nonneg (tournamentScorePotential T i)) (by positivity : 0≤2*d/n)).mpr
        (tournamentScorePotential_le_score_budget T hn d hd hs i)
      simpa only [sq_abs] using h
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp; ring

theorem score_sqrt_le_score_budget {n : ℕ} (T : Tournament n)
    (hn : 2 ≤ n) (d : ℝ) (hd : 0 ≤ d) (hs : ∀ i, |score T i| ≤ d) :
    Real.sqrt (scoreVariance T/n) ≤ 2*d/n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hvar := div_le_div_of_nonneg_right (scoreVariance_le_score_budget T hn d hd hs) hn0.le
  have hsqrt := Real.sq_sqrt (div_nonneg (scoreVariance_nonneg T) hn0.le)
  have he : (4*d^2/n)/n=(2*d/n)^2 := by field_simp; ring
  rw [he] at hvar
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0≤2*d/n)).mp
  rwa [hsqrt]

theorem preconditionedDeletedMarginalBudget_le_small_score {n t : ℕ} (T : Tournament n)
    (hn : 2 ≤ n) (d : ℝ) (hd : 0 ≤ d) (hs : ∀ i, |score T i| ≤ d) :
    preconditionedDeletedMarginalBudget n t (scoreVariance T) (1/2) ≤
      64*(d+(t : ℝ)+1)/n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have h := mul_le_mul_of_nonneg_left (score_sqrt_le_score_budget T hn d hd hs) (by norm_num : (0 : ℝ)≤32)
  unfold preconditionedDeletedMarginalBudget
  norm_num only at ⊢
  have he : 64*(d+(t : ℝ)+1)/n = 32*(2*d/n)+32*(t : ℝ)/n+4*(1+4*(t : ℝ))/n+
      (16*(t : ℝ)+60)/n := by ring
  rw [he]
  linarith [div_nonneg (by positivity : (0 : ℝ)≤16*(t : ℝ)+60) hn0.le]

theorem rectangularScaling_capacity_le_marginal_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι κ ℝ) (e : ι ≃ κ) (K C q eps delta : ℝ) (hd : 0≤delta)
    (x : ι → ℝ) (y : κ → ℝ) (hxy : RectangularScalingWitness X e K C q eps x y)
    (hr : ∀ i, |matrixRowError X i|≤delta) (hc : ∀ j, |matrixColumnError X j|≤delta) :
    |(∑ i,x i)+(∑ j,y j)| ≤
      128*localScalingInverseBudget C q^2*(Fintype.card ι : ℝ)*delta^2 := by
  rw [abs_of_nonneg hxy.capacity_nonneg]
  have hnorm := rectangularMarginalVector_euclidean_le X e delta hd hr hc
  have hsq := (sq_le_sq₀ (localEuclideanNorm_nonneg _) (by positivity : 0≤2*Real.sqrt (Fintype.card ι : ℝ)*delta)).mpr hnorm
  have hm : (0 : ℝ)≤Fintype.card ι := Nat.cast_nonneg _
  calc
    _ ≤ 32*localScalingInverseBudget C q^2*localEuclideanNorm (rectangularMarginalVector X)^2 := hxy.capacity_upper
    _ ≤ 32*localScalingInverseBudget C q^2*(2*Real.sqrt (Fintype.card ι : ℝ)*delta)^2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt hm]; ring

end TournamentHamiltonian
