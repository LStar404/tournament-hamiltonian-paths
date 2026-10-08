import TournamentHamiltonian.ShortWeightedConvolution
import TournamentHamiltonian.PairedPermanentRestoration

/-! The actual paired weights in principal deletion restoration, including the
linear cardinality error, have uniformly bounded excess mass. -/
namespace TournamentHamiltonian
open scoped Classical

noncomputable def pairedConvolutionWeight {n : ℕ} (T : Tournament n) (K : ℝ) (i : Fin n) : ℝ :=
  Real.exp (K / n) * (pairedLeft (tournamentScorePotential T i) * pairedRight (tournamentScorePotential T i))

noncomputable def pairedConvolutionWeightCap (a0 K : ℝ) : ℝ := Real.exp K / (1 - a0 ^ 2)
noncomputable def pairedConvolutionExcessConstant (a0 K : ℝ) : ℝ :=
  Real.exp K * (1 / (1 - a0 ^ 2) + K)

theorem pairedConvolutionWeight_bounds {n : ℕ} (T : Tournament n) (hn : 1 ≤ n)
    (a0 K : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1) (hK : 0 ≤ K)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    ∀ i, 1 ≤ pairedConvolutionWeight T K i ∧ pairedConvolutionWeight T K i ≤ pairedConvolutionWeightCap a0 K := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < 1 - a0 ^ 2 := by nlinarith
  have he0 : 1 ≤ Real.exp (K / n) := Real.one_le_exp_iff.mpr (div_nonneg hK hn0.le)
  have he1 : Real.exp (K / n) ≤ Real.exp K := Real.exp_le_exp.mpr (div_le_self hK hn1)
  intro i
  let a := tournamentScorePotential T i
  have haa : -1 < a ∧ a < 1 := by have h := abs_le.mp (ha i); dsimp [a]; constructor <;> linarith
  have hasq : a ^ 2 ≤ a0 ^ 2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) h0).mpr (ha i)
  have hda : 0 < 1 - a ^ 2 := by linarith
  have hp : pairedLeft a * pairedRight a = 1 / (1 - a ^ 2) := by
    rw [pairedLeft_mul_right a haa, pairedW]
    field_simp
    ring
  have hp0 : 1 ≤ 1 / (1 - a ^ 2) := (le_div_iff₀ hda).mpr (by nlinarith [sq_nonneg a])
  have hp1 : 1 / (1 - a ^ 2) ≤ 1 / (1 - a0 ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) hd (by linarith)
  change 1 ≤ Real.exp (K / n) * (pairedLeft a * pairedRight a) ∧
    Real.exp (K / n) * (pairedLeft a * pairedRight a) ≤ Real.exp K / (1 - a0 ^ 2)
  rw [hp]
  constructor
  · exact (show (1 : ℝ) = 1 * 1 by ring).trans_le (mul_le_mul he0 hp0 (by norm_num) (Real.exp_nonneg _))
  · have h := mul_le_mul he1 hp1 (by positivity) (Real.exp_nonneg K)
    simpa only [mul_one_div] using h

theorem pairedConvolutionWeight_excess {n : ℕ} (T : Tournament n) (hn : 1 ≤ n)
    (a0 K : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1) (hK : 0 ≤ K)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    (∑ i, (pairedConvolutionWeight T K i - 1)) ≤
      pairedConvolutionExcessConstant a0 K * (scoreVariance T + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < 1 - a0 ^ 2 := by nlinarith
  have hτ := scoreVariance_nonneg T
  have he : Real.exp (K / n) ≤ Real.exp K := Real.exp_le_exp.mpr (div_le_self hK hn1)
  have hW0 : 0 ≤ ∑ i, pairedW (tournamentScorePotential T i) := by
    apply Finset.sum_nonneg
    intro i _
    unfold pairedW
    have hs : tournamentScorePotential T i ^ 2 ≤ a0 ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) h0).mpr (ha i)
    exact div_nonneg (sq_nonneg _) (by linarith)
  have hW := preconditioned_W_le_variance T a0 h0 h1 ha
  have hmass := mul_le_mul he hW hW0 (Real.exp_nonneg K)
  have hinc := mul_le_mul_of_nonneg_left (exp_sub_one_le_self_mul_exp (K / n)) hn0.le
  have hcancel : (n : ℝ) * (K / n * Real.exp (K / n)) = K * Real.exp (K / n) := by field_simp
  rw [hcancel] at hinc
  have hinc1 := hinc.trans (mul_le_mul_of_nonneg_left he hK)
  have hsum : (∑ i, (pairedConvolutionWeight T K i - 1)) =
      Real.exp (K / n) * (∑ i, pairedW (tournamentScorePotential T i)) +
        (n : ℝ) * (Real.exp (K / n) - 1) := by
    have hp (i : Fin n) : -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1 := by
      have h := abs_le.mp (ha i)
      constructor <;> linarith
    simp only [pairedConvolutionWeight, pairedLeft_mul_right _ (hp _), mul_add, mul_one,
      show ∀ i, Real.exp (K / n) + Real.exp (K / n) * pairedW (tournamentScorePotential T i) - 1 =
        Real.exp (K / n) * pairedW (tournamentScorePotential T i) + (Real.exp (K / n) - 1) by intro i; ring,
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hsum]
  apply (add_le_add hmass hinc1).trans
  dsimp [pairedConvolutionExcessConstant]
  have hτK : 0 ≤ K * scoreVariance T := mul_nonneg hK hτ
  have hdinv : 0 ≤ 1 / (1 - a0 ^ 2) := by positivity
  calc
    _ = Real.exp K * (scoreVariance T * (1 / (1 - a0 ^ 2)) + K) := by ring
    _ ≤ Real.exp K * ((1 / (1 - a0 ^ 2) + K) * (scoreVariance T + 1)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (Real.exp_nonneg K)
    _ = _ := by ring

end TournamentHamiltonian
