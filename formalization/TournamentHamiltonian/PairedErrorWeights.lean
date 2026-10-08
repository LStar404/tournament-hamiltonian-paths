import TournamentHamiltonian.PairedConvolutionWeights
import TournamentHamiltonian.PairedPermanentErrorBudget

/-! The full cardinality-linear Gaussian error is retained in actual paired
weights, including the t sqrt(tau/n) term. -/
namespace TournamentHamiltonian
open scoped Classical

noncomputable def pairedErrorWeight {n : ℕ} (T : Tournament n) (x : ℝ) (i : Fin n) : ℝ :=
  Real.exp x * (pairedLeft (tournamentScorePotential T i) * pairedRight (tournamentScorePotential T i))

theorem pairedErrorWeight_bounds {n : ℕ} (T : Tournament n) (a0 x : ℝ)
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    ∀ i, 1 ≤ pairedErrorWeight T x i ∧ pairedErrorWeight T x i ≤ pairedConvolutionWeightCap a0 1 := by
  have hd : 0 < 1 - a0 ^ 2 := by nlinarith
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
  change 1 ≤ Real.exp x * (pairedLeft a * pairedRight a) ∧
    Real.exp x * (pairedLeft a * pairedRight a) ≤ Real.exp 1 / (1 - a0 ^ 2)
  rw [hp]
  constructor
  · simpa only [one_mul] using mul_le_mul (Real.one_le_exp_iff.mpr hx0) hp0
      (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_nonneg x)
  · have h := mul_le_mul (Real.exp_le_exp.mpr hx1) hp1 (by positivity) (Real.exp_nonneg 1)
    simpa only [mul_one_div] using h

theorem pairedErrorWeight_excess {n : ℕ} (T : Tournament n) (hn : 0 < n) (a0 x : ℝ)
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    (∑ i, (pairedErrorWeight T x i - 1)) / n ≤
      Real.exp 1 * (scoreVariance T / ((1 - a0 ^ 2) * n) + x) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < 1 - a0 ^ 2 := by nlinarith
  have hW0 : 0 ≤ ∑ i, pairedW (tournamentScorePotential T i) := by
    apply Finset.sum_nonneg
    intro i _
    unfold pairedW
    have hs : tournamentScorePotential T i ^ 2 ≤ a0 ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) h0).mpr (ha i)
    exact div_nonneg (sq_nonneg _) (by linarith)
  have hmass := mul_le_mul (Real.exp_le_exp.mpr hx1)
    (preconditioned_W_le_variance T a0 h0 h1 ha) hW0 (Real.exp_nonneg 1)
  have hinc := (exp_sub_one_le_self_mul_exp x).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx1) hx0)
  have hsum : (∑ i, (pairedErrorWeight T x i - 1)) =
      Real.exp x * (∑ i, pairedW (tournamentScorePotential T i)) + (n : ℝ) * (Real.exp x - 1) := by
    have hp (i : Fin n) : -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1 := by
      have h := abs_le.mp (ha i)
      constructor <;> linarith
    simp only [pairedErrorWeight, pairedLeft_mul_right _ (hp _), mul_add, mul_one,
      show ∀ i, Real.exp x + Real.exp x * pairedW (tournamentScorePotential T i) - 1 =
        Real.exp x * pairedW (tournamentScorePotential T i) + (Real.exp x - 1) by intro i; ring,
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hsum]
  have h := div_le_div_of_nonneg_right
    (add_le_add hmass (mul_le_mul_of_nonneg_left hinc hn0.le)) hn0.le
  convert h using 1
  field_simp

theorem pairedErrorWeight_prod {n : ℕ} (T : Tournament n) (x : ℝ) (U : Finset (Fin n)) :
    (∏ i ∈ U, pairedErrorWeight T x i) = Real.exp ((U.card : ℝ) * x) *
      (∏ i ∈ U, pairedLeft (tournamentScorePotential T i)) *
      (∏ j ∈ U, pairedRight (tournamentScorePotential T j)) := by
  simp only [pairedErrorWeight, Finset.prod_mul_distrib, Finset.prod_const]
  rw [← Real.exp_nat_mul]
  ring

theorem pairedPermanentErrorBudget_card_split (n t : ℕ) (tau : ℝ) :
    pairedPermanentErrorBudget n t tau = pairedPermanentErrorBudget n 0 tau +
      (t : ℝ) * (Real.sqrt (tau / n) + 1 / n) + (t : ℝ) ^ 2 / n := by
  unfold pairedPermanentErrorBudget
  norm_num
  ring

end TournamentHamiltonian
