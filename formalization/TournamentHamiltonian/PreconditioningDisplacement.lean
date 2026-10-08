import TournamentHamiltonian.PreconditioningBounds
import TournamentHamiltonian.GramLipschitz

open scoped Matrix.Norms.L2Operator

namespace TournamentHamiltonian

theorem pairedLeft_nonneg (a : ℝ) (ha : -1 < a) : 0 ≤ pairedLeft a := by
  unfold pairedLeft
  have h : 0 < 1 + a := by linarith
  positivity

theorem pairedRight_nonneg (a : ℝ) (ha : a < 1) : 0 ≤ pairedRight a := by
  unfold pairedRight
  have h : 0 < 1 - a := by linarith
  positivity

theorem pairedLeft_le_bound (a a0 : ℝ) (h1 : a0 < 1) (ha : |a| ≤ a0) :
    pairedLeft a ≤ 1 / (1 - a0) := by
  have hl : -a0 ≤ a := (abs_le.mp ha).1
  have hgap : 0 < 1 - a0 := by linarith
  unfold pairedLeft
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) hgap (by linarith)

theorem pairedRight_le_bound (a a0 : ℝ) (h1 : a0 < 1) (ha : |a| ≤ a0) :
    pairedRight a ≤ 1 / (1 - a0) := by
  have hu : a ≤ a0 := (abs_le.mp ha).2
  have hgap : 0 < 1 - a0 := by linarith
  unfold pairedRight
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) hgap (by linarith)

theorem paired_scale_difference_abs_le (a b a0 : ℝ) (_h0 : 0 ≤ a0) (h1 : a0 < 1)
    (ha : |a| ≤ a0) (hb : |b| ≤ a0) :
    |pairedLeft a * pairedRight b - 1| ≤ 2 * (|a| + |b|) / (1 - a0) ^ 2 := by
  have hgap : 0 < 1 - a0 := by linarith
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hp : 0 < 1 + a := by linarith
  have hm : 0 < 1 - b := by linarith
  have heq : pairedLeft a * pairedRight b - 1 = (-a + b + a * b) / ((1 + a) * (1 - b)) := by
    unfold pairedLeft pairedRight
    field_simp [hp.ne', hm.ne']
    ring
  have hden : (1 - a0) ^ 2 ≤ (1 + a) * (1 - b) := by
    have hprod := mul_le_mul (by linarith : 1 - a0 ≤ 1 + a)
      (by linarith : 1 - a0 ≤ 1 - b) hgap.le hp.le
    simpa only [pow_two] using hprod
  have hnum : |-a + b + a * b| ≤ 2 * (|a| + |b|) := by
    have hmul : |a| * |b| ≤ |a| := mul_le_of_le_one_right (abs_nonneg a) (hb.trans h1.le)
    have htri := abs_add_le (-a + b) (a * b)
    have htri' := abs_add_le (-a) b
    rw [abs_mul] at htri
    rw [abs_neg] at htri'
    nlinarith [abs_nonneg a, abs_nonneg b]
  rw [heq, abs_div, abs_of_pos (mul_pos hp hm)]
  exact (div_le_div_of_nonneg_right hnum (mul_pos hp hm).le).trans
    (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hgap) hden)

theorem real_opNorm_le_frobenius {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : ‖M‖ ≤ realFrobeniusNorm M := by
  rw [Matrix.cstar_norm_def (n := ι) (𝕜 := ℝ)]
  apply ContinuousLinearMap.opNorm_le_bound
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) (realFrobeniusNorm_nonneg M)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (realFrobeniusNorm_nonneg M) (norm_nonneg _))).mp
  rw [mul_pow, realFrobeniusNorm_sq]
  simp only [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, (∑ j, M i j * x j) ^ 2) ≤ (∑ i, ∑ j, M i j ^ 2) * ∑ j, x j ^ 2
  calc
    _ ≤ ∑ i, (∑ j, M i j ^ 2) * ∑ j, x j ^ 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M i) (fun j => x j))
    _ = _ := by rw [Finset.sum_mul]

theorem tournamentDensity_entry_bounds {n : ℕ} (T : Tournament n) (hn : 1 < n) (i j : Fin n) :
    0 ≤ tournamentDensity T i j ∧ tournamentDensity T i j ≤ 2 / (n - 1 : ℝ) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hscale : 0 ≤ (2 : ℝ) / (n - 1 : ℝ) := by positivity
  have hA : 0 ≤ adjacency T i j ∧ adjacency T i j ≤ 1 := by
    unfold adjacency
    split <;> norm_num
  simp only [tournamentDensity, Matrix.smul_apply, smul_eq_mul]
  constructor
  · exact mul_nonneg hscale hA.1
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hA.2 hscale

theorem preconditionedTournamentDensity_entry_bounds {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (_h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (i j : Fin n) :
    0 ≤ preconditionedTournamentDensity T i j ∧
      preconditionedTournamentDensity T i j ≤ 4 / ((1 - a0) ^ 2 * n) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hg : 0 < 1 - a0 := by linarith
  have ha' : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1 :=
    fun i => abs_lt.mp ((ha i).trans_lt h1)
  have hL := pairedLeft_nonneg _ (ha' i).1
  have hR := pairedRight_nonneg _ (ha' j).2
  have hC := tournamentDensity_entry_bounds T hn i j
  have hprod := mul_le_mul (pairedLeft_le_bound _ a0 h1 (ha i))
    (pairedRight_le_bound _ a0 h1 (ha j)) hR (by positivity : 0 ≤ 1 / (1 - a0))
  have hscaled : (2 : ℝ) / (n - 1 : ℝ) ≤ 4 / n := by
    apply (div_le_div_iff₀ (by linarith : 0 < (n : ℝ) - 1) (by linarith : 0 < (n : ℝ))).mpr
    linarith
  constructor
  · exact mul_nonneg (mul_nonneg hL hC.1) hR
  · change pairedLeft _ * tournamentDensity T i j * pairedRight _ ≤ _
    calc
      _ = (pairedLeft (tournamentScorePotential T i) * pairedRight (tournamentScorePotential T j)) *
          tournamentDensity T i j := by ring
      _ ≤ (1 / (1 - a0) * (1 / (1 - a0))) * (2 / (n - 1 : ℝ)) :=
        mul_le_mul hprod hC.2 hC.1 (by positivity)
      _ ≤ (1 / (1 - a0) * (1 / (1 - a0))) * (4 / n) :=
        mul_le_mul_of_nonneg_left hscaled (by positivity)
      _ = _ := by field_simp

noncomputable def preconditionedDensityDifference {n : ℕ} (T : Tournament n) :
    Matrix (Fin n) (Fin n) ℝ := preconditionedTournamentDensity T - tournamentDensity T

theorem preconditionedDensityDifference_entry_bound {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (i j : Fin n) :
    |preconditionedDensityDifference T i j| ≤
      4 * (|tournamentScorePotential T i| + |tournamentScorePotential T j|) /
        ((n - 1 : ℝ) * (1 - a0) ^ 2) := by
  have hg : 0 < 1 - a0 := by linarith
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hC := tournamentDensity_entry_bounds T hn i j
  have heq : preconditionedDensityDifference T i j = tournamentDensity T i j *
      (pairedLeft (tournamentScorePotential T i) * pairedRight (tournamentScorePotential T j) - 1) := by
    simp only [preconditionedDensityDifference, Matrix.sub_apply, preconditionedTournamentDensity]
    ring
  rw [heq, abs_mul, abs_of_nonneg hC.1]
  calc
    _ ≤ (2 / (n - 1 : ℝ)) *
        (2 * (|tournamentScorePotential T i| + |tournamentScorePotential T j|) / (1 - a0) ^ 2) :=
      mul_le_mul hC.2 (paired_scale_difference_abs_le _ _ a0 h0 h1 (ha i) (ha j))
        (abs_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

theorem preconditionedDensityDifference_frobenius_sq_bound {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    realFrobeniusNorm (preconditionedDensityDifference T) ^ 2 ≤
      64 * n * scoreVariance T / ((n - 1 : ℝ) ^ 2 * (1 - a0) ^ 4) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hg : 0 < 1 - a0 := by linarith
  let b : ℝ := 4 / ((n - 1 : ℝ) * (1 - a0) ^ 2)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have he (i j : Fin n) : preconditionedDensityDifference T i j ^ 2 ≤
      2 * b ^ 2 * (tournamentScorePotential T i ^ 2 + tournamentScorePotential T j ^ 2) := by
    have h := preconditionedDensityDifference_entry_bound T hn a0 h0 h1 ha i j
    have heq : 4 * (|tournamentScorePotential T i| + |tournamentScorePotential T j|) /
        ((n - 1 : ℝ) * (1 - a0) ^ 2) =
        b * (|tournamentScorePotential T i| + |tournamentScorePotential T j|) := by dsimp [b]; ring
    rw [heq] at h
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ b *
      (|tournamentScorePotential T i| + |tournamentScorePotential T j|))).mpr h
    rw [sq_abs] at hsq
    have ht : (|tournamentScorePotential T i| + |tournamentScorePotential T j|) ^ 2 ≤
        2 * (tournamentScorePotential T i ^ 2 + tournamentScorePotential T j ^ 2) := by
      nlinarith [sq_abs (tournamentScorePotential T i), sq_abs (tournamentScorePotential T j),
        sq_nonneg (|tournamentScorePotential T i| - |tournamentScorePotential T j|)]
    apply hsq.trans
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg b)]
  rw [realFrobeniusNorm_sq]
  calc
    _ ≤ ∑ i, ∑ j, 2 * b ^ 2 *
        (tournamentScorePotential T i ^ 2 + tournamentScorePotential T j ^ 2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => he i j))
    _ = 4 * n * b ^ 2 * scoreVariance T := by
      simp only [Finset.sum_add_distrib, mul_add, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold scoreVariance
      simp only [← Finset.mul_sum]
      ring
    _ = _ := by dsimp [b]; field_simp; ring

theorem preconditionedDensityDifference_frobenius_bound {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    realFrobeniusNorm (preconditionedDensityDifference T) ≤
      16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hg : 0 < 1 - a0 := by linarith
  have ht := scoreVariance_nonneg T
  have hs := preconditionedDensityDifference_frobenius_sq_bound T hn a0 h0 h1 ha
  have hratio : 64 * n * scoreVariance T / ((n - 1 : ℝ) ^ 2 * (1 - a0) ^ 4) ≤
      256 * scoreVariance T / ((n : ℝ) * (1 - a0) ^ 4) := by
    apply (div_le_div_iff₀ (by positivity : 0 < (n - 1 : ℝ) ^ 2 * (1 - a0) ^ 4)
      (by positivity : 0 < (n : ℝ) * (1 - a0) ^ 4)).mpr
    have hnSq : (n : ℝ) ^ 2 ≤ 4 * (n - 1 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) (show 0 ≤ 3 * (n : ℝ) - 2 by linarith)]
    have hmul := mul_le_mul_of_nonneg_right hnSq (show 0 ≤ 64 * scoreVariance T * (1 - a0) ^ 4 by positivity)
    nlinarith [hmul]
  apply (sq_le_sq₀ (realFrobeniusNorm_nonneg _) (by positivity)).mp
  have heq : (16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n)) ^ 2 =
      256 * scoreVariance T / ((n : ℝ) * (1 - a0) ^ 4) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ scoreVariance T / n)]
    field_simp; ring
  rw [heq]
  exact hs.trans hratio

theorem preconditionedDensityDifference_opNorm_bound {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1)
    (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    ‖preconditionedDensityDifference T‖ ≤
      16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) :=
  (real_opNorm_le_frobenius _).trans
    (preconditionedDensityDifference_frobenius_bound T hn a0 h0 h1 ha)

end TournamentHamiltonian
