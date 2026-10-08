import TournamentHamiltonian.PreconditioningDisplacement

namespace TournamentHamiltonian

theorem pairedLeft_sub_one_sq_le (a a0 : ℝ) (h1 : a0 < 1) (ha : |a| ≤ a0) :
    (pairedLeft a - 1) ^ 2 ≤ a ^ 2 / (1 - a0) ^ 2 := by
  have hg : 0 < 1 - a0 := by linarith
  have hap := (abs_le.mp ha).1
  have hp : 0 < 1 + a := by linarith
  have he : pairedLeft a - 1 = -a / (1 + a) := by
    unfold pairedLeft
    field_simp
    ring
  rw [he, div_pow, neg_sq]
  apply div_le_div_of_nonneg_left (sq_nonneg a) (sq_pos_of_pos hg)
  nlinarith

theorem pairedRight_sub_one_sq_le (a a0 : ℝ) (h1 : a0 < 1) (ha : |a| ≤ a0) :
    (pairedRight a - 1) ^ 2 ≤ a ^ 2 / (1 - a0) ^ 2 := by
  have hg : 0 < 1 - a0 := by linarith
  have ham := (abs_le.mp ha).2
  have hm : 0 < 1 - a := by linarith
  have he : pairedRight a - 1 = a / (1 - a) := by
    unfold pairedRight
    field_simp
    ring
  rw [he, div_pow]
  apply div_le_div_of_nonneg_left (sq_nonneg a) (sq_pos_of_pos hg)
  nlinarith

theorem scaled_row_sum_sq_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (d l K v : ℝ) (_hl : 0 ≤ l) (_hK : 0 ≤ K)
    (hd : 0 ≤ d ∧ d ≤ l) (hM : ∀ i j, 0 ≤ M i j ∧ M i j ≤ K)
    (hb : (∑ j, b j ^ 2) ≤ v) (i : Fin n) :
    (d * ∑ j, M i j * b j) ^ 2 ≤ l ^ 2 * n * K ^ 2 * v := by
  have hv : 0 ≤ v := (Finset.sum_nonneg (fun j _ => sq_nonneg (b j))).trans hb
  have hMsq : (∑ j, M i j ^ 2) ≤ (n : ℝ) * K ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin n, K ^ 2 := Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (hM i j).1 (hM i j).2 2)
      _ = _ := by simp
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M i) b
  have hinner : (∑ j, M i j * b j) ^ 2 ≤ (n : ℝ) * K ^ 2 * v :=
    hc.trans (mul_le_mul hMsq hb (Finset.sum_nonneg (fun j _ => sq_nonneg (b j))) (by positivity))
  rw [mul_pow]
  exact (mul_le_mul (pow_le_pow_left₀ hd.1 hd.2 2) hinner (sq_nonneg _) (sq_nonneg l)).trans
    (le_of_eq (by ring))

private theorem marginal_budget_algebra (N tau a0 : ℝ) (hN : 2 ≤ N)
    (ht : 0 ≤ tau) (h1 : a0 < 1) :
    (1 / (1 - a0)) ^ 2 * N * (2 / (N - 1)) ^ 2 * (tau / (1 - a0) ^ 2) ≤
      16 * tau / (N * (1 - a0) ^ 4) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hg : 0 < 1 - a0 := by linarith
  have he : (1 / (1 - a0)) ^ 2 * N * (2 / (N - 1)) ^ 2 * (tau / (1 - a0) ^ 2) =
      4 * N * tau / ((N - 1) ^ 2 * (1 - a0) ^ 4) := by field_simp; ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity : 0 < (N - 1) ^ 2 * (1 - a0) ^ 4)
    (by positivity : 0 < N * (1 - a0) ^ 4)).mpr
  have hnSq : N ^ 2 ≤ 4 * (N - 1) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ N - 2 by linarith) (show 0 ≤ 3 * N - 2 by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hnSq (show 0 ≤ 4 * tau * (1 - a0) ^ 4 by positivity)]

theorem preconditioned_row_error_sq_bound {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) (i : Fin n) :
    matrixRowError (preconditionedTournamentDensity T) i ^ 2 ≤
      16 * scoreVariance T / ((n : ℝ) * (1 - a0) ^ 4) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hg : 0 < 1 - a0 := by linarith
  have ha' : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1 :=
    fun i => abs_lt.mp ((ha i).trans_lt h1)
  have hb : (∑ j, (pairedRight (tournamentScorePotential T j) - 1) ^ 2) ≤
      scoreVariance T / (1 - a0) ^ 2 := by
    rw [scoreVariance, Finset.sum_div]
    exact Finset.sum_le_sum (fun j _ => pairedRight_sub_one_sq_le _ a0 h1 (ha j))
  rw [preconditionedTournamentDensity_row_error T hn ha']
  exact (scaled_row_sum_sq_le (tournamentDensity T) (fun j => pairedRight (tournamentScorePotential T j) - 1)
    (pairedLeft (tournamentScorePotential T i)) (1 / (1 - a0)) (2 / (n - 1 : ℝ))
    (scoreVariance T / (1 - a0) ^ 2) (by positivity) (by positivity)
    ⟨pairedLeft_nonneg _ (ha' i).1, pairedLeft_le_bound _ a0 h1 (ha i)⟩
    (tournamentDensity_entry_bounds T hn) hb i).trans
    (marginal_budget_algebra n (scoreVariance T) a0 hnR (scoreVariance_nonneg T) h1)

theorem preconditioned_column_error_sq_bound {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) (j : Fin n) :
    matrixColumnError (preconditionedTournamentDensity T) j ^ 2 ≤
      16 * scoreVariance T / ((n : ℝ) * (1 - a0) ^ 4) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hg : 0 < 1 - a0 := by linarith
  have ha' : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1 :=
    fun i => abs_lt.mp ((ha i).trans_lt h1)
  have hb : (∑ i, (pairedLeft (tournamentScorePotential T i) - 1) ^ 2) ≤
      scoreVariance T / (1 - a0) ^ 2 := by
    rw [scoreVariance, Finset.sum_div]
    exact Finset.sum_le_sum (fun i _ => pairedLeft_sub_one_sq_le _ a0 h1 (ha i))
  rw [preconditionedTournamentDensity_column_error T hn ha']
  exact (scaled_row_sum_sq_le (tournamentDensity T).transpose (fun i => pairedLeft (tournamentScorePotential T i) - 1)
    (pairedRight (tournamentScorePotential T j)) (1 / (1 - a0)) (2 / (n - 1 : ℝ))
    (scoreVariance T / (1 - a0) ^ 2) (by positivity) (by positivity)
    ⟨pairedRight_nonneg _ (ha' j).2, pairedRight_le_bound _ a0 h1 (ha j)⟩
    (fun i k => tournamentDensity_entry_bounds T hn k i) hb j).trans
    (marginal_budget_algebra n (scoreVariance T) a0 hnR (scoreVariance_nonneg T) h1)

private theorem abs_marginal_of_sq_bound (x tau N a0 : ℝ) (ht : 0 ≤ tau)
    (hN : 0 < N) (h1 : a0 < 1) (h : x ^ 2 ≤ 16 * tau / (N * (1 - a0) ^ 4)) :
    |x| ≤ 4 / (1 - a0) ^ 2 * Real.sqrt (tau / N) := by
  have hg : 0 < 1 - a0 := by linarith
  apply (sq_le_sq₀ (abs_nonneg x) (by positivity)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (div_nonneg ht hN.le)]
  convert h using 1
  field_simp
  ring

theorem preconditioned_row_error_abs_bound {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) (i : Fin n) :
    |matrixRowError (preconditionedTournamentDensity T) i| ≤
      4 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact abs_marginal_of_sq_bound _ _ _ _ (scoreVariance_nonneg T) hn0 h1
    (preconditioned_row_error_sq_bound T hn a0 h1 ha i)

theorem preconditioned_column_error_abs_bound {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) (j : Fin n) :
    |matrixColumnError (preconditionedTournamentDensity T) j| ≤
      4 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact abs_marginal_of_sq_bound _ _ _ _ (scoreVariance_nonneg T) hn0 h1
    (preconditioned_column_error_sq_bound T hn a0 h1 ha j)

theorem preconditioned_row_error_sum_sq_bound {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    (∑ i, matrixRowError (preconditionedTournamentDensity T) i ^ 2) ≤
      16 * scoreVariance T / (1 - a0) ^ 4 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  calc
    _ ≤ ∑ _i : Fin n, 16 * scoreVariance T / ((n : ℝ) * (1 - a0) ^ 4) :=
      Finset.sum_le_sum (fun i _ => preconditioned_row_error_sq_bound T hn a0 h1 ha i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

theorem preconditioned_column_error_sum_sq_bound {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    (∑ j, matrixColumnError (preconditionedTournamentDensity T) j ^ 2) ≤
      16 * scoreVariance T / (1 - a0) ^ 4 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  calc
    _ ≤ ∑ _j : Fin n, 16 * scoreVariance T / ((n : ℝ) * (1 - a0) ^ 4) :=
      Finset.sum_le_sum (fun j _ => preconditioned_column_error_sq_bound T hn a0 h1 ha j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

theorem preconditioned_marginal_error_sum_sq_bound {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    (∑ i, matrixRowError (preconditionedTournamentDensity T) i ^ 2) +
      (∑ j, matrixColumnError (preconditionedTournamentDensity T) j ^ 2) ≤
        32 * scoreVariance T / (1 - a0) ^ 4 := by
  have h := add_le_add (preconditioned_row_error_sum_sq_bound T hn a0 h1 ha)
    (preconditioned_column_error_sum_sq_bound T hn a0 h1 ha)
  convert h using 1; ring

end TournamentHamiltonian
