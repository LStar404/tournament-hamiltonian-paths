import TournamentHamiltonian.CompressedCoreMajorant
import Mathlib.Analysis.SpecificLimits.Normed

namespace TournamentHamiltonian

noncomputable def excessWindowTerm (D : ℝ) (n j : ℕ) : ℝ :=
  (D * (j : ℝ) / (n : ℝ)) ^ j

theorem excessWindowTerm_nonneg (D : ℝ) (n j : ℕ) (hD : 0 ≤ D) :
    0 ≤ excessWindowTerm D n j := by unfold excessWindowTerm; positivity

theorem one_add_inv_pow_le_exp_one (j : ℕ) (hj : 1 ≤ j) :
    (1 + 1 / (j : ℝ)) ^ j ≤ Real.exp 1 := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 1 / (j : ℝ))
    (show 1 + 1 / (j : ℝ) ≤ Real.exp (1 / (j : ℝ)) by
      simpa only [add_comm] using Real.add_one_le_exp (1 / (j : ℝ))) j
  have heq : (j : ℝ) * (1 / (j : ℝ)) = 1 := by field_simp
  rw [← Real.exp_nat_mul, heq] at h
  simpa only [add_comm] using h

theorem excessWindowTerm_succ_le (D : ℝ) (n j : ℕ)
    (hD : 0 ≤ D) (hj : 1 ≤ j) :
    excessWindowTerm D n (j + 1) ≤
      (3 * D * ((j : ℝ) + 1) / n) * excessWindowTerm D n j := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hbase : D * ((j : ℝ) + 1) / n = (D * (j : ℝ) / n) * (1 + 1 / (j : ℝ)) := by
    field_simp [hj0]
  have heq : excessWindowTerm D n (j + 1) =
      (D * ((j : ℝ) + 1) / n) * excessWindowTerm D n j * (1 + 1 / (j : ℝ)) ^ j := by
    unfold excessWindowTerm
    push_cast
    rw [pow_succ, hbase, mul_pow]
    ring
  rw [heq]
  have h := (one_add_inv_pow_le_exp_one j hj).trans Real.exp_one_lt_three.le
  have hv := excessWindowTerm_nonneg D n j hD
  have hm := mul_le_mul_of_nonneg_left h (by positivity :
    0 ≤ (D * ((j : ℝ) + 1) / n) * excessWindowTerm D n j)
  exact hm.trans_eq (by ring)

theorem excessWindowTerm_half_ratio (D : ℝ) (n M j : ℕ)
    (hn : 0 < n) (hD : 0 ≤ D) (hM : 16 * D * (M : ℝ) ≤ n)
    (hj : 1 ≤ j) (hjM : j + 1 ≤ M) :
    excessWindowTerm D n (j + 1) ≤ (1 / 2) * excessWindowTerm D n j := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hjM' : (j : ℝ) + 1 ≤ M := by exact_mod_cast hjM
  have hprod := mul_le_mul_of_nonneg_left hjM' hD
  have hco : 3 * D * ((j : ℝ) + 1) / n ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith
  exact (excessWindowTerm_succ_le D n j hD hj).trans
    (mul_le_mul_of_nonneg_right hco (excessWindowTerm_nonneg D n j hD))

theorem excessWindowTerm_geometric_le (D : ℝ) (n M k : ℕ)
    (hn : 0 < n) (hD : 0 ≤ D) (hM : 16 * D * (M : ℝ) ≤ n) (hk : k + 2 ≤ M) :
    excessWindowTerm D n (k + 2) ≤ excessWindowTerm D n 2 * (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkM : k + 2 ≤ M := by omega
    have hratio := excessWindowTerm_half_ratio D n M (k + 2) hn hD hM (by omega) (by omega)
    have hmul := mul_le_mul_of_nonneg_left (ih hkM) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa only [Nat.succ_eq_add_one, pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      hratio.trans hmul

theorem finite_excess_window_tail_le (D : ℝ) (n M : ℕ)
    (hn : 0 < n) (hD : 0 ≤ D) (hM : 16 * D * (M : ℝ) ≤ n) :
    (∑ j ∈ Finset.Icc 2 M, excessWindowTerm D n j) ≤ 8 * D ^ 2 / (n : ℝ) ^ 2 := by
  have heq : Finset.Icc 2 M = Finset.Ico 2 (M + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [heq, Finset.sum_Ico_eq_sum_range]
  have hfinite : (∑ k ∈ Finset.range (M + 1 - 2), excessWindowTerm D n (2 + k)) ≤
      ∑ k ∈ Finset.range (M + 1 - 2), excessWindowTerm D n 2 * (1 / 2 : ℝ) ^ k := by
    apply Finset.sum_le_sum
    intro k hk
    have hkM : k + 2 ≤ M := by have h := Finset.mem_range.mp hk; omega
    simpa only [Nat.add_comm] using excessWindowTerm_geometric_le D n M k hn hD hM hkM
  have hs := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (excessWindowTerm D n 2)
  have hsum := hs.summable.sum_le_tsum (Finset.range (M + 1 - 2)) (fun _ _ =>
    mul_nonneg (excessWindowTerm_nonneg D n 2 hD) (by positivity))
  rw [hs.tsum_eq] at hsum
  have h := hfinite.trans hsum
  exact h.trans_eq (by unfold excessWindowTerm; norm_num; ring)

end TournamentHamiltonian
