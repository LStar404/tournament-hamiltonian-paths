import TournamentHamiltonian.PermanentAnalyticTail
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

theorem polynomial_eval_one_split (p : Polynomial ℝ) (M : ℕ) :
    p.eval 1 = (∑ k ∈ Finset.range (M + 1), p.coeff k) +
      ∑ k ∈ p.support.filter (fun k => M < k), p.coeff k := by
  classical
  have heval : p.eval 1 = ∑ k ∈ p.support, p.coeff k := by
    simp [Polynomial.eval_eq_sum, Polynomial.sum]
  have hlow : (∑ k ∈ p.support.filter (fun k => ¬ M < k), p.coeff k) =
      ∑ k ∈ Finset.range (M + 1), p.coeff k := by
    apply Finset.sum_subset
    · intro k hk
      have hm := (Finset.mem_filter.mp hk).2
      exact Finset.mem_range.mpr (by omega)
    · intro k hk hnot
      have hkm := Finset.mem_range.mp hk
      have hnotmem : k ∉ p.support := by
        intro hmem
        exact hnot (Finset.mem_filter.mpr ⟨hmem, by omega⟩)
      exact Polynomial.notMem_support_iff.mp hnotmem
  rw [heval, ← Finset.sum_filter_add_sum_filter_not _ (fun k => M < k), hlow, add_comm]

/-- A genuine polynomial and a genuine nonnegative convergent series may be
compared by their finite coefficient window and their actual two tails. -/
theorem polynomial_nonnegative_series_comparison (p : Polynomial ℝ) (g : ℕ → ℝ)
    (G K T U : ℝ) (hg : ∀ k, 0 ≤ g k) (hG : HasSum g G) (M : ℕ)
    (hwindow : (∑ k ∈ Finset.range (M + 1), |p.coeff k - g k|) ≤ K)
    (hpTail : (∑ k ∈ p.support.filter (fun k => M < k), |p.coeff k|) ≤ T)
    (hgTail : (∑' k, g (k + (M + 1))) ≤ U) :
    |p.eval 1 - G| ≤ K + T + U := by
  have hgs := Summable.sum_add_tsum_nat_add (M + 1) hG.summable
  rw [hG.tsum_eq] at hgs
  have hgtail0 : 0 ≤ ∑' k, g (k + (M + 1)) := tsum_nonneg (fun k => hg _)
  have heq : p.eval 1 - G =
      (∑ k ∈ Finset.range (M + 1), (p.coeff k - g k)) +
        (∑ k ∈ p.support.filter (fun k => M < k), p.coeff k) -
          ∑' k, g (k + (M + 1)) := by
    rw [polynomial_eval_one_split, ← hgs, Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ |∑ k ∈ Finset.range (M + 1), (p.coeff k - g k)| +
        |∑ k ∈ p.support.filter (fun k => M < k), p.coeff k| +
          |∑' k, g (k + (M + 1))| :=
      (show |(∑ k ∈ Finset.range (M + 1), (p.coeff k - g k)) +
          (∑ k ∈ p.support.filter (fun k => M < k), p.coeff k) -
            ∑' k, g (k + (M + 1))| ≤
        |(∑ k ∈ Finset.range (M + 1), (p.coeff k - g k)) +
          (∑ k ∈ p.support.filter (fun k => M < k), p.coeff k)| +
            |∑' k, g (k + (M + 1))| by
          simpa only [Real.norm_eq_abs] using norm_sub_le
            ((∑ k ∈ Finset.range (M + 1), (p.coeff k - g k)) +
              (∑ k ∈ p.support.filter (fun k => M < k), p.coeff k))
            (∑' k, g (k + (M + 1)))).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K + T + U := add_le_add
      (add_le_add (Finset.abs_sum_le_sum_abs _ _ |>.trans hwindow)
        (Finset.abs_sum_le_sum_abs _ _ |>.trans hpTail))
      (by rwa [abs_of_nonneg hgtail0])

end TournamentHamiltonian
