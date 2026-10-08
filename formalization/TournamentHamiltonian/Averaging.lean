import TournamentHamiltonian.Orientation
import Mathlib.Data.Fintype.Card

/-! The random-tournament expectation and the averaging lower bound, proved
by finite counting. Independent edge probabilities are not assumed as an axiom. -/

namespace TournamentHamiltonian

open scoped Classical

noncomputable def fixedAssignmentsEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (f : α → Bool) :
    {ω : α → Bool // ∀ i ∈ s, ω i = f i} ≃ ({i : α // i ∉ s} → Bool) where
  toFun ω i := ω.val i.val
  invFun g := ⟨fun i => if h : i ∈ s then f i else g ⟨i, h⟩, by
    intro i hi
    simp [hi]⟩
  left_inv ω := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp [hi, ω.property i hi]
    · simp [hi]
  right_inv g := by
    funext i
    simp [i.property]

theorem fixedAssignments_card {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (f : α → Bool) :
    Fintype.card {ω : α → Bool // ∀ i ∈ s, ω i = f i} =
      2 ^ (Fintype.card α - s.card) := by
  classical
  rw [Fintype.card_congr (fixedAssignmentsEquiv s f)]
  simp [Fintype.card_subtype_compl, Fintype.card_coe]

/-- Every prescribed permutation appears in exactly this many orientations.
The theorem also covers a single vertex, where no edges are constrained. -/
theorem path_completions_card {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    (Finset.univ.filter (fun ω : Edge (n + 1) → Bool =>
      IsHamiltonian (tournamentOfOrientation ω) σ)).card =
      2 ^ (Fintype.card (Edge (n + 1)) - n) := by
  classical
  simp_rw [isHamiltonian_iff_fixed_edges]
  rw [← Fintype.card_subtype]
  rw [fixedAssignments_card, pathEdges_card]

/-- Sum of all path counts over independent tournament orientations. -/
theorem total_pathCount (n : ℕ) :
    (∑ ω : Edge (n + 1) → Bool, pathCount (tournamentOfOrientation ω)) =
      Nat.factorial (n + 1) * 2 ^ (Fintype.card (Edge (n + 1)) - n) := by
  classical
  unfold pathCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hinner (σ : Equiv.Perm (Fin (n + 1))) :
      (∑ ω : Edge (n + 1) → Bool,
        if IsHamiltonian (tournamentOfOrientation ω) σ then 1 else 0) =
          2 ^ (Fintype.card (Edge (n + 1)) - n) := by
    simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using path_completions_card σ
  simp_rw [hinner]
  simp [Fintype.card_perm]

/-- Uniformly averaging all independent orientations gives exactly mu_n. -/
theorem meanPaths_eq_orientation_average (n : ℕ) :
    (∑ ω : Edge (n + 1) → Bool, (pathCount (tournamentOfOrientation ω) : ℝ)) /
        (Fintype.card (Edge (n + 1) → Bool) : ℝ) = meanPaths (n + 1) := by
  classical
  let m := Fintype.card (Edge (n + 1))
  have hmn : n ≤ m := by
    have h := Finset.card_le_univ (pathEdges (Equiv.refl (Fin (n + 1))))
    simpa [pathEdges_card, m] using h
  have hpow : (2 : ℝ) ^ m = 2 ^ n * 2 ^ (m - n) := by
    rw [← pow_add, Nat.add_sub_of_le hmn]
  rw [← Nat.cast_sum, total_pathCount]
  simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, meanPaths, Nat.add_sub_cancel]
  change (Nat.factorial (n + 1) : ℝ) * 2 ^ (m - n) / 2 ^ m =
    (Nat.factorial (n + 1) : ℝ) / 2 ^ n
  rw [hpow]
  field_simp

theorem factorial_le_pow_mul_maxPaths (n : ℕ) :
    Nat.factorial (n + 1) ≤ 2 ^ n * maxPaths (n + 1) := by
  classical
  let m := Fintype.card (Edge (n + 1))
  have hmn : n ≤ m := by
    have h := Finset.card_le_univ (pathEdges (Equiv.refl (Fin (n + 1))))
    simpa [pathEdges_card, m] using h
  have hsum : (∑ ω : Edge (n + 1) → Bool, pathCount (tournamentOfOrientation ω)) ≤
      2 ^ m * maxPaths (n + 1) := by
    calc
      _ ≤ ∑ _ω : Edge (n + 1) → Bool, maxPaths (n + 1) :=
        Finset.sum_le_sum (fun ω _ => pathCount_le_maxPaths (tournamentOfOrientation ω))
      _ = _ := by simp [m]
  rw [total_pathCount] at hsum
  change Nat.factorial (n + 1) * 2 ^ (m - n) ≤ 2 ^ m * maxPaths (n + 1) at hsum
  have hpow : 2 ^ m = 2 ^ n * 2 ^ (m - n) := by
    rw [← pow_add, Nat.add_sub_of_le hmn]
  have hsum' : Nat.factorial (n + 1) * 2 ^ (m - n) ≤
      (2 ^ n * maxPaths (n + 1)) * 2 ^ (m - n) := by
    simpa [hpow, mul_assoc, mul_comm, mul_left_comm] using hsum
  exact Nat.le_of_mul_le_mul_right hsum' (by positivity)

/-- The unconditional averaging bound used to exclude exceptional vertices. -/
theorem meanPaths_le_maxPaths (n : ℕ) (hn : 1 ≤ n) :
    meanPaths n ≤ (maxPaths n : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := factorial_le_pow_mul_maxPaths k
  unfold meanPaths
  simp only [Nat.succ_sub_one]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)).2
  exact_mod_cast (by simpa [mul_comm] using h :
    Nat.factorial (k + 1) ≤ maxPaths (k + 1) * 2 ^ k)

end TournamentHamiltonian
