import TournamentHamiltonian.Bregman
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Order.Interval.Finset.Fin

/-! The exact row-order rank averaging needed by the random-greedy proof
of Brégman's bound. Ordered finite supports are counted explicitly. -/

namespace TournamentHamiltonian

open scoped Classical

noncomputable def orderedSupportRank {α : Type*} [LinearOrder α]
    (S : Finset α) (x : α) : ℕ := (S.filter (fun y => x ≤ y)).card

theorem orderedSupportRank_pos {α : Type*} [LinearOrder α]
    (S : Finset α) {x : α} (hx : x ∈ S) : 0 < orderedSupportRank S x := by
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, le_rfl⟩⟩

theorem orderedSupportRank_orderIso {α : Type*} [LinearOrder α]
    (S : Finset α) (k : Fin S.card) :
    orderedSupportRank S (S.orderIsoOfFin rfl k).val = S.card - k.val := by
  let e := S.orderIsoOfFin rfl
  have hf : S.filter (fun y => (e k).val ≤ y) =
      (Finset.Ici k).map (e.toEquiv.toEmbedding.trans (Function.Embedding.subtype _)) := by
    ext y
    constructor
    · intro hy
      have hys := (Finset.mem_filter.mp hy).1
      refine Finset.mem_map.mpr ⟨e.symm ⟨y, hys⟩, ?_, ?_⟩
      · apply Finset.mem_Ici.mpr
        apply e.le_iff_le.mp
        rw [e.apply_symm_apply]
        change (e k).val ≤ y
        exact (Finset.mem_filter.mp hy).2
      · simp
    · intro hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
      apply Finset.mem_filter.mpr
      exact ⟨(e j).property, e.monotone (Finset.mem_Ici.mp hj)⟩
  unfold orderedSupportRank
  rw [hf, Finset.card_map, Fin.card_Ici]

theorem orderedSupportRank_product {α : Type*} [LinearOrder α] (S : Finset α) :
    (∏ x ∈ S, orderedSupportRank S x) = S.card.factorial := by
  calc
    _ = ∏ x : S, orderedSupportRank S x.val := (Finset.prod_coe_sort _ _).symm
    _ = ∏ k : Fin S.card, orderedSupportRank S (S.orderIsoOfFin rfl k).val := by
      exact (Fintype.prod_equiv (S.orderIsoOfFin rfl).toEquiv (fun k =>
        orderedSupportRank S (S.orderIsoOfFin rfl k).val)
        (fun x : S => orderedSupportRank S x.val) (fun _ => rfl)).symm
    _ = ∏ k : Fin S.card, (S.card - k.val) := by simp_rw [orderedSupportRank_orderIso]
    _ = ∏ k : Fin S.card, (k.val + 1) := by
      apply Fintype.prod_equiv Fin.revPerm
      intro k
      change S.card - k.val = k.rev.val + 1
      rw [Fin.val_rev]
      omega
    _ = S.card.factorial := by
      rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => k + 1) S.card]
      exact (Nat.factorial_eq_prod_range_add_one _).symm

theorem orderedSupportRank_log_sum {α : Type*} [LinearOrder α] (S : Finset α) :
    (∑ x ∈ S, Real.log (orderedSupportRank S x : ℝ)) = Real.log (S.card.factorial : ℝ) := by
  rw [← Real.log_prod (fun x hx =>
    (Nat.cast_pos.mpr (orderedSupportRank_pos S hx) : (0 : ℝ) < _).ne'),
    ← Nat.cast_prod, orderedSupportRank_product]

noncomputable def rowOrderRank {α : Type*} [LinearOrder α]
    (S : Finset α) (τ : Equiv.Perm α) (x : α) : ℕ :=
  orderedSupportRank (S.map τ.symm.toEmbedding) (τ.symm x)

theorem rowOrderRank_pos {α : Type*} [LinearOrder α]
    (S : Finset α) (τ : Equiv.Perm α) {x : α} (hx : x ∈ S) : 0 < rowOrderRank S τ x :=
  orderedSupportRank_pos _ (Finset.mem_map.mpr ⟨x, hx, rfl⟩)

theorem rowOrderRank_log_sum {α : Type*} [LinearOrder α]
    (S : Finset α) (τ : Equiv.Perm α) :
    (∑ x ∈ S, Real.log (rowOrderRank S τ x : ℝ)) = Real.log (S.card.factorial : ℝ) := by
  have h := orderedSupportRank_log_sum (S.map τ.symm.toEmbedding)
  simpa only [Finset.sum_map, Finset.card_map, Equiv.toEmbedding_apply, rowOrderRank] using h

theorem rowOrderRank_left_mul {α : Type*} [LinearOrder α]
    (S : Finset α) (τ e : Equiv.Perm α)
    (he : S.map e.symm.toEmbedding = S) (x : α) :
    rowOrderRank S (e * τ) x = rowOrderRank S τ (e.symm x) := by
  have hm : S.map (e * τ).symm.toEmbedding =
      (S.map e.symm.toEmbedding).map τ.symm.toEmbedding := by
    rw [Finset.map_map]
    rfl
  unfold rowOrderRank
  rw [hm, he]
  rfl

theorem support_swap_map_eq {α : Type*} [DecidableEq α]
    (S : Finset α) (i j : α) (hi : i ∈ S) (hj : j ∈ S) :
    S.map (Equiv.swap i j).toEmbedding = S := by
  have hp (x : α) : Equiv.swap i j x ∈ S ↔ x ∈ S := by
    by_cases hx : x = i
    · subst x; simp [hi, hj]
    · by_cases hx' : x = j
      · subst x; simp [hi, hj]
      · simp [Equiv.swap_apply_of_ne_of_ne hx hx']
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (hp y).mpr hy
  · intro hx
    exact Finset.mem_map.mpr ⟨Equiv.swap i j x, (hp x).mpr hx, by simp⟩

/-- A fixed support element has the same rank distribution as every other
support element, by swapping their row labels. -/
theorem rowOrderRank_log_sum_eq {α : Type*} [Fintype α] [LinearOrder α]
    (S : Finset α) (i j : α) (hi : i ∈ S) (hj : j ∈ S) :
    (∑ τ : Equiv.Perm α, Real.log (rowOrderRank S τ i : ℝ)) =
      ∑ τ : Equiv.Perm α, Real.log (rowOrderRank S τ j : ℝ) := by
  let e := Equiv.swap i j
  calc
    _ = ∑ τ : Equiv.Perm α, Real.log (rowOrderRank S (e * τ) i : ℝ) :=
      ((Group.mulLeft_bijective e).sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro τ _
      have he : S.map e.symm.toEmbedding = S := by
        simpa only [e, Equiv.symm_swap] using support_swap_map_eq S i j hi hj
      rw [rowOrderRank_left_mul S τ e he]
      simp [e]

/-- Exact uniform rank averaging, with no probabilistic independence assumption. -/
theorem rowOrderRank_log_average {α : Type*} [Fintype α] [LinearOrder α]
    (S : Finset α) (i : α) (hi : i ∈ S) :
    (S.card : ℝ) * (∑ τ : Equiv.Perm α, Real.log (rowOrderRank S τ i : ℝ)) =
      (Nat.factorial (Fintype.card α) : ℝ) * Real.log (S.card.factorial : ℝ) := by
  calc
    _ = ∑ x ∈ S, ∑ τ : Equiv.Perm α, Real.log (rowOrderRank S τ x : ℝ) := by
      have he (x : α) (hx : x ∈ S) := rowOrderRank_log_sum_eq S i x hi hx
      simp_rw [← Finset.sum_congr rfl he]
      simp
    _ = ∑ τ : Equiv.Perm α, ∑ x ∈ S, Real.log (rowOrderRank S τ x : ℝ) := Finset.sum_comm
    _ = _ := by
      simp_rw [rowOrderRank_log_sum]
      simp [Fintype.card_perm]

end TournamentHamiltonian
