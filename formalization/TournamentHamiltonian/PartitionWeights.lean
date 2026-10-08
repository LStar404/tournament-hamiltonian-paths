import TournamentHamiltonian.PartitionExpansion
import Mathlib.Order.LatticeIntervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Pi.Interval

/-! Explicit weights for the actual finite partition lattice. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section IncidenceHelpers

variable {Λ Ω R : Type*} [Fintype Λ] [DecidableEq Λ] [PartialOrder Λ] [OrderBot Λ]
  [LocallyFiniteOrder Λ] [CommRing R]

theorem mu_bottom_prefix_sum (P : Λ) :
    (∑ Q ∈ Finset.univ.filter (fun Q : Λ => Q ≤ P), IncidenceAlgebra.mu R ⊥ Q) =
      if P = ⊥ then 1 else 0 := by
  classical
  have he : Finset.univ.filter (fun Q : Λ => Q ≤ P) = Finset.Icc ⊥ P := by
    ext Q
    simp
  rw [he, IncidenceAlgebra.sum_Icc_mu_right]
  simp only [eq_comm]

theorem mu_bottom_eq_of_prefix_sums (f : Λ → R)
    (hf : ∀ P, (∑ Q ∈ Finset.univ.filter (fun Q : Λ => Q ≤ P), f Q) =
      if P = ⊥ then 1 else 0) (P : Λ) : f P = IncidenceAlgebra.mu R ⊥ P := by
  classical
  let g (Q : Λ) : R := if Q = ⊥ then 1 else 0
  have h (Q : Λ) : g Q = ∑ X ∈ Finset.Iic Q, f X := by
    have he : Finset.univ.filter (fun X : Λ => X ≤ Q) = Finset.Iic Q := by ext; simp
    simpa only [he, g] using (hf Q).symm
  have hi := IncidenceAlgebra.moebius_inversion_bot f g h P
  simpa [g, mul_ite] using hi

theorem mu_bottom_orderIso [Fintype Ω] [DecidableEq Ω] [PartialOrder Ω] [OrderBot Ω]
    [LocallyFiniteOrder Ω] (e : Λ ≃o Ω) (P : Λ) :
    IncidenceAlgebra.mu R ⊥ (e P) = IncidenceAlgebra.mu R ⊥ P := by
  classical
  apply mu_bottom_eq_of_prefix_sums
    (fun Q : Λ => IncidenceAlgebra.mu R ⊥ (e Q)) _ P
  intro Q
  have he : (∑ X ∈ Finset.univ.filter (fun X : Λ => X ≤ Q), IncidenceAlgebra.mu R ⊥ (e X)) =
      ∑ Y ∈ Finset.univ.filter (fun Y : Ω => Y ≤ e Q), IncidenceAlgebra.mu R ⊥ Y := by
    simp only [Finset.sum_filter]
    apply Fintype.sum_equiv e.toEquiv
    intro X
    simp
  rw [he, mu_bottom_prefix_sum]
  have hb : e Q = ⊥ ↔ Q = ⊥ := by rw [← e.map_bot, e.injective.eq_iff]
  simp only [hb]

theorem mu_bottom_Iic (P : Λ) (Q : Set.Iic P) :
    IncidenceAlgebra.mu R (⊥ : Set.Iic P) Q = IncidenceAlgebra.mu R (⊥ : Λ) Q.val := by
  symm
  apply mu_bottom_eq_of_prefix_sums
    (fun X : Set.Iic P => IncidenceAlgebra.mu R (⊥ : Λ) X.val) _ Q
  intro X
  have he : (∑ Y ∈ Finset.univ.filter (fun Y : Set.Iic P => Y ≤ X),
      IncidenceAlgebra.mu R (⊥ : Λ) Y.val) =
      ∑ Y ∈ Finset.univ.filter (fun Y : Λ => Y ≤ X.val),
        IncidenceAlgebra.mu R (⊥ : Λ) Y := by
    rw [Finset.sum_filter]
    calc
      _ = ∑ Y : Set.Iic P, if Y.val ≤ X.val then IncidenceAlgebra.mu R (⊥ : Λ) Y.val else 0 := rfl
      _ = ∑ Y ∈ Finset.univ.filter (fun Y : Λ => Y ≤ P),
          if Y ≤ X.val then IncidenceAlgebra.mu R (⊥ : Λ) Y else 0 :=
        (Finset.sum_subtype (p := fun Y : Λ => Y ≤ P)
          (Finset.univ.filter (fun Y : Λ => Y ≤ P)) (by simp)
          (fun Y => if Y ≤ X.val then IncidenceAlgebra.mu R (⊥ : Λ) Y else 0)).symm
      _ = _ := by
        simp only [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro Y _
        by_cases hy : Y ≤ X.val
        · simp [hy, hy.trans X.property]
        · simp [hy]
  rw [he, mu_bottom_prefix_sum]
  have hb : X.val = ⊥ ↔ X = ⊥ := by
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  simp only [hb]

theorem mu_bottom_cast (P : Λ) :
    IncidenceAlgebra.mu R ⊥ P = (IncidenceAlgebra.mu ℤ ⊥ P : ℤ) := by
  symm
  apply mu_bottom_eq_of_prefix_sums (R := R) (fun Q : Λ => (IncidenceAlgebra.mu ℤ ⊥ Q : ℤ)) _ P
  intro Q
  rw [← Int.cast_sum, mu_bottom_prefix_sum]
  split_ifs <;> simp

end IncidenceHelpers

theorem mu_bottom_pi {α : Type*} [Fintype α] [DecidableEq α] {β : α → Type*}
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)] [∀ i, PartialOrder (β i)]
    [∀ i, OrderBot (β i)] [∀ i, LocallyFiniteOrder (β i)]
    {R : Type*} [CommRing R] (P : ∀ i, β i) :
    IncidenceAlgebra.mu R (⊥ : ∀ i, β i) P =
      ∏ i : α, IncidenceAlgebra.mu R (⊥ : β i) (P i) := by
  symm
  apply mu_bottom_eq_of_prefix_sums (fun Q : ∀ i, β i =>
    ∏ i : α, IncidenceAlgebra.mu R (⊥ : β i) (Q i)) _ P
  intro Q
  calc
    _ = ∑ X : ∀ i, β i,
        ∏ i : α, if X i ≤ Q i then IncidenceAlgebra.mu R (⊥ : β i) (X i) else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro X _
      by_cases hx : X ≤ Q
      · simp only [hx, ite_true]
        apply Finset.prod_congr rfl
        intro i _
        simp [hx i]
      · rw [ite_eq_right hx]
        symm
        obtain ⟨i, hi⟩ := not_forall.mp hx
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]
    _ = ∏ i : α, ∑ X : β i,
        if X ≤ Q i then IncidenceAlgebra.mu R (⊥ : β i) X else 0 := by
      rw [Fintype.prod_sum]
    _ = ∏ i : α, if Q i = ⊥ then (1 : R) else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [Finset.sum_filter] using mu_bottom_prefix_sum (R := R) (Q i)
    _ = _ := by
      by_cases hq : Q = ⊥
      · simp [hq]
      · rw [ite_eq_right hq]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hq
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp only [Pi.bot_apply] at hi
        simp [hi]

section PartitionInterval

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The actual set of edge labels in one partition block. -/
abbrev PartitionBlock (P : Setoid κ) (v : Quotient P) :=
  {i : κ // Quotient.mk P i = v}

private noncomputable def assembleRefinement (P : Setoid κ)
    (F : ∀ v : Quotient P, Setoid (PartitionBlock P v)) : Setoid κ where
  r i j := ∃ v : Quotient P, ∃ hi : Quotient.mk P i = v,
    ∃ hj : Quotient.mk P j = v, F v ⟨i, hi⟩ ⟨j, hj⟩
  iseqv := {
    refl i := ⟨Quotient.mk P i, rfl, rfl, (F _).refl _⟩
    symm := by
      rintro i j ⟨v, hi, hj, h⟩
      exact ⟨v, hj, hi, (F v).symm h⟩
    trans := by
      rintro i j k ⟨v, hi, hj, hij⟩ ⟨w, hj', hk, hjk⟩
      have hvw : v = w := hj.symm.trans hj'
      cases hvw
      exact ⟨v, hi, hk, (F v).trans hij hjk⟩ }

omit [Fintype κ] [DecidableEq κ] in
private theorem assembleRefinement_le (P : Setoid κ)
    (F : ∀ v : Quotient P, Setoid (PartitionBlock P v)) : assembleRefinement P F ≤ P := by
  rintro i j ⟨v, hi, hj, _⟩
  exact Quotient.exact (hi.trans hj.symm)

/-- Refining `P` is exactly the same as independently partitioning each of its blocks. -/
noncomputable def partitionIntervalOrderIso (P : Setoid κ) :
    Set.Iic P ≃o (∀ v : Quotient P, Setoid (PartitionBlock P v)) where
  toFun Q v := Q.val.comap (Subtype.val : PartitionBlock P v → κ)
  invFun F := ⟨assembleRefinement P F, assembleRefinement_le P F⟩
  left_inv Q := by
    apply Subtype.ext
    apply Setoid.ext
    intro i j
    constructor
    · rintro ⟨v, hi, hj, h⟩
      exact h
    · intro h
      exact ⟨Quotient.mk P i, rfl, (Quotient.sound (Q.property h)).symm, h⟩
  right_inv F := by
    funext v
    apply Setoid.ext
    intro i j
    constructor
    · rintro ⟨w, hi, hj, h⟩
      have hvw : v = w := i.property.symm.trans hi
      cases hvw
      exact h
    · intro h
      exact ⟨v, i.property, j.property, h⟩
  map_rel_iff' := by
    intro Q Q'
    constructor
    · intro h i j hij
      let v := Quotient.mk P i
      have hj : Quotient.mk P j = v := (Quotient.sound (Q.property hij)).symm
      exact h v (x := ⟨i, rfl⟩) (y := ⟨j, hj⟩) hij
    · intro h v i j hij
      exact h hij

omit [DecidableEq κ] in
/-- General block factorization of the Möbius coefficient; no size restriction on blocks. -/
theorem partition_mu_eq_product_blocks {R : Type*} [CommRing R] (P : Setoid κ) :
    IncidenceAlgebra.mu R (⊥ : Setoid κ) P =
      ∏ v : Quotient P,
        IncidenceAlgebra.mu R (⊥ : Setoid (PartitionBlock P v)) ⊤ := by
  let e := partitionIntervalOrderIso P
  calc
    _ = IncidenceAlgebra.mu R (⊥ : Set.Iic P) ⊤ := (mu_bottom_Iic P ⊤).symm
    _ = IncidenceAlgebra.mu R (⊥ : ∀ v : Quotient P, Setoid (PartitionBlock P v)) ⊤ := by
      rw [← e.map_top]
      exact (mu_bottom_orderIso e ⊤).symm
    _ = _ := mu_bottom_pi ⊤

theorem setoid_mu_top_of_card_two {α : Type*} [Fintype α] [DecidableEq α]
    {R : Type*} [CommRing R] (hα : Fintype.card α = 2) :
    IncidenceAlgebra.mu R (⊥ : Setoid α) ⊤ = -1 := by
  have hc : (Finset.univ : Finset α).card = 2 := hα
  obtain ⟨i, j, hij, hen⟩ := Finset.card_eq_two.mp hc
  have henum (a : α) : a = i ∨ a = j := by
    have ha := Finset.mem_univ a
    simpa only [hen, Finset.mem_insert, Finset.mem_singleton] using ha
  have hs (Q : Setoid α) : Q = ⊥ ∨ Q = ⊤ := by
    by_cases hq : Q i j
    · right
      apply Setoid.eq_top_iff.mpr
      intro a b
      rcases henum a with rfl | rfl <;> rcases henum b with rfl | rfl
      · exact Q.refl _
      · exact hq
      · exact Q.symm hq
      · exact Q.refl _
    · have hq' : ¬ Q j i := fun h => hq (Q.symm h)
      left
      apply Setoid.ext
      intro a b
      rcases henum a with rfl | rfl <;> rcases henum b with rfl | rfl
      · simp
      · simp [hq, hij]
      · simp [hq', hij.symm]
      · simp
  have hbt : (⊥ : Setoid α) ≠ ⊤ := by
    intro h
    have hh : (⊥ : Setoid α) i j := h.symm ▸ (show (⊤ : Setoid α) i j from trivial)
    exact hij hh
  have hI : Finset.Ico (⊥ : Setoid α) ⊤ = {⊥} := by
    ext Q
    simp only [Finset.mem_Ico, bot_le, true_and, Finset.mem_singleton]
    constructor
    · intro hQ
      exact (hs Q).resolve_right (ne_of_lt hQ)
    · intro hQ
      subst Q
      exact lt_of_le_of_ne bot_le hbt
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hbt, hI]
  simp

/-- The exact Wick-pairing Möbius sign, including the empty partition. -/
theorem partition_mu_of_pair_blocks {R : Type*} [CommRing R] (P : Setoid κ)
    (hP : ∀ v : Quotient P, Fintype.card (PartitionBlock P v) = 2) :
    IncidenceAlgebra.mu R (⊥ : Setoid κ) P = (-1 : R) ^ Fintype.card (Quotient P) := by
  rw [partition_mu_eq_product_blocks]
  simp_rw [setoid_mu_top_of_card_two (hP _)]
  exact Finset.prod_const _

omit [DecidableEq κ] in
theorem partitionBlock_card_eq_degree (P : Setoid κ) (v : Quotient P) :
    Fintype.card (PartitionBlock P v) = coordinatePartitionDegree P v := by
  exact Fintype.card_of_subtype (Finset.univ.filter (fun i : κ => Quotient.mk P i = v)) (by simp)

theorem partition_mu_of_degree_two {R : Type*} [CommRing R] (P : Setoid κ)
    (hP : ∀ v : Quotient P, coordinatePartitionDegree P v = 2) :
    IncidenceAlgebra.mu R (⊥ : Setoid κ) P = (-1 : R) ^ Fintype.card (Quotient P) := by
  apply partition_mu_of_pair_blocks
  intro v
  rw [partitionBlock_card_eq_degree, hP]

omit [DecidableEq κ] in
theorem partition_block_card_sum (P : Setoid κ) :
    (∑ v : Quotient P, Fintype.card (PartitionBlock P v)) = Fintype.card κ := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk P))

omit [DecidableEq κ] in
theorem pair_partition_card (P : Setoid κ)
    (hP : ∀ v : Quotient P, Fintype.card (PartitionBlock P v) = 2) :
    Fintype.card κ = 2 * Fintype.card (Quotient P) := by
  rw [← partition_block_card_sum P]
  simp [hP, mul_comm]

/-- Two Wick pairing partitions have product Möbius weight exactly one. -/
theorem pair_partition_mu_product {R : Type*} [CommRing R] (P Q : Setoid κ)
    (hP : ∀ v : Quotient P, Fintype.card (PartitionBlock P v) = 2)
    (hQ : ∀ v : Quotient Q, Fintype.card (PartitionBlock Q v) = 2) :
    IncidenceAlgebra.mu R (⊥ : Setoid κ) P * IncidenceAlgebra.mu R (⊥ : Setoid κ) Q = 1 := by
  have hc : Fintype.card (Quotient P) = Fintype.card (Quotient Q) := by
    have hp := pair_partition_card P hP
    have hq := pair_partition_card Q hQ
    omega
  rw [partition_mu_of_pair_blocks P hP, partition_mu_of_pair_blocks Q hQ, hc, ← pow_add,
    show Fintype.card (Quotient Q) + Fintype.card (Quotient Q) =
      2 * Fintype.card (Quotient Q) by omega, pow_mul]
  simp

theorem setoid_mu_top_of_card_one {α : Type*} [Fintype α] [DecidableEq α]
    {R : Type*} [CommRing R] (hα : Fintype.card α = 1) :
    IncidenceAlgebra.mu R (⊥ : Setoid α) ⊤ = 1 := by
  have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hα.le
  have hbt : (⊥ : Setoid α) = ⊤ := by
    apply Setoid.ext
    intro a b
    simp [Subsingleton.elim a b]
  rw [hbt]
  exact IncidenceAlgebra.mu_self _

omit [DecidableEq κ] in
theorem partitionBlock_card_pos (P : Setoid κ) (v : Quotient P) :
    0 < Fintype.card (PartitionBlock P v) := by
  induction v using Quotient.inductionOn with
  | h e =>
    have : Nonempty (PartitionBlock P (Quotient.mk P e)) := ⟨⟨e, rfl⟩⟩
    exact Fintype.card_pos

/-- Explicit manuscript block weights for arbitrary mixtures of singleton and pair blocks. -/
theorem partition_mu_block_weights_of_card_le_two {R : Type*} [CommRing R] (P : Setoid κ)
    (hP : ∀ v : Quotient P, Fintype.card (PartitionBlock P v) ≤ 2) :
    IncidenceAlgebra.mu R (⊥ : Setoid κ) P =
      ∏ v : Quotient P, (-1 : R) ^ (Fintype.card (PartitionBlock P v) - 1) *
        ((Fintype.card (PartitionBlock P v) - 1).factorial : R) := by
  rw [partition_mu_eq_product_blocks]
  apply Finset.prod_congr rfl
  intro v _
  have hvpos := partitionBlock_card_pos P v
  have hvle := hP v
  have hv : Fintype.card (PartitionBlock P v) = 1 ∨
      Fintype.card (PartitionBlock P v) = 2 := by omega
  rcases hv with hv | hv
  · rw [setoid_mu_top_of_card_one hv, hv]
    simp
  · rw [setoid_mu_top_of_card_two hv, hv]
    simp

end PartitionInterval

end TournamentHamiltonian
