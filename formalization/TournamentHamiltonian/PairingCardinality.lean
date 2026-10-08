import TournamentHamiltonian.PartitionWeights
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! Exact finite counting of partitions into pairs. The proof counts
fixed-point-free involutions by removing a chosen element and its partner,
then transports the count to the original Setoid partitions. -/

namespace TournamentHamiltonian

open scoped Classical

/-- The canonical Wick pairing predicate on the manuscript's Setoid partitions. -/
def IsPairingPartition {α : Type*} [Fintype α] (P : Setoid α) : Prop :=
  ∀ v : Quotient P, Fintype.card (PartitionBlock P v) = 2

abbrev PairingMap (α : Type*) :=
  {f : α → α // Function.Involutive f ∧ ∀ x, f x ≠ x}

abbrev PairRemainder {α : Type*} (x y : α) := {z : α // z ≠ x ∧ z ≠ y}

noncomputable def addPair {α : Type*} [DecidableEq α] (x y : α) (hy : y ≠ x)
    (f : PairingMap (PairRemainder x y)) : PairingMap α := by
  let g : α → α := fun z => if hx : z = x then y else if hz : z = y then x
    else (f.val ⟨z, hx, hz⟩).val
  have gx : g x = y := by simp [g]
  have gy : g y = x := by simp [g, hy]
  refine ⟨g, ?_, ?_⟩
  · intro z
    by_cases hx : z = x
    · subst z; rw [gx, gy]
    · by_cases hz : z = y
      · subst z; rw [gy, gx]
      · have hval : g z = (f.val ⟨z, hx, hz⟩).val := by simp [g, hx, hz]
        rw [hval]
        have hfne := (f.val ⟨z, hx, hz⟩).property
        simp only [g, dite_eq_right hfne.1, dite_eq_right hfne.2]
        exact congrArg Subtype.val (f.property.1 ⟨z, hx, hz⟩)
  · intro z
    by_cases hx : z = x
    · subst z; simpa only [gx] using hy
    · by_cases hz : z = y
      · subst z; simpa only [gy] using hy.symm
      · simp only [g, dite_eq_right hx, dite_eq_right hz]
        intro h
        exact f.property.2 ⟨z, hx, hz⟩ (Subtype.ext h)

@[simp] theorem addPair_apply_left {α : Type*} [DecidableEq α]
    (x y : α) (hy : y ≠ x) (f : PairingMap (PairRemainder x y)) :
    (addPair x y hy f).val x = y := by simp [addPair]

@[simp] theorem addPair_apply_right {α : Type*} [DecidableEq α]
    (x y : α) (hy : y ≠ x) (f : PairingMap (PairRemainder x y)) :
    (addPair x y hy f).val y = x := by simp [addPair, hy]

@[simp] theorem addPair_apply_remainder {α : Type*} [DecidableEq α]
    (x y : α) (hy : y ≠ x) (f : PairingMap (PairRemainder x y))
    (z : PairRemainder x y) : (addPair x y hy f).val z.val = (f.val z).val := by
  simp [addPair, z.property.1, z.property.2]

noncomputable def removePair {α : Type*} (x : α) (f : PairingMap α) :
    PairingMap (PairRemainder x (f.val x)) := by
  have hmap (z : PairRemainder x (f.val x)) : f.val z.val ≠ x ∧ f.val z.val ≠ f.val x := by
    constructor
    · intro h
      have hh := congrArg f.val h
      rw [f.property.1 z.val] at hh
      exact z.property.2 hh
    · exact fun h => z.property.1 (f.property.1.injective h)
  refine ⟨fun z => ⟨f.val z.val, hmap z⟩, ?_, ?_⟩
  · intro z
    apply Subtype.ext
    exact f.property.1 z.val
  · intro z h
    exact f.property.2 z.val (congrArg Subtype.val h)

/-- The chosen element's partner is independent of the remaining pairing. -/
noncomputable def addPairEquiv {α : Type*} [DecidableEq α] (x : α) :
    (Σ y : {y : α // y ≠ x}, PairingMap (PairRemainder x y.val)) ≃ PairingMap α :=
  Equiv.ofBijective (fun p => addPair x p.1.val p.1.property p.2) (by
    constructor
    · rintro ⟨y, f⟩ ⟨z, g⟩ h
      have hyz : y = z := Subtype.ext (by
        simpa using congrArg (fun q : PairingMap α => q.val x) h)
      cases hyz
      congr 1
      apply Subtype.ext
      funext w
      apply Subtype.ext
      simpa using congrArg (fun q : PairingMap α => q.val w.val) h
    · intro f
      refine ⟨⟨⟨f.val x, f.property.2 x⟩, removePair x f⟩, ?_⟩
      apply Subtype.ext
      funext z
      by_cases hx : z = x
      · subst z; simp
      · by_cases hz : z = f.val x
        · subst z
          simp [f.property.1 x]
        · have hr : z ∈ (Set.univ : Set α) := trivial
          change (addPair x (f.val x) (f.property.2 x) (removePair x f)).val z = f.val z
          simpa [removePair] using addPair_apply_remainder x (f.val x) (f.property.2 x)
            (removePair x f) (⟨z, hx, hz⟩ : PairRemainder x (f.val x)))

/-- The recurrence has the correct empty and odd-order conventions. -/
def pairingNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * pairingNumber n

theorem card_pairRemainder {α : Type*} [Fintype α] [DecidableEq α]
    (x y : α) (hy : y ≠ x) :
    Fintype.card (PairRemainder x y) = Fintype.card α - 2 := by
  let e : PairRemainder x y ≃ ((Finset.univ.erase x).erase y : Finset α) :=
    Equiv.subtypeEquivRight (fun z : α => by simp [and_comm])
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_erase_of_mem (by simp [hy]),
    Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
  omega

theorem card_other_elements {α : Type*} [Fintype α] [DecidableEq α] (x : α) :
    Fintype.card {y : α // y ≠ x} = Fintype.card α - 1 := by
  let e : {y : α // y ≠ x} ≃ (Finset.univ.erase x : Finset α) :=
    Equiv.subtypeEquivRight (fun z : α => by simp)
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ x),
    Finset.card_univ]

universe u

theorem pairingMap_card (α : Type u) [Fintype α] [DecidableEq α] :
    Fintype.card (PairingMap α) = pairingNumber (Fintype.card α) := by
  have h : ∀ m, ∀ (β : Type u) [Fintype β] [DecidableEq β],
      Fintype.card β = m → Fintype.card (PairingMap β) = pairingNumber m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro β _ _ hm
      cases m with
      | zero =>
        have : IsEmpty β := Fintype.card_eq_zero_iff.mp hm
        change Fintype.card (PairingMap β) = 1
        apply Fintype.card_eq_one_iff.mpr
        refine ⟨⟨fun x => isEmptyElim x, ?_, ?_⟩, ?_⟩
        · intro x; exact isEmptyElim x
        · intro x; exact isEmptyElim x
        · intro f
          apply Subtype.ext
          funext x
          exact isEmptyElim x
      | succ m =>
        cases m with
        | zero =>
          have : Subsingleton β := Fintype.card_le_one_iff_subsingleton.mp hm.le
          obtain ⟨x⟩ : Nonempty β := Fintype.card_pos_iff.mp (by omega)
          change Fintype.card (PairingMap β) = 0
          apply Fintype.card_eq_zero_iff.mpr
          exact ⟨fun f => f.property.2 x (Subsingleton.elim _ _)⟩
        | succ m =>
          obtain ⟨x⟩ : Nonempty β := Fintype.card_pos_iff.mp (by omega)
          calc
            _ = Fintype.card (Σ y : {y : β // y ≠ x}, PairingMap (PairRemainder x y.val)) :=
              (Fintype.card_congr (addPairEquiv x)).symm
            _ = ∑ y : {y : β // y ≠ x}, Fintype.card (PairingMap (PairRemainder x y.val)) :=
              Fintype.card_sigma
            _ = ∑ _y : {y : β // y ≠ x}, pairingNumber m := by
              apply Finset.sum_congr rfl
              intro y _
              apply ih m (by omega) (PairRemainder x y.val)
              rw [card_pairRemainder x y.val y.property, hm]
              omega
            _ = pairingNumber (m + 1 + 1) := by
              simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
                card_other_elements, hm]
              simp [pairingNumber]
  exact h (Fintype.card α) α rfl

theorem pairingNumber_eq_doubleFactorial (n : ℕ) :
    pairingNumber n = if Even n then (n - 1).doubleFactorial else 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pairingNumber, Nat.doubleFactorial]
  | one => norm_num [pairingNumber]
  | more n ih _ =>
    have he : Even (n + 2) ↔ Even n := by simp [Nat.even_add]
    simp only [pairingNumber, he, ih]
    by_cases hn : Even n
    · simp only [hn, ite_true]
      have hn1 : n + 2 - 1 = n + 1 := by omega
      rw [hn1, Nat.doubleFactorial_add_one]
    · simp [hn]

theorem pairingMap_card_eq_doubleFactorial (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (PairingMap α) =
      if Even (Fintype.card α) then (Fintype.card α - 1).doubleFactorial else 0 := by
  rw [pairingMap_card, pairingNumber_eq_doubleFactorial]

noncomputable def partitionClass {α : Type*} [Fintype α] (P : Setoid α) (x : α) : Finset α :=
  Finset.univ.filter (fun z => P x z)

theorem partitionClass_card {α : Type*} [Fintype α] [DecidableEq α]
    (P : Setoid α) (x : α) :
    (partitionClass P x).card = Fintype.card (PartitionBlock P (Quotient.mk P x)) := by
  let e : partitionClass P x ≃ PartitionBlock P (Quotient.mk P x) :=
    Equiv.subtypeEquivRight (fun z : α => by
      simp only [partitionClass, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => Quotient.sound (P.symm h), fun h => P.symm (Quotient.exact h)⟩)
  exact (Fintype.card_coe _).symm.trans (Fintype.card_congr e)

theorem isPairingPartition_iff_class_card {α : Type*} [Fintype α] [DecidableEq α]
    (P : Setoid α) : IsPairingPartition P ↔ ∀ x, (partitionClass P x).card = 2 := by
  constructor
  · intro h x
    rw [partitionClass_card]
    exact h _
  · intro h v
    refine Quotient.inductionOn v ?_
    intro x
    rw [← partitionClass_card]
    exact h x

private theorem pairing_partner_exists {α : Type*} [Fintype α] [DecidableEq α]
    (P : Setoid α) (hP : IsPairingPartition P) (x : α) :
    ∃ y, (partitionClass P x).erase x = {y} := by
  apply Finset.card_eq_one.mp
  rw [Finset.card_erase_of_mem (by simp [partitionClass]),
    (isPairingPartition_iff_class_card P).mp hP x]

noncomputable def pairingPartner {α : Type*} [Fintype α] [DecidableEq α]
    (P : Setoid α) (hP : IsPairingPartition P) (x : α) : α :=
  Classical.choose (pairing_partner_exists P hP x)

theorem pairingPartner_erase {α : Type*} [Fintype α] [DecidableEq α]
    (P : Setoid α) (hP : IsPairingPartition P) (x : α) :
    (partitionClass P x).erase x = {pairingPartner P hP x} :=
  Classical.choose_spec (pairing_partner_exists P hP x)

theorem pairingPartner_spec {α : Type*} [Fintype α] [DecidableEq α]
    (P : Setoid α) (hP : IsPairingPartition P) (x : α) :
    P x (pairingPartner P hP x) ∧ pairingPartner P hP x ≠ x ∧
      ∀ z, P x z → z = x ∨ z = pairingPartner P hP x := by
  have hy : pairingPartner P hP x ∈ (partitionClass P x).erase x := by
    rw [pairingPartner_erase P hP x]
    simp
  refine ⟨?_, (Finset.mem_erase.mp hy).1, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.mem_erase.mp hy).2).2
  · intro z hz
    by_cases hx : z = x
    · exact Or.inl hx
    · right
      have hh : z ∈ (partitionClass P x).erase x :=
        Finset.mem_erase.mpr ⟨hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
      rw [pairingPartner_erase P hP x] at hh
      exact Finset.mem_singleton.mp hh

theorem pairingPartner_involutive {α : Type*} [Fintype α] [DecidableEq α]
    (P : Setoid α) (hP : IsPairingPartition P) : Function.Involutive (pairingPartner P hP) := by
  intro x
  have hx := pairingPartner_spec P hP x
  have hy := (pairingPartner_spec P hP (pairingPartner P hP x)).2.2 x (P.symm hx.1)
  rcases hy with h | h
  · exact (hx.2.1 h.symm).elim
  · exact h.symm

noncomputable def pairingSetoid {α : Type*} (f : PairingMap α) : Setoid α where
  r x y := x = y ∨ f.val x = y
  iseqv := {
    refl x := Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        simpa only [f.property.1 x] using (congrArg f.val h).symm
    trans := by
      intro x y z hxy hyz
      rcases hxy with hxy | hxy
      · simpa only [hxy] using hyz
      · rcases hyz with hyz | hyz
        · exact Or.inr (hxy.trans hyz)
        · left
          have hh := congrArg f.val hxy
          rw [f.property.1 x] at hh
          exact hh.trans hyz }

theorem pairingSetoid_isPairing {α : Type*} [Fintype α] [DecidableEq α]
    (f : PairingMap α) : IsPairingPartition (pairingSetoid f) := by
  apply (isPairingPartition_iff_class_card _).mpr
  intro x
  have he : partitionClass (pairingSetoid f) x = {x, f.val x} := by
    ext z
    simp only [partitionClass, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    change (x = z ∨ f.val x = z) ↔ z = x ∨ z = f.val x
    simp [eq_comm]
  rw [he]
  simp [(f.property.2 x).symm]

noncomputable def pairingPartitionEquivMap {α : Type*} [Fintype α] [DecidableEq α] :
    {P : Setoid α // IsPairingPartition P} ≃ PairingMap α where
  toFun P := ⟨pairingPartner P.val P.property, pairingPartner_involutive _ _,
    fun x => (pairingPartner_spec _ _ x).2.1⟩
  invFun f := ⟨pairingSetoid f, pairingSetoid_isPairing f⟩
  left_inv P := by
    apply Subtype.ext
    apply Setoid.ext
    intro x y
    change (x = y ∨ pairingPartner P.val P.property x = y) ↔ P.val x y
    constructor
    · rintro (h | h)
      · subst y; exact P.val.refl x
      · rw [← h]; exact (pairingPartner_spec _ _ x).1
    · intro h
      rcases (pairingPartner_spec _ _ x).2.2 y h with hy | hy
      · exact Or.inl hy.symm
      · exact Or.inr hy.symm
  right_inv f := by
    apply Subtype.ext
    funext x
    have h := pairingPartner_spec (pairingSetoid f) (pairingSetoid_isPairing f) x
    rcases h.1 with hxy | hxy
    · exact (h.2.1 hxy.symm).elim
    · exact hxy.symm

/-- Exact number of actual Setoid partitions into two-element blocks. -/
theorem pairingPartition_card {α : Type*} [Fintype α] [DecidableEq α] :
    Fintype.card {P : Setoid α // IsPairingPartition P} =
      if Even (Fintype.card α) then (Fintype.card α - 1).doubleFactorial else 0 := by
  rw [Fintype.card_congr pairingPartitionEquivMap, pairingMap_card_eq_doubleFactorial]

/-- Relabeling an involution preserves both pairing conditions. -/
noncomputable def pairingMapCongr {α β : Type*} (e : α ≃ β) : PairingMap α ≃ PairingMap β where
  toFun f := ⟨fun y => e (f.val (e.symm y)),
    fun y => by simp only [Equiv.symm_apply_apply]; rw [f.property.1 (e.symm y), Equiv.apply_symm_apply],
    fun y h => f.property.2 (e.symm y) (by
      simpa only [Equiv.symm_apply_apply] using congrArg e.symm h)⟩
  invFun f := ⟨fun x => e.symm (f.val (e x)),
    fun x => by simp only [Equiv.apply_symm_apply]; rw [f.property.1 (e x), Equiv.symm_apply_apply],
    fun x h => f.property.2 (e x) (by
      simpa only [Equiv.apply_symm_apply] using congrArg e h)⟩
  left_inv f := by apply Subtype.ext; funext x; simp
  right_inv f := by apply Subtype.ext; funext y; simp

noncomputable def sigmaPairingMap {ι : Type*} {α : ι → Type*}
    (F : ∀ a, PairingMap (α a)) : PairingMap (Σ a, α a) :=
  ⟨fun x => ⟨x.1, (F x.1).val x.2⟩,
    (by
      rintro ⟨a, x⟩
      change (⟨a, (F a).val ((F a).val x)⟩ : Σ a, α a) = ⟨a, x⟩
      rw [(F a).property.1 x]),
    fun ⟨a, x⟩ h => (F a).property.2 x (eq_of_heq (Sigma.mk.inj h).2)⟩

noncomputable def assembleFiberPairing {κ ι : Type*} (r : κ → ι)
    (F : ∀ a : ι, PairingMap {x : κ // r x = a}) :
    {f : PairingMap κ // ∀ x, r (f.val x) = r x} := by
  let f := pairingMapCongr (Equiv.sigmaFiberEquiv r) (sigmaPairingMap F)
  refine ⟨f, ?_⟩
  intro x
  exact ((F (r x)).val ⟨x, rfl⟩).property

theorem assembleFiberPairing_apply {κ ι : Type*} (r : κ → ι)
    (F : ∀ a : ι, PairingMap {x : κ // r x = a})
    (a : ι) (x : {x : κ // r x = a}) :
    (assembleFiberPairing r F).val.val x.val = ((F a).val x).val := by
  rcases x with ⟨x, hx⟩
  cases hx
  rfl

noncomputable def restrictFiberPairing {κ ι : Type*} (r : κ → ι)
    (f : {f : PairingMap κ // ∀ x, r (f.val x) = r x})
    (a : ι) : PairingMap {x : κ // r x = a} :=
  ⟨fun x => ⟨f.val.val x.val, (f.property x.val).trans x.property⟩,
    fun x => Subtype.ext (f.val.property.1 x.val),
    fun x h => f.val.property.2 x.val (congrArg Subtype.val h)⟩

/-- A compatible pairing is independently a pairing of every fiber. Empty
fibers contribute the unique empty pairing. -/
noncomputable def pairingMapsFiberEquiv {κ ι : Type*} (r : κ → ι) :
    (∀ a : ι, PairingMap {x : κ // r x = a}) ≃
      {f : PairingMap κ // ∀ x, r (f.val x) = r x} :=
  Equiv.ofBijective (assembleFiberPairing r) (by
    constructor
    · intro F G h
      funext a
      apply Subtype.ext
      funext x
      apply Subtype.ext
      simpa only [assembleFiberPairing_apply] using
        congrArg (fun f : {f : PairingMap κ // ∀ x, r (f.val x) = r x} => f.val.val x.val) h
    · intro f
      refine ⟨restrictFiberPairing r f, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      funext x
      rfl)

noncomputable def compatiblePairingPartitionEquivMap {κ ι : Type*}
    [Fintype κ] [DecidableEq κ] (r : κ → ι) :
    {P : Setoid κ // IsPairingPartition P ∧ P ≤ Setoid.ker r} ≃
      {f : PairingMap κ // ∀ x, r (f.val x) = r x} where
  toFun P := ⟨pairingPartitionEquivMap ⟨P.val, P.property.1⟩, fun x =>
    (P.property.2 (pairingPartner_spec P.val P.property.1 x).1).symm⟩
  invFun f := ⟨pairingSetoid f.val, pairingSetoid_isPairing f.val, by
    intro x y h
    change x = y ∨ f.val.val x = y at h
    rcases h with h | h
    · exact congrArg r h
    · exact (f.property x).symm.trans (congrArg r h)⟩
  left_inv P := by
    apply Subtype.ext
    exact congrArg (fun Q : {Q : Setoid κ // IsPairingPartition Q} => Q.val)
      (pairingPartitionEquivMap.left_inv ⟨P.val, P.property.1⟩)
  right_inv f := by
    apply Subtype.ext
    exact pairingPartitionEquivMap.apply_symm_apply f.val

/-- The complete Wick compatibility count, factored over all coordinate fibers. -/
theorem compatible_pairingPartition_card {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (r : κ → ι) :
    Fintype.card {P : Setoid κ // IsPairingPartition P ∧ P ≤ Setoid.ker r} =
      ∏ a : ι, if Even (Fintype.card {x : κ // r x = a}) then
        (Fintype.card {x : κ // r x = a} - 1).doubleFactorial else 0 := by
  rw [Fintype.card_congr (compatiblePairingPartitionEquivMap r),
    Fintype.card_congr (pairingMapsFiberEquiv r).symm, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro a _
  exact pairingMap_card_eq_doubleFactorial _

/-- The same compatibility count in the tuple-multiplicity Finset convention. -/
theorem compatible_pairingPartition_count {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (r : κ → ι) :
    (Finset.univ.filter (fun P : Setoid κ => IsPairingPartition P ∧ P ≤ Setoid.ker r)).card =
      ∏ a : ι, if Even ((Finset.univ.filter (fun x : κ => r x = a)).card) then
        ((Finset.univ.filter (fun x : κ => r x = a)).card - 1).doubleFactorial else 0 := by
  simpa only [Fintype.card_subtype] using compatible_pairingPartition_card r

end TournamentHamiltonian
