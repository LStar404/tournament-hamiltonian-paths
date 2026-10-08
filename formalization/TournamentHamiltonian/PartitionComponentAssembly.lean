import TournamentHamiltonian.PartitionComponentSplit

/-! Genuine partition assembly on complementary edge subsets. -/

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {α β κ : Type*}

def sumPartition (P : Setoid α) (Q : Setoid β) : Setoid (α ⊕ β) where
  r := fun x y => match x, y with
    | .inl a, .inl b => P a b
    | .inr a, .inr b => Q a b
    | _, _ => False
  iseqv := {
    refl := by intro x; cases x <;> first | exact P.refl _ | exact Q.refl _
    symm := by intro x y h; cases x <;> cases y <;>
      first | exact P.symm h | exact Q.symm h | exact False.elim h
    trans := by intro x y z hxy hyz; cases x <;> cases y <;> cases z <;>
      first | exact P.trans hxy hyz | exact Q.trans hxy hyz |
        exact False.elim hxy | exact False.elim hyz }

noncomputable def assembleSubsetPartition (s : κ → Prop) [DecidablePred s]
    (P : Setoid {e // s e}) (Q : Setoid {e // ¬s e}) : Setoid κ :=
  Setoid.comap (Equiv.sumCompl s).symm (sumPartition P Q)

theorem assembleSubsetPartition_pos (s : κ → Prop) [DecidablePred s]
    (P : Setoid {e // s e}) (Q : Setoid {e // ¬s e}) (e f : {e // s e}) :
    assembleSubsetPartition s P Q e.val f.val ↔ P e f := by
  change sumPartition P Q ((Equiv.sumCompl s).symm e.val) ((Equiv.sumCompl s).symm f.val) ↔ P e f
  rw [Equiv.sumCompl_symm_apply_pos, Equiv.sumCompl_symm_apply_pos]
  rfl

theorem assembleSubsetPartition_neg (s : κ → Prop) [DecidablePred s]
    (P : Setoid {e // s e}) (Q : Setoid {e // ¬s e}) (e f : {e // ¬s e}) :
    assembleSubsetPartition s P Q e.val f.val ↔ Q e f := by
  change sumPartition P Q ((Equiv.sumCompl s).symm e.val) ((Equiv.sumCompl s).symm f.val) ↔ Q e f
  rw [Equiv.sumCompl_symm_apply_neg, Equiv.sumCompl_symm_apply_neg]
  rfl

theorem assembleSubsetPartition_mixed (s : κ → Prop) [DecidablePred s]
    (P : Setoid {e // s e}) (Q : Setoid {e // ¬s e}) (e : {e // s e}) (f : {e // ¬s e}) :
    ¬ assembleSubsetPartition s P Q e.val f.val := by
  change ¬ sumPartition P Q ((Equiv.sumCompl s).symm e.val) ((Equiv.sumCompl s).symm f.val)
  rw [Equiv.sumCompl_symm_apply_pos, Equiv.sumCompl_symm_apply_neg]
  exact id

theorem assembleSubsetPartition_invariant (s : κ → Prop) [DecidablePred s]
    (P : Setoid {e // s e}) (Q : Setoid {e // ¬s e}) :
    ∀ e f, assembleSubsetPartition s P Q e f → (s e ↔ s f) := by
  intro e f h
  by_cases he : s e <;> by_cases hf : s f
  · exact iff_of_true he hf
  · exact False.elim (assembleSubsetPartition_mixed s P Q ⟨e, he⟩ ⟨f, hf⟩ h)
  · exact False.elim (assembleSubsetPartition_mixed s P Q ⟨f, hf⟩ ⟨e, he⟩
      ((assembleSubsetPartition s P Q).symm h))
  · exact iff_of_false he hf

theorem assembleSubsetPartition_comap_pos (s : κ → Prop) [DecidablePred s]
    (P : Setoid {e // s e}) (Q : Setoid {e // ¬s e}) :
    Setoid.comap (Subtype.val : {e // s e} → κ) (assembleSubsetPartition s P Q) = P := by
  apply Setoid.ext
  exact assembleSubsetPartition_pos s P Q

theorem assembleSubsetPartition_comap_neg (s : κ → Prop) [DecidablePred s]
    (P : Setoid {e // s e}) (Q : Setoid {e // ¬s e}) :
    Setoid.comap (Subtype.val : {e // ¬s e} → κ) (assembleSubsetPartition s P Q) = Q := by
  apply Setoid.ext
  exact assembleSubsetPartition_neg s P Q

theorem assembleSubsetPartition_of_invariant (P : Setoid κ) (s : κ → Prop) [DecidablePred s]
    (hs : ∀ e f, P e f → (s e ↔ s f)) :
    assembleSubsetPartition s (Setoid.comap (Subtype.val : {e // s e} → κ) P)
      (Setoid.comap (Subtype.val : {e // ¬s e} → κ) P) = P := by
  apply Setoid.ext
  intro e f
  by_cases he : s e <;> by_cases hf : s f
  · exact assembleSubsetPartition_pos s _ _ ⟨e, he⟩ ⟨f, hf⟩
  · constructor
    · intro h
      exact False.elim (assembleSubsetPartition_mixed s _ _ ⟨e, he⟩ ⟨f, hf⟩ h)
    · intro h
      exact False.elim (hf ((hs e f h).mp he))
  · constructor
    · intro h
      exact False.elim (assembleSubsetPartition_mixed s _ _ ⟨f, hf⟩ ⟨e, he⟩
        ((assembleSubsetPartition s _ _).symm h))
    · intro h
      exact False.elim (he ((hs e f h).mpr hf))
  · exact assembleSubsetPartition_neg s _ _ ⟨e, he⟩ ⟨f, hf⟩

theorem assembleSubsetPartition_mono (s : κ → Prop) [DecidablePred s]
    {P R : Setoid {e // s e}} {Q S : Setoid {e // ¬s e}}
    (hP : P ≤ R) (hQ : Q ≤ S) : assembleSubsetPartition s P Q ≤ assembleSubsetPartition s R S := by
  intro e f h
  have hi := assembleSubsetPartition_invariant s P Q e f h
  by_cases he : s e
  · have hf := hi.mp he
    exact (assembleSubsetPartition_pos s R S ⟨e, he⟩ ⟨f, hf⟩).mpr
      (hP ((assembleSubsetPartition_pos s P Q ⟨e, he⟩ ⟨f, hf⟩).mp h))
  · have hf := hi.not.mp he
    exact (assembleSubsetPartition_neg s R S ⟨e, he⟩ ⟨f, hf⟩).mpr
      (hQ ((assembleSubsetPartition_neg s P Q ⟨e, he⟩ ⟨f, hf⟩).mp h))

/-- Connectedness does not cross the subset boundary, and joins restrict to the actual component joins. -/
theorem assembleSubsetPartition_sup (s : κ → Prop) [DecidablePred s]
    (P R : Setoid {e // s e}) (Q S : Setoid {e // ¬s e}) :
    assembleSubsetPartition s (P ⊔ R) (Q ⊔ S) =
      assembleSubsetPartition s P Q ⊔ assembleSubsetPartition s R S := by
  apply le_antisymm
  · let T := assembleSubsetPartition s P Q ⊔ assembleSubsetPartition s R S
    have hp : P ≤ Setoid.comap Subtype.val T := by
      intro e f h
      exact (le_sup_left : assembleSubsetPartition s P Q ≤ T)
        ((assembleSubsetPartition_pos s P Q e f).mpr h)
    have hr : R ≤ Setoid.comap Subtype.val T := by
      intro e f h
      exact (le_sup_right : assembleSubsetPartition s R S ≤ T)
        ((assembleSubsetPartition_pos s R S e f).mpr h)
    have hq : Q ≤ Setoid.comap Subtype.val T := by
      intro e f h
      exact (le_sup_left : assembleSubsetPartition s P Q ≤ T)
        ((assembleSubsetPartition_neg s P Q e f).mpr h)
    have ht : S ≤ Setoid.comap Subtype.val T := by
      intro e f h
      exact (le_sup_right : assembleSubsetPartition s R S ≤ T)
        ((assembleSubsetPartition_neg s R S e f).mpr h)
    intro e f h
    have hi := assembleSubsetPartition_invariant s (P ⊔ R) (Q ⊔ S) e f h
    by_cases he : s e
    · have hf := hi.mp he
      exact (sup_le hp hr) ((assembleSubsetPartition_pos s _ _ ⟨e, he⟩ ⟨f, hf⟩).mp h)
    · have hf := hi.not.mp he
      exact (sup_le hq ht) ((assembleSubsetPartition_neg s _ _ ⟨e, he⟩ ⟨f, hf⟩).mp h)
  · exact sup_le (assembleSubsetPartition_mono s le_sup_left le_sup_left)
      (assembleSubsetPartition_mono s le_sup_right le_sup_right)

variable [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem assembleSubsetPartition_degree_pos (s : κ → Prop) [DecidablePred s]
    (P : Setoid {e // s e}) (Q : Setoid {e // ¬s e}) (e : {e // s e}) :
    coordinatePartitionDegree (assembleSubsetPartition s P Q) (Quotient.mk _ e.val) =
      coordinatePartitionDegree P (Quotient.mk P e) := by
  have h := restrictedPartitionDegree_eq (assembleSubsetPartition s P Q) s
    (assembleSubsetPartition_invariant s P Q) e
  rw [assembleSubsetPartition_comap_pos] at h
  exact h.symm

omit [DecidableEq κ] in
theorem assembleSubsetPartition_degree_neg (s : κ → Prop) [DecidablePred s]
    (P : Setoid {e // s e}) (Q : Setoid {e // ¬s e}) (e : {e // ¬s e}) :
    coordinatePartitionDegree (assembleSubsetPartition s P Q) (Quotient.mk _ e.val) =
      coordinatePartitionDegree Q (Quotient.mk Q e) := by
  have h := restrictedPartitionDegree_eq (assembleSubsetPartition s P Q) (fun e => ¬s e)
    (fun _ _ h => (assembleSubsetPartition_invariant s P Q _ _ h).not) e
  rw [assembleSubsetPartition_comap_neg] at h
  exact h.symm

omit [DecidableEq κ] in
theorem assembleSubsetPair_pure_pos (s : κ → Prop) [DecidablePred s]
    (P R : Setoid {e // s e}) (Q S : Setoid {e // ¬s e}) (e : {e // s e}) :
    IsPureDegreeTwoComponent (assembleSubsetPartition s P Q) (assembleSubsetPartition s R S) e.val ↔
      IsPureDegreeTwoComponent P R e := by
  constructor
  · intro h f hf
    have hfull : (assembleSubsetPartition s P Q ⊔ assembleSubsetPartition s R S) f.val e.val := by
      rw [← assembleSubsetPartition_sup]
      exact (assembleSubsetPartition_pos s _ _ f e).mpr hf
    have hd := h f.val hfull
    rw [assembleSubsetPartition_degree_pos s P Q f, assembleSubsetPartition_degree_pos s R S f] at hd
    exact hd
  · intro h f hf
    rw [← assembleSubsetPartition_sup] at hf
    have hsf := (assembleSubsetPartition_invariant s (P ⊔ R) (Q ⊔ S) f e.val hf).mpr e.property
    let x : {e // s e} := ⟨f, hsf⟩
    have hd := h x ((assembleSubsetPartition_pos s _ _ x e).mp hf)
    rw [assembleSubsetPartition_degree_pos s P Q x, assembleSubsetPartition_degree_pos s R S x]
    exact hd

omit [DecidableEq κ] in
theorem assembleSubsetPair_pure_neg (s : κ → Prop) [DecidablePred s]
    (P R : Setoid {e // s e}) (Q S : Setoid {e // ¬s e}) (e : {e // ¬s e}) :
    IsPureDegreeTwoComponent (assembleSubsetPartition s P Q) (assembleSubsetPartition s R S) e.val ↔
      IsPureDegreeTwoComponent Q S e := by
  constructor
  · intro h f hf
    have hfull : (assembleSubsetPartition s P Q ⊔ assembleSubsetPartition s R S) f.val e.val := by
      rw [← assembleSubsetPartition_sup]
      exact (assembleSubsetPartition_neg s _ _ f e).mpr hf
    have hd := h f.val hfull
    rw [assembleSubsetPartition_degree_neg s P Q f, assembleSubsetPartition_degree_neg s R S f] at hd
    exact hd
  · intro h f hf
    rw [← assembleSubsetPartition_sup] at hf
    have hsf := (assembleSubsetPartition_invariant s (P ⊔ R) (Q ⊔ S) f e.val hf).not.mpr e.property
    let x : {e // ¬s e} := ⟨f, hsf⟩
    have hd := h x ((assembleSubsetPartition_neg s _ _ x e).mp hf)
    rw [assembleSubsetPartition_degree_neg s P Q x, assembleSubsetPartition_degree_neg s R S x]
    exact hd

omit [DecidableEq κ] in
/-- Every component of two pairing partitions is a pure degree-two component, including the empty type. -/
theorem pairingPartitionPair_all_pure (P Q : Setoid κ)
    (hP : IsPairingPartition P) (hQ : IsPairingPartition Q) (e : κ) :
    IsPureDegreeTwoComponent P Q e := by
  intro f _
  have hp := hP (Quotient.mk P f)
  have hq := hQ (Quotient.mk Q f)
  rw [partitionBlock_card_eq_degree] at hp hq
  exact ⟨hp, hq⟩

omit [DecidableEq κ] in
/-- Assembly of Wick partitions and a core without pure components recovers exactly the chosen split. -/
theorem assembleSubsetPair_pure_iff (s : κ → Prop) [DecidablePred s]
    (P R : Setoid {e // s e}) (Q S : Setoid {e // ¬s e})
    (hP : IsPairingPartition P) (hR : IsPairingPartition R)
    (hcore : ∀ e, ¬ IsPureDegreeTwoComponent Q S e) (e : κ) :
    IsPureDegreeTwoComponent (assembleSubsetPartition s P Q) (assembleSubsetPartition s R S) e ↔ s e := by
  by_cases he : s e
  · exact iff_of_true ((assembleSubsetPair_pure_pos s P R Q S ⟨e, he⟩).mpr
      (pairingPartitionPair_all_pure P R hP hR ⟨e, he⟩)) he
  · exact iff_of_false (fun h => hcore ⟨e, he⟩
      ((assembleSubsetPair_pure_neg s P R Q S ⟨e, he⟩).mp h)) he

omit [DecidableEq κ] in
theorem coreComponent_row_reassembly (P Q : Setoid κ) :
    assembleSubsetPartition (IsPureDegreeTwoComponent P Q)
      (pureRowPartition P Q) (coreRowPartition P Q) = P :=
  assembleSubsetPartition_of_invariant P _
    (fun _ _ h => isPureDegreeTwoComponent_row_invariant P Q h)

omit [DecidableEq κ] in
theorem coreComponent_column_reassembly (P Q : Setoid κ) :
    assembleSubsetPartition (IsPureDegreeTwoComponent P Q)
      (pureColumnPartition P Q) (coreColumnPartition P Q) = Q :=
  assembleSubsetPartition_of_invariant Q _
    (fun _ _ h => isPureDegreeTwoComponent_column_invariant P Q h)

omit [DecidableEq κ] in
/-- The canonical extracted core has no pure component at all, a stronger statement than nonpairing. -/
theorem coreComponent_no_pure_component (P Q : Setoid κ) (e : CoreComponentEdges P Q) :
    ¬ IsPureDegreeTwoComponent (coreRowPartition P Q) (coreColumnPartition P Q) e := by
  intro he
  have h := assembleSubsetPair_pure_neg (IsPureDegreeTwoComponent P Q)
    (pureRowPartition P Q) (pureColumnPartition P Q) (coreRowPartition P Q) (coreColumnPartition P Q) e
  rw [coreComponent_row_reassembly P Q, coreComponent_column_reassembly P Q] at h
  exact e.property (h.mpr he)

end TournamentHamiltonian
