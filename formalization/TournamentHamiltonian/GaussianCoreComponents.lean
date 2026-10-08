import TournamentHamiltonian.GaussianCoreGraph

/-! Canonical extraction of the actual degree-two components of a pair of partitions. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The join of the row and column relations is exactly connectedness on edge labels. -/
def IsPureDegreeTwoComponent (P Q : Setoid κ) (e : κ) : Prop :=
  ∀ f, (P ⊔ Q) f e →
    coordinatePartitionDegree P (Quotient.mk P f) = 2 ∧
      coordinatePartitionDegree Q (Quotient.mk Q f) = 2

omit [DecidableEq κ] in
theorem isPureDegreeTwoComponent_congr (P Q : Setoid κ) {e f : κ}
    (hef : (P ⊔ Q) e f) : IsPureDegreeTwoComponent P Q e ↔ IsPureDegreeTwoComponent P Q f := by
  constructor
  · intro h g hg
    exact h g ((P ⊔ Q).trans hg ((P ⊔ Q).symm hef))
  · intro h g hg
    exact h g ((P ⊔ Q).trans hg hef)

omit [DecidableEq κ] in
theorem isPureDegreeTwoComponent_row_invariant (P Q : Setoid κ) {e f : κ}
    (hef : P e f) : IsPureDegreeTwoComponent P Q e ↔ IsPureDegreeTwoComponent P Q f :=
  isPureDegreeTwoComponent_congr P Q ((le_sup_left : P ≤ P ⊔ Q) hef)

omit [DecidableEq κ] in
theorem isPureDegreeTwoComponent_column_invariant (P Q : Setoid κ) {e f : κ}
    (hef : Q e f) : IsPureDegreeTwoComponent P Q e ↔ IsPureDegreeTwoComponent P Q f :=
  isPureDegreeTwoComponent_congr P Q ((le_sup_right : Q ≤ P ⊔ Q) hef)

/-- Restricting to a union of actual partition blocks preserves every retained block cardinality. -/
noncomputable def restrictedPartitionBlockEquiv (P : Setoid κ) (s : κ → Prop) [DecidablePred s]
    (hs : ∀ e f, P e f → (s e ↔ s f)) (x : {e // s e}) :
    PartitionBlock (Setoid.comap Subtype.val P) (Quotient.mk _ x) ≃
      PartitionBlock P (Quotient.mk P x.val) where
  toFun y := ⟨y.val.val, by
    have hy := Quotient.exact y.property
    exact Quotient.sound hy⟩
  invFun y := by
    have hy := Quotient.exact y.property
    exact ⟨⟨y.val, (hs y.val x.val hy).mpr x.property⟩, Quotient.sound hy⟩
  left_inv y := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

omit [DecidableEq κ] in
theorem restrictedPartitionDegree_eq (P : Setoid κ) (s : κ → Prop) [DecidablePred s]
    (hs : ∀ e f, P e f → (s e ↔ s f)) (x : {e // s e}) :
    coordinatePartitionDegree (Setoid.comap Subtype.val P) (Quotient.mk _ x) =
      coordinatePartitionDegree P (Quotient.mk P x.val) := by
  rw [← partitionBlock_card_eq_degree, ← partitionBlock_card_eq_degree]
  exact Fintype.card_congr (restrictedPartitionBlockEquiv P s hs x)

abbrev PureComponentEdges (P Q : Setoid κ) := {e // IsPureDegreeTwoComponent P Q e}
abbrev CoreComponentEdges (P Q : Setoid κ) := {e // ¬ IsPureDegreeTwoComponent P Q e}

noncomputable def pureRowPartition (P Q : Setoid κ) : Setoid (PureComponentEdges P Q) :=
  Setoid.comap Subtype.val P
noncomputable def pureColumnPartition (P Q : Setoid κ) : Setoid (PureComponentEdges P Q) :=
  Setoid.comap Subtype.val Q
noncomputable def coreRowPartition (P Q : Setoid κ) : Setoid (CoreComponentEdges P Q) :=
  Setoid.comap Subtype.val P
noncomputable def coreColumnPartition (P Q : Setoid κ) : Setoid (CoreComponentEdges P Q) :=
  Setoid.comap Subtype.val Q

omit [DecidableEq κ] in
theorem pureRowPartition_isPairing (P Q : Setoid κ) : IsPairingPartition (pureRowPartition P Q) := by
  intro v
  induction v using Quotient.inductionOn with
  | h e =>
    rw [partitionBlock_card_eq_degree]
    change coordinatePartitionDegree (Setoid.comap Subtype.val P) (Quotient.mk _ e) = 2
    rw [restrictedPartitionDegree_eq P _ (fun _ _ h => isPureDegreeTwoComponent_row_invariant P Q h)]
    exact (e.property e.val ((P ⊔ Q).refl _)).1

omit [DecidableEq κ] in
theorem pureColumnPartition_isPairing (P Q : Setoid κ) : IsPairingPartition (pureColumnPartition P Q) := by
  intro v
  induction v using Quotient.inductionOn with
  | h e =>
    rw [partitionBlock_card_eq_degree]
    change coordinatePartitionDegree (Setoid.comap Subtype.val Q) (Quotient.mk _ e) = 2
    rw [restrictedPartitionDegree_eq Q _ (fun _ _ h => isPureDegreeTwoComponent_column_invariant P Q h)]
    exact (e.property e.val ((P ⊔ Q).refl _)).2

omit [DecidableEq κ] in
theorem coreRowPartition_no_singleton (P Q : Setoid κ) (hP : ¬ HasSingletonClass P) :
    ¬ HasSingletonClass (coreRowPartition P Q) := by
  rintro ⟨e, he⟩
  apply hP
  refine ⟨e.val, fun i hi => ?_⟩
  have hci : ¬ IsPureDegreeTwoComponent P Q i :=
    (isPureDegreeTwoComponent_row_invariant P Q hi).not.mpr e.property
  exact congrArg Subtype.val (he ⟨i, hci⟩ hi)

omit [DecidableEq κ] in
theorem coreColumnPartition_no_singleton (P Q : Setoid κ) (hQ : ¬ HasSingletonClass Q) :
    ¬ HasSingletonClass (coreColumnPartition P Q) := by
  rintro ⟨e, he⟩
  apply hQ
  refine ⟨e.val, fun i hi => ?_⟩
  have hci : ¬ IsPureDegreeTwoComponent P Q i :=
    (isPureDegreeTwoComponent_column_invariant P Q hi).not.mpr e.property
  exact congrArg Subtype.val (he ⟨i, hci⟩ hi)

omit [DecidableEq κ] in
/-- Every retained core component really contains a vertex of degree different from two. -/
theorem corePartitions_not_pairings (P Q : Setoid κ) (e : CoreComponentEdges P Q) :
    ¬ (IsPairingPartition (coreRowPartition P Q) ∧
      IsPairingPartition (coreColumnPartition P Q)) := by
  rintro ⟨hp, hq⟩
  apply e.property
  intro f hf
  have hcf : ¬ IsPureDegreeTwoComponent P Q f :=
    (isPureDegreeTwoComponent_congr P Q hf).not.mpr e.property
  let x : CoreComponentEdges P Q := ⟨f, hcf⟩
  have hpd := hp (Quotient.mk (coreRowPartition P Q) x)
  have hqd := hq (Quotient.mk (coreColumnPartition P Q) x)
  rw [partitionBlock_card_eq_degree] at hpd hqd
  change coordinatePartitionDegree (Setoid.comap Subtype.val P) (Quotient.mk _ x) = 2 at hpd
  change coordinatePartitionDegree (Setoid.comap Subtype.val Q) (Quotient.mk _ x) = 2 at hqd
  have hep := restrictedPartitionDegree_eq P (fun t => ¬ IsPureDegreeTwoComponent P Q t)
    (fun _ _ h => (isPureDegreeTwoComponent_row_invariant P Q h).not) x
  have heq := restrictedPartitionDegree_eq Q (fun t => ¬ IsPureDegreeTwoComponent P Q t)
    (fun _ _ h => (isPureDegreeTwoComponent_column_invariant P Q h).not) x
  exact ⟨hep.symm.trans hpd, heq.symm.trans hqd⟩

/-- The canonical nonempty core has strictly fewer vertices than edges, including disconnected cores. -/
theorem coreComponent_positive_excess (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) (e : CoreComponentEdges P Q) :
    Fintype.card (Quotient (coreRowPartition P Q)) +
      Fintype.card (Quotient (coreColumnPartition P Q)) < Fintype.card (CoreComponentEdges P Q) := by
  exact nonPairing_graph_positive_excess _ _ (coreRowPartition_no_singleton P Q hP)
    (coreColumnPartition_no_singleton P Q hQ) (corePartitions_not_pairings P Q e)

omit [DecidableEq κ] in
theorem coreComponent_excess_lt_degree (P Q : Setoid κ) (e : CoreComponentEdges P Q) :
    Fintype.card (CoreComponentEdges P Q) -
      (Fintype.card (Quotient (coreRowPartition P Q)) +
        Fintype.card (Quotient (coreColumnPartition P Q))) < Fintype.card κ := by
  have hs : Fintype.card (CoreComponentEdges P Q) ≤ Fintype.card κ :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have : Nonempty (Quotient (coreRowPartition P Q)) := ⟨Quotient.mk _ e⟩
  have hp : 0 < Fintype.card (Quotient (coreRowPartition P Q)) := Fintype.card_pos
  have : Nonempty (CoreComponentEdges P Q) := ⟨e⟩
  have hc : 0 < Fintype.card (CoreComponentEdges P Q) := Fintype.card_pos
  omega

end TournamentHamiltonian
