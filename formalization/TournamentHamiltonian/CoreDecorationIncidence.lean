import TournamentHamiltonian.CoreDecorationVertices

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ]

theorem decoratedHalfEdgeEquiv_vertex (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) (x : DecoratedCoreHalfEdges P Q d) :
    partitionHalfEdgeVertex P Q (decoratedHalfEdgeEquiv P Q d hP hQ x).val = (d.1 x.1).val :=
  (d.2 (d.1 x.1) x.2).property

theorem decoratedHalfEdgeEquiv_pair (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) (x : DecoratedCoreHalfEdges P Q d) :
    decoratedHalfEdgeEquiv P Q d hP hQ ((decoratedCompressedPairing P Q d hP hQ).val x) =
      (partitionCoreTerminalPairing P Q).val (decoratedHalfEdgeEquiv P Q d hP hQ x) :=
  Equiv.apply_symm_apply _ _

theorem decoratedPathArrival_first_departure (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) :
    partitionHalfEdgeFlip (decoratedPathArrival P Q d hP hQ c ⟨0, decoratedPathLength_pos P Q d hP hQ c⟩) =
      (decoratedPathSelectedTerminal P Q d hP hQ c).val := by
  change partitionHalfEdgeFlip (partitionHalfEdgeFlip
      (partitionHalfEdgeSplice P Q (decoratedPathSelectedTerminal P Q d hP hQ c).val)) = _
  rw [partitionHalfEdgeFlip_involutive]
  exact (decoratedPathSelectedTerminal P Q d hP hQ c).property

theorem decoratedPathArrival_last (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) :
    decoratedPathArrival P Q d hP hQ c
      ⟨decoratedPathLength P Q d hP hQ c - 1, by have h := decoratedPathLength_pos P Q d hP hQ c; omega⟩ =
      ((partitionCoreTerminalPairing P Q).val (decoratedPathSelectedTerminal P Q d hP hQ c)).val := by
  unfold decoratedPathArrival
  rw [Nat.sub_add_cancel (decoratedPathLength_pos P Q d hP hQ c)]
  rw [decoratedPathLength_selected_period]
  rfl

theorem decoratedPathArrival_previous_departure_vertex (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) (i : Fin (decoratedPathLength P Q d hP hQ c - 1)) :
    partitionHalfEdgeVertex P Q (partitionHalfEdgeFlip
      (decoratedPathArrival P Q d hP hQ c ⟨i.val+1, by have h := i.isLt; omega⟩)) =
      partitionHalfEdgeVertex P Q (decoratedPathArrival P Q d hP hQ c ⟨i.val, by have h := i.isLt; omega⟩) := by
  unfold decoratedPathArrival
  rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, partitionHalfEdgeFlip_involutive]
  exact partitionHalfEdgeSplice_vertex P Q _

abbrev DecoratedGraphVertexAddresses (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :=
  Fin (Fintype.card (HighGraphVertices P Q)) ⊕ DecoratedInternalPositions P Q d hP hQ

noncomputable def decoratedDepartureAddress (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) (i : Fin (decoratedPathLength P Q d hP hQ c)) :
    DecoratedGraphVertexAddresses P Q d hP hQ :=
  if hz : i.val=0 then .inl (Quotient.out c).1 else .inr ⟨c,⟨i.val-1, by have h := i.isLt; omega⟩⟩

noncomputable def decoratedArrivalAddress (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) (i : Fin (decoratedPathLength P Q d hP hQ c)) :
    DecoratedGraphVertexAddresses P Q d hP hQ :=
  if hz : i.val+1=decoratedPathLength P Q d hP hQ c
    then .inl ((decoratedCompressedPairing P Q d hP hQ).val (Quotient.out c)).1
    else .inr ⟨c,⟨i.val, by have h := i.isLt; omega⟩⟩

theorem decoratedDepartureAddress_vertex (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e)
    (c : DecoratedCompressedPaths P Q d hP hQ) (i : Fin (decoratedPathLength P Q d hP hQ c)) :
    decoratedGraphVertexEquiv P Q d hP hQ hc (decoratedDepartureAddress P Q d hP hQ c i) =
      partitionHalfEdgeVertex P Q (partitionHalfEdgeFlip (decoratedPathArrival P Q d hP hQ c i)) := by
  unfold decoratedDepartureAddress
  split_ifs with hz
  · have hi : i=⟨0,decoratedPathLength_pos P Q d hP hQ c⟩ := Fin.ext hz
    rw [hi,decoratedPathArrival_first_departure,decoratedGraphVertexEquiv_high]
    exact (decoratedHalfEdgeEquiv_vertex P Q d hP hQ (Quotient.out c)).symm
  · rw [decoratedGraphVertexEquiv_internal]
    have hprev := decoratedPathArrival_previous_departure_vertex P Q d hP hQ c
      ⟨i.val-1, by have h := i.isLt; omega⟩
    have hi : (⟨i.val-1+1, by have h := i.isLt; omega⟩ : Fin (decoratedPathLength P Q d hP hQ c)) = i :=
      Fin.ext (by change i.val-1+1=i.val; omega)
    rw [hi] at hprev
    exact hprev.symm

theorem decoratedArrivalAddress_vertex (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e)
    (c : DecoratedCompressedPaths P Q d hP hQ) (i : Fin (decoratedPathLength P Q d hP hQ c)) :
    decoratedGraphVertexEquiv P Q d hP hQ hc (decoratedArrivalAddress P Q d hP hQ c i) =
      partitionHalfEdgeVertex P Q (decoratedPathArrival P Q d hP hQ c i) := by
  unfold decoratedArrivalAddress
  split_ifs with hz
  · have hi : i=⟨decoratedPathLength P Q d hP hQ c-1,
        by have h := decoratedPathLength_pos P Q d hP hQ c; omega⟩ :=
      Fin.ext (by change i.val=decoratedPathLength P Q d hP hQ c-1; omega)
    rw [hi,decoratedPathArrival_last,decoratedGraphVertexEquiv_high]
    change _ = partitionHalfEdgeVertex P Q
      ((partitionCoreTerminalPairing P Q).val (decoratedHalfEdgeEquiv P Q d hP hQ (Quotient.out c))).val
    rw [← decoratedHalfEdgeEquiv_pair]
    exact (decoratedHalfEdgeEquiv_vertex P Q d hP hQ _).symm
  · rw [decoratedGraphVertexEquiv_internal]

end TournamentHamiltonian
