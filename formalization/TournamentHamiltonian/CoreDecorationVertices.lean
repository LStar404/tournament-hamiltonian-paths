import TournamentHamiltonian.CorePathReversal

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ]

abbrev DecoratedInternalPositions (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :=
  Σ c : DecoratedCompressedPaths P Q d hP hQ, Fin (decoratedPathLength P Q d hP hQ c - 1)

noncomputable def decoratedInternalPositionEquiv (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) :
    Fin (decoratedPathLength P Q d hP hQ c - 1) ≃
      Fin (compressedPathLength P Q (decoratedCompressedPathEquiv P Q d hP hQ c) - 1) :=
  if decoratedPathSelectedTerminal P Q d hP hQ c =
      compressedPathTerminal P Q (decoratedCompressedPathEquiv P Q d hP hQ c)
    then Equiv.refl _ else Fin.revPerm

noncomputable def decoratedInternalPositionsEquiv (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    DecoratedInternalPositions P Q d hP hQ ≃ CompressedInternalPositions P Q :=
  (Equiv.sigmaCongrRight (decoratedInternalPositionEquiv P Q d hP hQ)).trans
    (Equiv.sigmaCongrLeft (β := fun c : ActualCompressedPaths P Q => Fin (compressedPathLength P Q c - 1))
      (decoratedCompressedPathEquiv P Q d hP hQ))

noncomputable def decoratedGraphVertexEquiv (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    (Fin (Fintype.card (HighGraphVertices P Q)) ⊕ DecoratedInternalPositions P Q d hP hQ) ≃
      PartitionGraphVertices P Q :=
  (Equiv.sumCongr d.1 (decoratedInternalPositionsEquiv P Q d hP hQ)).trans
    (compressedGraphVertexEquiv P Q hP hQ hc)

theorem decoratedInternalVertex_reading (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) (i : Fin (decoratedPathLength P Q d hP hQ c - 1)) :
    partitionHalfEdgeVertex P Q
      (decoratedPathArrival P Q d hP hQ c ⟨i.val, by have h := i.isLt; omega⟩) =
      compressedInternalVertex P Q (decoratedInternalPositionsEquiv P Q d hP hQ ⟨c,i⟩) := by
  rw [decoratedPathArrival_reading]
  change _ = compressedInternalVertex P Q
    ⟨decoratedCompressedPathEquiv P Q d hP hQ c, decoratedInternalPositionEquiv P Q d hP hQ c i⟩
  unfold decoratedInternalPositionEquiv
  split_ifs
  · rfl
  · have hv : (Fin.rev (⟨i.val, by have h := i.isLt; omega⟩ : Fin (decoratedPathLength P Q d hP hQ c))).val =
        (Fin.rev i).val + 1 := by
      simp only [Fin.val_rev]
      have hi := i.isLt
      omega
    have hp := compressedPathArrival_previous_departure_vertex P Q
      (decoratedCompressedPathEquiv P Q d hP hQ c) (Fin.rev i)
    convert hp using 1
    apply congrArg (partitionHalfEdgeVertex P Q)
    apply congrArg partitionHalfEdgeFlip
    apply congrArg (compressedPathArrival P Q _)
    exact Fin.ext hv
    rfl

theorem decoratedGraphVertexEquiv_high (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) (i : Fin (Fintype.card (HighGraphVertices P Q))) :
    decoratedGraphVertexEquiv P Q d hP hQ hc (.inl i) = (d.1 i).val := rfl

theorem decoratedGraphVertexEquiv_internal (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e)
    (c : DecoratedCompressedPaths P Q d hP hQ) (i : Fin (decoratedPathLength P Q d hP hQ c - 1)) :
    decoratedGraphVertexEquiv P Q d hP hQ hc (.inr ⟨c,i⟩) =
      partitionHalfEdgeVertex P Q
        (decoratedPathArrival P Q d hP hQ c ⟨i.val, by have h := i.isLt; omega⟩) :=
  (decoratedInternalVertex_reading P Q d hP hQ c i).symm

end TournamentHamiltonian
