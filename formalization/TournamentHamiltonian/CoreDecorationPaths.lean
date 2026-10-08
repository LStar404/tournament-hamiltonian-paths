import TournamentHamiltonian.CoreDecorationCoordinates
import TournamentHamiltonian.CoreCompressionEndpoints
import Mathlib.Data.Fin.Rev

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ]

abbrev DecoratedCompressedPaths (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :=
  Quotient (pairingSetoid (decoratedCompressedPairing P Q d hP hQ))

noncomputable def decoratedPathSelectedTerminal (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) : TerminalHalfEdges (partitionHalfEdgeSplice P Q) :=
  decoratedHalfEdgeEquiv P Q d hP hQ (Quotient.out c)

noncomputable def decoratedPathLength (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) : ℕ :=
  compressedPathLength P Q (decoratedCompressedPathEquiv P Q d hP hQ c)

theorem decoratedPathSelectedTerminal_class (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) :
    Quotient.mk (actualCompressedPairPartition P Q) (decoratedPathSelectedTerminal P Q d hP hQ c) =
      decoratedCompressedPathEquiv P Q d hP hQ c := by
  change decoratedCompressedPathEquiv P Q d hP hQ (Quotient.mk _ (Quotient.out c)) = _
  rw [Quotient.out_eq]

theorem decoratedPathSelectedTerminal_cases (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) :
    decoratedPathSelectedTerminal P Q d hP hQ c =
      compressedPathTerminal P Q (decoratedCompressedPathEquiv P Q d hP hQ c) ∨
    decoratedPathSelectedTerminal P Q d hP hQ c =
      compressedPathEndTerminal P Q (decoratedCompressedPathEquiv P Q d hP hQ c) := by
  have hq := decoratedPathSelectedTerminal_class P Q d hP hQ c
  have ht : Quotient.mk (actualCompressedPairPartition P Q)
      (compressedPathTerminal P Q (decoratedCompressedPathEquiv P Q d hP hQ c)) =
        decoratedCompressedPathEquiv P Q d hP hQ c := Quotient.out_eq _
  have hr := Quotient.exact (hq.trans ht.symm)
  change _ = _ ∨ (partitionCoreTerminalPairing P Q).val _ = _ at hr
  rcases hr with hr | hr
  · exact Or.inl hr
  · right
    have h := congrArg (partitionCoreTerminalPairing P Q).val hr
    rw [(partitionCoreTerminalPairing P Q).property.1] at h
    exact h

theorem decoratedPathLength_pos (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) : 0 < decoratedPathLength P Q d hP hQ c :=
  compressedPathLength_pos P Q _

theorem decoratedPathLength_selected_period (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) :
    decoratedPathLength P Q d hP hQ c =
      involutionPathPeriod partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q)
        (decoratedPathSelectedTerminal P Q d hP hQ c).val / 2 := by
  rcases decoratedPathSelectedTerminal_cases P Q d hP hQ c with h | h
  · rw [h]; rfl
  · rw [h]
    change _ = involutionPathPeriod partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q)
      (pathTerminalPartner _ _ _) / 2
    unfold pathTerminalPartner
    rw [involutionPathPeriod_at_pow]
    rfl

noncomputable def decoratedPathPositionEquiv (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) :
    Fin (decoratedPathLength P Q d hP hQ c) ≃
      Fin (compressedPathLength P Q (decoratedCompressedPathEquiv P Q d hP hQ c)) :=
  if decoratedPathSelectedTerminal P Q d hP hQ c =
      compressedPathTerminal P Q (decoratedCompressedPathEquiv P Q d hP hQ c)
    then Equiv.refl _ else Fin.revPerm

noncomputable def decoratedPathEdgeAssignment (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    (Σ c : DecoratedCompressedPaths P Q d hP hQ, Fin (decoratedPathLength P Q d hP hQ c)) ≃ κ :=
  ((Equiv.sigmaCongrRight (decoratedPathPositionEquiv P Q d hP hQ)).trans
    (Equiv.sigmaCongrLeft (β := fun c : ActualCompressedPaths P Q => Fin (compressedPathLength P Q c))
      (decoratedCompressedPathEquiv P Q d hP hQ))).trans
      (compressedPathEdgeEquiv P Q hc)

theorem decoratedPathLength_sum (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    (∑ c : DecoratedCompressedPaths P Q d hP hQ, decoratedPathLength P Q d hP hQ c) = Fintype.card κ := by
  have h := Fintype.card_congr (decoratedPathEdgeAssignment P Q d hP hQ hc)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

end TournamentHamiltonian
