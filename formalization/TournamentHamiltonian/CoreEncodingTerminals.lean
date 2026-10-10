import TournamentHamiltonian.CoreEncodingDecoder

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {b : ℕ}

noncomputable def encodedTerminalPosition {d : Fin b → ℕ} (p : PairingMap (EncodedCoreHalfEdges d))
    (L : EncodedCorePaths p → ℕ) (hL : ∀ c, 0 < L c) (x : EncodedCoreHalfEdges d) :
    Σ c : EncodedCorePaths p, Fin (L c) :=
  let c : EncodedCorePaths p := Quotient.mk _ x
  ⟨c, if x=Quotient.out c then ⟨0,hL c⟩ else ⟨L c-1,by have h := hL c; omega⟩⟩

noncomputable def encodedTerminalHalfEdge {κ : Type*} {d : Fin b → ℕ} (colors : Fin b → Bool)
    (p : PairingMap (EncodedCoreHalfEdges d)) (L : EncodedCorePaths p → ℕ) (hL : ∀ c, 0 < L c)
    (a : (Σ c : EncodedCorePaths p, Fin (L c)) ≃ κ) (x : EncodedCoreHalfEdges d) :
    PartitionHalfEdges (κ := κ) :=
  halfEdgeAtSide (colors x.1) (a (encodedTerminalPosition p L hL x))

theorem pairing_label_out_cases {d : Fin b → ℕ} (p : PairingMap (EncodedCoreHalfEdges d))
    (x : EncodedCoreHalfEdges d) :
    x=Quotient.out (Quotient.mk (pairingSetoid p) x) ∨
      x=p.val (Quotient.out (Quotient.mk (pairingSetoid p) x)) := by
  have h := Quotient.exact (Quotient.out_eq (Quotient.mk (pairingSetoid p) x))
  change _=_ ∨ p.val _=x at h
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem partitionHalfEdge_original_flip {κ : Type*} (x : PartitionHalfEdges (κ := κ)) :
    Sum.elim id id (partitionHalfEdgeFlip x) = Sum.elim id id x := by cases x <;> rfl

variable {κ : Type*} [Fintype κ]

theorem encodedTerminalHalfEdge_actual (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) (x : DecoratedCoreHalfEdges P Q d) :
    encodedTerminalHalfEdge (decoratedCoreColor P Q d) (decoratedCompressedPairing P Q d hP hQ)
      (decoratedPathLength P Q d hP hQ) (decoratedPathLength_pos P Q d hP hQ)
      (decoratedPathEdgeAssignment P Q d hP hQ hc) x = (decoratedHalfEdgeEquiv P Q d hP hQ x).val := by
  unfold encodedTerminalHalfEdge encodedTerminalPosition
  dsimp only
  rw [decoratedCoreColor_halfEdgeSide]
  split_ifs with hx
  · have ht : decoratedPathSelectedTerminal P Q d hP hQ (Quotient.mk _ x) =
        decoratedHalfEdgeEquiv P Q d hP hQ x := by
      unfold decoratedPathSelectedTerminal
      rw [← hx]
    rw [decoratedPathEdgeAssignment_reading]
    have hf := congrArg (Sum.elim id id) (decoratedPathArrival_first_departure P Q d hP hQ (Quotient.mk _ x))
    rw [partitionHalfEdge_original_flip, ht] at hf
    rw [hf]
    exact halfEdgeAtSide_side_original _
  · have hp := (pairing_label_out_cases (decoratedCompressedPairing P Q d hP hQ) x).resolve_left hx
    have ht : (partitionCoreTerminalPairing P Q).val
        (decoratedPathSelectedTerminal P Q d hP hQ (Quotient.mk _ x)) =
        decoratedHalfEdgeEquiv P Q d hP hQ x := by
      change (partitionCoreTerminalPairing P Q).val
        (decoratedHalfEdgeEquiv P Q d hP hQ (Quotient.out (Quotient.mk _ x))) = _
      rw [← decoratedHalfEdgeEquiv_pair, ← hp]
    rw [decoratedPathEdgeAssignment_reading, decoratedPathArrival_last, ht]
    exact halfEdgeAtSide_side_original _

theorem decoratedHalfEdgeEquiv_injective_decorations (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (d e : HighVertexDecorations P Q)
    (hterminal : ∀ i k (hd : k < decoratedCoreDegree P Q d i) (he : k < decoratedCoreDegree P Q e i),
      (decoratedHalfEdgeEquiv P Q d hP hQ ⟨i,⟨k,hd⟩⟩).val =
        (decoratedHalfEdgeEquiv P Q e hP hQ ⟨i,⟨k,he⟩⟩).val) : d=e := by
  have h1 : d.1=e.1 := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    have hd : 0 < decoratedCoreDegree P Q d i := by have h := decoratedCoreDegree_ge_three P Q d i; omega
    have he : 0 < decoratedCoreDegree P Q e i := by have h := decoratedCoreDegree_ge_three P Q e i; omega
    have h := congrArg (partitionHalfEdgeVertex P Q) (hterminal i 0 hd he)
    simpa only [decoratedHalfEdgeEquiv_vertex] using h
  rcases d with ⟨d1,d2⟩
  rcases e with ⟨e1,e2⟩
  change d1=e1 at h1
  subst e1
  congr 1
  funext v
  obtain ⟨i,rfl⟩ := d1.surjective v
  apply Equiv.ext
  intro k
  apply Subtype.ext
  exact hterminal i k.val k.isLt k.isLt

end TournamentHamiltonian
