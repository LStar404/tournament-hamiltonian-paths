import TournamentHamiltonian.CoreCompressionVertices
import TournamentHamiltonian.CoreCompressionWeights
import TournamentHamiltonian.CompressedCoreMajorant

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ]

noncomputable def terminalHighIncidentEquiv (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    TerminalHalfEdges (partitionHalfEdgeSplice P Q) ≃
      Σ v : HighGraphVertices P Q, HighIncidentHalfEdges P Q v where
  toFun x := ⟨⟨partitionHalfEdgeVertex P Q x.val,
    (partitionHalfEdgeSplice_fixed_iff P Q hP hQ x.val).mp x.property⟩, ⟨x.val, rfl⟩⟩
  invFun x := ⟨x.2.val, (partitionHalfEdgeSplice_fixed_iff P Q hP hQ x.2.val).mpr
    (by rw [x.2.property]; exact x.1.property)⟩
  left_inv x := rfl
  right_inv := by
    rintro ⟨⟨v, hv⟩, ⟨x, hx⟩⟩
    dsimp at hx
    subst v
    rfl

noncomputable def decoratedCoreDegree (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (i : Fin (Fintype.card (HighGraphVertices P Q))) : ℕ :=
  Fintype.card (HighIncidentHalfEdges P Q (d.1 i))

abbrev DecoratedCoreHalfEdges (P Q : Setoid κ) (d : HighVertexDecorations P Q) :=
  Σ i : Fin (Fintype.card (HighGraphVertices P Q)), Fin (decoratedCoreDegree P Q d i)

noncomputable def decoratedHalfEdgeEquiv (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    DecoratedCoreHalfEdges P Q d ≃ TerminalHalfEdges (partitionHalfEdgeSplice P Q) :=
  ((Equiv.sigmaCongrRight (fun i => d.2 (d.1 i))).trans
    (Equiv.sigmaCongrLeft d.1)).trans (terminalHighIncidentEquiv P Q hP hQ).symm

theorem decoratedCoreDegree_ge_three (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (i : Fin (Fintype.card (HighGraphVertices P Q))) : 3 ≤ decoratedCoreDegree P Q d i := by
  rw [decoratedCoreDegree, highIncidentHalfEdges_card]
  exact (d.1 i).property

theorem decoratedCoreDegree_sum (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    (∑ i, decoratedCoreDegree P Q d i) =
      2 * (Fintype.card (HighGraphVertices P Q) + partitionGraphExcess P Q) := by
  have h := Fintype.card_congr (decoratedHalfEdgeEquiv P Q d hP hQ)
  rw [Fintype.card_sigma] at h
  simp only [Fintype.card_fin] at h
  rw [partitionCoreTerminal_card P Q hP hQ, ← highGraphVertices_card P Q] at h
  exact h

theorem decoratedCoreDegree_mem (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    decoratedCoreDegree P Q d ∈ compressedDegreeSequences
      (partitionGraphExcess P Q) (Fintype.card (HighGraphVertices P Q)) :=
  mem_compressedDegreeSequences.mpr ⟨decoratedCoreDegree_sum P Q d hP hQ,
    decoratedCoreDegree_ge_three P Q d⟩

noncomputable def conjugatePairingMap {α β : Type*} (e : α ≃ β) (p : PairingMap β) :
    PairingMap α :=
  ⟨fun x => e.symm (p.val (e x)),
    (by intro x; simp only [Equiv.apply_symm_apply]; rw [p.property.1 (e x), Equiv.symm_apply_apply]),
    (by intro x h; exact p.property.2 (e x) (by simpa only [Equiv.apply_symm_apply] using congrArg e h))⟩

noncomputable def conjugatePairingQuotientEquiv {α β : Type*} (e : α ≃ β) (p : PairingMap β) :
    Quotient (pairingSetoid (conjugatePairingMap e p)) ≃ Quotient (pairingSetoid p) :=
  Quotient.congr e (by
    intro x y
    change (x = y ∨ e.symm (p.val (e x)) = y) ↔ (e x = e y ∨ p.val (e x) = e y)
    constructor
    · rintro (h | h)
      · exact Or.inl (congrArg e h)
      · exact Or.inr (by simpa only [Equiv.apply_symm_apply] using congrArg e h)
    · rintro (h | h)
      · exact Or.inl (e.injective h)
      · exact Or.inr (by simpa only [Equiv.symm_apply_apply] using congrArg e.symm h))

noncomputable def decoratedCompressedPairing (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    PairingMap (DecoratedCoreHalfEdges P Q d) :=
  conjugatePairingMap (decoratedHalfEdgeEquiv P Q d hP hQ) (partitionCoreTerminalPairing P Q)

noncomputable def decoratedCompressedPathEquiv (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    Quotient (pairingSetoid (decoratedCompressedPairing P Q d hP hQ)) ≃ ActualCompressedPaths P Q :=
  conjugatePairingQuotientEquiv (decoratedHalfEdgeEquiv P Q d hP hQ) (partitionCoreTerminalPairing P Q)

noncomputable def decoratedCoreColor (P Q : Setoid κ) (d : HighVertexDecorations P Q) :
    Fin (Fintype.card (HighGraphVertices P Q)) → Bool :=
  fun i => match (d.1 i).val with | Sum.inl _ => false | Sum.inr _ => true

theorem decoratedCoreColor_choices (b : ℕ) : Fintype.card (Fin b → Bool) = 2 ^ b := by simp

end TournamentHamiltonian
