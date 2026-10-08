import TournamentHamiltonian.CoreCompressionPaths
import TournamentHamiltonian.CoreCompressionWeights

/-! The actual numerical vertex labels split into high vertices and independent
internal positions along the compressed positive-length paths. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

abbrev CompressedInternalPositions (P Q : Setoid κ) :=
  Σ c : ActualCompressedPaths P Q, Fin (compressedPathLength P Q c - 1)

noncomputable def compressedInternalArrival (P Q : Setoid κ)
    (x : CompressedInternalPositions P Q) : PartitionHalfEdges (κ := κ) :=
  compressedPathArrival P Q x.1 ⟨x.2.val, by have h := x.2.isLt; omega⟩

noncomputable def compressedInternalVertex (P Q : Setoid κ)
    (x : CompressedInternalPositions P Q) : PartitionGraphVertices P Q :=
  partitionHalfEdgeVertex P Q (compressedInternalArrival P Q x)

theorem compressedInternalArrival_not_terminal (P Q : Setoid κ) (x : CompressedInternalPositions P Q) :
    partitionHalfEdgeSplice P Q (compressedInternalArrival P Q x) ≠ compressedInternalArrival P Q x := by
  let a : Equiv.Perm (PartitionHalfEdges (κ := κ)) := partitionHalfEdgeFlip
  let s := partitionHalfEdgeSplice P Q
  let z := compressedPathTerminal P Q x.1
  let k := x.2.val + 1
  have hp := involutionPathPeriod_pos a s z.val
  have hi := x.2.isLt
  have he := Nat.even_iff.mp (terminal_involutionPathPeriod_even a s partitionHalfEdgeFlip_involutive
    (partitionHalfEdgeSplice_involutive P Q) partitionHalfEdgeFlip_ne z.val z.property)
  have hd := Nat.mod_add_div (involutionPathPeriod a s z.val) 2
  have hl : k < involutionPathPeriod a s z.val := by
    change x.2.val < involutionPathPeriod a s z.val / 2 - 1 at hi
    omega
  intro hfix
  have hends := (terminal_on_path_iff a s partitionHalfEdgeFlip_involutive
    (partitionHalfEdgeSplice_involutive P Q) partitionHalfEdgeFlip_ne z.val z.property hl).mp hfix
  change x.2.val < involutionPathPeriod a s z.val / 2 - 1 at hi
  rcases hends with hends | hends <;> dsimp [k] at hends <;> omega

theorem compressedInternalVertex_degree (P Q : Setoid κ) (x : CompressedInternalPositions P Q) :
    partitionGraphDegree P Q (compressedInternalVertex P Q x) = 2 := by
  have hn := compressedInternalArrival_not_terminal P Q x
  have hd : (partitionClass (sumPartition P Q) (compressedInternalArrival P Q x)).card = 2 := by
    by_contra hd
    exact hn ((degreeTwoSplice_fixed_iff _ _).mpr hd)
  exact (partitionHalfEdge_class_card P Q _).symm.trans hd

theorem compressedPathArrival_flip_ne (P Q : Setoid κ)
    (c d : ActualCompressedPaths P Q) (i : Fin (compressedPathLength P Q c))
    (j : Fin (compressedPathLength P Q d)) :
    partitionHalfEdgeFlip (compressedPathArrival P Q c i) ≠ compressedPathArrival P Q d j := by
  intro hf
  have hprojection : Sum.elim id id (partitionHalfEdgeFlip (compressedPathArrival P Q c i)) =
      Sum.elim id id (compressedPathArrival P Q c i) := by
    generalize compressedPathArrival P Q c i = h
    cases h <;> rfl
  have hEdge : compressedPathOriginalEdge P Q ⟨c, i⟩ = compressedPathOriginalEdge P Q ⟨d, j⟩ :=
    hprojection.symm.trans (congrArg (Sum.elim id id) hf)
  have hData := compressedPathOriginalEdge_injective P Q hEdge
  have hHalf := congrArg (fun x : Σ c : ActualCompressedPaths P Q, Fin (compressedPathLength P Q c) =>
    compressedPathArrival P Q x.1 x.2) hData
  exact partitionHalfEdgeFlip_ne _ (hf.trans hHalf.symm)

theorem compressedInternalArrival_splice_next (P Q : Setoid κ) (x : CompressedInternalPositions P Q) :
    partitionHalfEdgeSplice P Q (compressedInternalArrival P Q x) = partitionHalfEdgeFlip
      (compressedPathArrival P Q x.1 ⟨x.2.val + 1, by have h := x.2.isLt; omega⟩) := by
  let p : Equiv.Perm (PartitionHalfEdges (κ := κ)) := partitionHalfEdgeFlip * partitionHalfEdgeSplice P Q
  change partitionHalfEdgeSplice P Q ((p ^ (x.2.val + 1)) (compressedPathTerminal P Q x.1).val) =
    partitionHalfEdgeFlip ((p ^ (x.2.val + 1 + 1)) (compressedPathTerminal P Q x.1).val)
  conv_rhs => rw [pow_succ', Equiv.Perm.mul_apply]
  change _ = partitionHalfEdgeFlip (partitionHalfEdgeFlip _)
  rw [partitionHalfEdgeFlip_involutive]

omit [Fintype κ] [DecidableEq κ] in
theorem partitionHalfEdge_vertex_eq_iff (P Q : Setoid κ) (x y : PartitionHalfEdges (κ := κ)) :
    partitionHalfEdgeVertex P Q x = partitionHalfEdgeVertex P Q y ↔ sumPartition P Q x y := by
  cases x <;> cases y
  · change Sum.inl (Quotient.mk P _) = Sum.inl (Quotient.mk P _) ↔ _
    rw [Sum.inl.injEq]
    exact Quotient.eq_iff_equiv
  · change Sum.inl (Quotient.mk P _) = Sum.inr (Quotient.mk Q _) ↔ False
    simp
  · change Sum.inr (Quotient.mk Q _) = Sum.inl (Quotient.mk P _) ↔ False
    simp
  · change Sum.inr (Quotient.mk Q _) = Sum.inr (Quotient.mk Q _) ↔ _
    rw [Sum.inr.injEq]
    exact Quotient.eq_iff_equiv

theorem compressedInternalVertex_injective (P Q : Setoid κ) :
    Function.Injective (compressedInternalVertex P Q) := by
  intro x y hvertex
  have hr := (partitionHalfEdge_vertex_eq_iff P Q _ _).mp hvertex
  have hmate := degreeTwoSplice_class_partner (sumPartition P Q) _ _ hr
    (compressedInternalArrival_not_terminal P Q x)
  rcases hmate with hsame | hsplice
  · let px : Σ c : ActualCompressedPaths P Q, Fin (compressedPathLength P Q c) :=
      ⟨x.1, ⟨x.2.val, by have h := x.2.isLt; omega⟩⟩
    let py : Σ c : ActualCompressedPaths P Q, Fin (compressedPathLength P Q c) :=
      ⟨y.1, ⟨y.2.val, by have h := y.2.isLt; omega⟩⟩
    have hEdge : compressedPathOriginalEdge P Q py = compressedPathOriginalEdge P Q px :=
      congrArg (Sum.elim id id) hsame
    have hData := compressedPathOriginalEdge_injective P Q hEdge
    have hfirst := congrArg Sigma.fst hData
    rcases x with ⟨c, i⟩
    rcases y with ⟨d, j⟩
    change d = c at hfirst
    subst d
    have hsecond : j.val = i.val := congrArg (fun z : Σ c : ActualCompressedPaths P Q,
      Fin (compressedPathLength P Q c) => z.2.val) hData
    exact Sigma.ext rfl (heq_of_eq (Fin.ext hsecond.symm))
  · change compressedInternalArrival P Q y = partitionHalfEdgeSplice P Q (compressedInternalArrival P Q x) at hsplice
    rw [compressedInternalArrival_splice_next] at hsplice
    exact (compressedPathArrival_flip_ne P Q x.1 y.1 _ _ hsplice.symm).elim

noncomputable def compressedGraphVertex (P Q : Setoid κ) :
    HighGraphVertices P Q ⊕ CompressedInternalPositions P Q → PartitionGraphVertices P Q :=
  Sum.elim Subtype.val (compressedInternalVertex P Q)

theorem compressedGraphVertex_injective (P Q : Setoid κ) :
    Function.Injective (compressedGraphVertex P Q) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext hxy)
      | inr y =>
          have hd := congrArg (partitionGraphDegree P Q) hxy
          change partitionGraphDegree P Q x.val = partitionGraphDegree P Q (compressedInternalVertex P Q y) at hd
          rw [compressedInternalVertex_degree] at hd
          have hx := x.property
          omega
  | inr x =>
      cases y with
      | inl y =>
          have hd := congrArg (partitionGraphDegree P Q) hxy
          change partitionGraphDegree P Q (compressedInternalVertex P Q x) = partitionGraphDegree P Q y.val at hd
          rw [compressedInternalVertex_degree] at hd
          have hy := y.property
          omega
      | inr y => exact congrArg Sum.inr (compressedInternalVertex_injective P Q hxy)

omit [DecidableEq κ] in
theorem highGraphVertices_card (P Q : Setoid κ) :
    Fintype.card (HighGraphVertices P Q) = (highDegreeVertices P Q).card := by
  rw [Fintype.card_subtype]
  rfl

theorem compressedInternalPositions_card_add_paths (P Q : Setoid κ)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    Fintype.card (CompressedInternalPositions P Q) + Fintype.card (ActualCompressedPaths P Q) = Fintype.card κ := by
  have hlen := compressedPathPosition_card P Q hc
  rw [Fintype.card_sigma] at hlen
  simp only [Fintype.card_fin] at hlen
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    _ = (∑ c : ActualCompressedPaths P Q, (compressedPathLength P Q c - 1)) +
        (∑ _c : ActualCompressedPaths P Q, 1) := by simp
    _ = ∑ c : ActualCompressedPaths P Q, (compressedPathLength P Q c - 1 + 1) :=
      (Finset.sum_add_distrib).symm
    _ = ∑ c : ActualCompressedPaths P Q, compressedPathLength P Q c := by
      apply Finset.sum_congr rfl
      intro c _
      exact Nat.sub_add_cancel (compressedPathLength_pos P Q c)
    _ = _ := hlen

theorem compressedGraphVertex_card (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    Fintype.card (HighGraphVertices P Q ⊕ CompressedInternalPositions P Q) =
      Fintype.card (PartitionGraphVertices P Q) := by
  have hlen := compressedInternalPositions_card_add_paths P Q hc
  have hpaths := actualCompressedPairPartition_card P Q hP hQ
  have hv := partitionGraph_vertex_count_le P Q hP hQ
  rw [Fintype.card_sum, highGraphVertices_card]
  unfold partitionGraphExcess at hpaths
  change Fintype.card (ActualCompressedPaths P Q) = _ at hpaths
  omega

theorem compressedGraphVertex_bijective (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    Function.Bijective (compressedGraphVertex P Q) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨compressedGraphVertex_injective P Q, compressedGraphVertex_card P Q hP hQ hc⟩

noncomputable def compressedGraphVertexEquiv (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    (HighGraphVertices P Q ⊕ CompressedInternalPositions P Q) ≃ PartitionGraphVertices P Q :=
  Equiv.ofBijective (compressedGraphVertex P Q) (compressedGraphVertex_bijective P Q hP hQ hc)

end TournamentHamiltonian
