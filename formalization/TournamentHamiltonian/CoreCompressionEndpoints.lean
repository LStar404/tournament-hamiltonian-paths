import TournamentHamiltonian.CoreCompressionVertices
import TournamentHamiltonian.GaussianChains

/-! Actual high endpoints, internal vertex addresses, and alternating matrix orientation. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def partitionHalfEdgeSide : PartitionHalfEdges (κ := κ) → Bool := Sum.elim (fun _ => false) (fun _ => true)

def partitionGraphVertexSide (P Q : Setoid κ) : PartitionGraphVertices P Q → Bool :=
  Sum.elim (fun _ => false) (fun _ => true)

omit [Fintype κ] [DecidableEq κ] in
theorem partitionHalfEdgeSide_vertex (P Q : Setoid κ) (x : PartitionHalfEdges (κ := κ)) :
    partitionGraphVertexSide P Q (partitionHalfEdgeVertex P Q x) = partitionHalfEdgeSide x := by
  cases x <;> rfl

omit [Fintype κ] [DecidableEq κ] in
theorem partitionHalfEdgeSide_flip (x : PartitionHalfEdges (κ := κ)) :
    partitionHalfEdgeSide (partitionHalfEdgeFlip x) = !partitionHalfEdgeSide x := by
  cases x <;> rfl

theorem partitionHalfEdgeSide_splice (P Q : Setoid κ) (x : PartitionHalfEdges (κ := κ)) :
    partitionHalfEdgeSide (partitionHalfEdgeSplice P Q x) = partitionHalfEdgeSide x := by
  have h := congrArg (partitionGraphVertexSide P Q) (partitionHalfEdgeSplice_vertex P Q x)
  simpa only [partitionHalfEdgeSide_vertex] using h

theorem partitionHalfEdgeSide_path_pow (P Q : Setoid κ) (x : PartitionHalfEdges (κ := κ)) (k : ℕ) :
    partitionHalfEdgeSide ((((partitionHalfEdgeFlip : Equiv.Perm (PartitionHalfEdges (κ := κ))) * partitionHalfEdgeSplice P Q) ^ k) x) =
      chainEndpointOrientation k (partitionHalfEdgeSide x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      rw [Equiv.Perm.mul_apply, partitionHalfEdgeSide_flip, partitionHalfEdgeSide_splice]
      rfl

noncomputable def compressedPathStartVertex (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : ActualCompressedPaths P Q) : HighGraphVertices P Q :=
  ⟨partitionHalfEdgeVertex P Q (compressedPathTerminal P Q c).val,
    (partitionHalfEdgeSplice_fixed_iff P Q hP hQ _).mp (compressedPathTerminal P Q c).property⟩

noncomputable def compressedPathEndTerminal (P Q : Setoid κ) (c : ActualCompressedPaths P Q) :
    TerminalHalfEdges (partitionHalfEdgeSplice P Q) :=
  (partitionCoreTerminalPairing P Q).val (compressedPathTerminal P Q c)

noncomputable def compressedPathEndVertex (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : ActualCompressedPaths P Q) : HighGraphVertices P Q :=
  ⟨partitionHalfEdgeVertex P Q (compressedPathEndTerminal P Q c).val,
    (partitionHalfEdgeSplice_fixed_iff P Q hP hQ _).mp (compressedPathEndTerminal P Q c).property⟩

theorem compressedPathArrival_last (P Q : Setoid κ) (c : ActualCompressedPaths P Q) :
    compressedPathArrival P Q c ⟨compressedPathLength P Q c - 1, by have h := compressedPathLength_pos P Q c; omega⟩ =
      (compressedPathEndTerminal P Q c).val := by
  change (((partitionHalfEdgeFlip : Equiv.Perm (PartitionHalfEdges (κ := κ))) * partitionHalfEdgeSplice P Q) ^ (compressedPathLength P Q c - 1 + 1))
      (compressedPathTerminal P Q c).val = pathTerminalPartner _ _ _
  rw [Nat.sub_add_cancel (compressedPathLength_pos P Q c)]
  rfl

theorem compressedPathArrival_first_departure (P Q : Setoid κ) (c : ActualCompressedPaths P Q) :
    partitionHalfEdgeFlip (compressedPathArrival P Q c ⟨0, compressedPathLength_pos P Q c⟩) =
      (compressedPathTerminal P Q c).val := by
  change partitionHalfEdgeFlip (((partitionHalfEdgeFlip : Equiv.Perm (PartitionHalfEdges (κ := κ))) * partitionHalfEdgeSplice P Q)
    (compressedPathTerminal P Q c).val) = _
  rw [Equiv.Perm.mul_apply, partitionHalfEdgeFlip_involutive]
  exact (compressedPathTerminal P Q c).property

theorem compressedPathArrival_departure_side (P Q : Setoid κ) (c : ActualCompressedPaths P Q)
    (i : Fin (compressedPathLength P Q c)) :
    partitionHalfEdgeSide (partitionHalfEdgeFlip (compressedPathArrival P Q c i)) =
      chainEndpointOrientation i.val (partitionHalfEdgeSide (compressedPathTerminal P Q c).val) := by
  change partitionHalfEdgeSide (partitionHalfEdgeFlip
    ((((partitionHalfEdgeFlip : Equiv.Perm (PartitionHalfEdges (κ := κ))) * partitionHalfEdgeSplice P Q) ^ (i.val + 1)) (compressedPathTerminal P Q c).val)) = _
  rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, partitionHalfEdgeFlip_involutive]
  rw [partitionHalfEdgeSide_splice, partitionHalfEdgeSide_path_pow]

theorem compressedPathArrival_internal_vertex (P Q : Setoid κ) (c : ActualCompressedPaths P Q)
    (i : Fin (compressedPathLength P Q c - 1)) :
    partitionHalfEdgeVertex P Q (compressedPathArrival P Q c ⟨i.val, by have h := i.isLt; omega⟩) =
      compressedInternalVertex P Q ⟨c, i⟩ := rfl

theorem compressedPathArrival_previous_departure_vertex (P Q : Setoid κ) (c : ActualCompressedPaths P Q)
    (i : Fin (compressedPathLength P Q c - 1)) :
    partitionHalfEdgeVertex P Q (partitionHalfEdgeFlip
      (compressedPathArrival P Q c ⟨i.val + 1, by have h := i.isLt; omega⟩)) =
      compressedInternalVertex P Q ⟨c, i⟩ := by
  rw [← compressedInternalArrival_splice_next P Q ⟨c, i⟩]
  exact partitionHalfEdgeSplice_vertex P Q _

theorem compressedPathArrival_first_departure_vertex (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) (c : ActualCompressedPaths P Q) :
    partitionHalfEdgeVertex P Q (partitionHalfEdgeFlip
      (compressedPathArrival P Q c ⟨0, compressedPathLength_pos P Q c⟩)) =
      (compressedPathStartVertex P Q hP hQ c).val := by
  rw [compressedPathArrival_first_departure]
  rfl

theorem compressedPathArrival_last_vertex (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) (c : ActualCompressedPaths P Q) :
    partitionHalfEdgeVertex P Q
      (compressedPathArrival P Q c ⟨compressedPathLength P Q c - 1, by have h := compressedPathLength_pos P Q c; omega⟩) =
      (compressedPathEndVertex P Q hP hQ c).val := by
  rw [compressedPathArrival_last]
  rfl

theorem compressedGraphVertexEquiv_high (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) (v : HighGraphVertices P Q) :
    compressedGraphVertexEquiv P Q hP hQ hc (.inl v) = v.val := rfl

theorem compressedGraphVertexEquiv_internal (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) (x : CompressedInternalPositions P Q) :
    compressedGraphVertexEquiv P Q hP hQ hc (.inr x) = compressedInternalVertex P Q x := rfl

end TournamentHamiltonian
