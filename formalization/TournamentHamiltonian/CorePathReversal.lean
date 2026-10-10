import TournamentHamiltonian.CoreDecorationPaths

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {α : Type*} [Fintype α]

omit [Fintype α] in
theorem terminal_path_reverse_arrival (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s)
    (hfree : ∀ x, a x ≠ x) (x : α) (hx : s x = x)
    (i : Fin (involutionPathPeriod a s x / 2)) :
    ((a * s) ^ (i.val + 1)) (pathTerminalPartner a s x) =
      a (((a * s) ^ ((involutionPathPeriod a s x / 2) - 1 - i.val + 1)) x) := by
  let p := a * s
  let L := involutionPathPeriod a s x / 2
  have he := Nat.even_iff.mp (terminal_involutionPathPeriod_even a s ha hs hfree x hx)
  have hd := Nat.mod_add_div (involutionPathPeriod a s x) 2
  have hperiod : L + L = involutionPathPeriod a s x := by dsimp [L]; omega
  have hi : i.val < L := i.isLt
  have hsum : (L - 1 - i.val) + (i.val + 1 + L) = L + L := by omega
  change (p ^ (i.val + 1)) ((p ^ L) x) = a ((p ^ (L - 1 - i.val + 1)) x)
  rw [terminal_edge_reflection_succ a s ha hs x hx]
  apply (p ^ (L - 1 - i.val)).injective
  change (p ^ (L - 1 - i.val)) ((p ^ (i.val + 1)) ((p ^ L) x)) =
    (p ^ (L - 1 - i.val)) ((p ^ (L - 1 - i.val))⁻¹ x)
  simp only [← Equiv.Perm.mul_apply, ← pow_add, mul_inv_cancel, Equiv.Perm.one_apply]
  rw [hsum, hperiod]
  exact involutionPathPeriod_pow a s x

variable {κ : Type*} [Fintype κ]

theorem compressedPath_reverse_arrival (P Q : Setoid κ) (c : ActualCompressedPaths P Q)
    (i : Fin (compressedPathLength P Q c)) :
    (((partitionHalfEdgeFlip : Equiv.Perm (PartitionHalfEdges (κ := κ))) * partitionHalfEdgeSplice P Q) ^ (i.val + 1))
      (compressedPathEndTerminal P Q c).val =
      partitionHalfEdgeFlip (compressedPathArrival P Q c (Fin.rev i)) := by
  have h := terminal_path_reverse_arrival partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q)
    partitionHalfEdgeFlip_involutive (partitionHalfEdgeSplice_involutive P Q) partitionHalfEdgeFlip_ne
    (compressedPathTerminal P Q c).val (compressedPathTerminal P Q c).property i
  have hv : (Fin.rev i).val = compressedPathLength P Q c - 1 - i.val := by
    simp only [Fin.val_rev]
    omega
  change (((partitionHalfEdgeFlip : Equiv.Perm (PartitionHalfEdges (κ := κ))) * partitionHalfEdgeSplice P Q) ^ (i.val + 1))
      (pathTerminalPartner partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q) (compressedPathTerminal P Q c).val) =
    partitionHalfEdgeFlip
      ((((partitionHalfEdgeFlip : Equiv.Perm (PartitionHalfEdges (κ := κ))) * partitionHalfEdgeSplice P Q) ^ ((Fin.rev i).val + 1))
        (compressedPathTerminal P Q c).val)
  rw [hv]
  exact h

noncomputable def decoratedPathArrival (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) (i : Fin (decoratedPathLength P Q d hP hQ c)) :
    PartitionHalfEdges (κ := κ) :=
  (((partitionHalfEdgeFlip : Equiv.Perm (PartitionHalfEdges (κ := κ))) * partitionHalfEdgeSplice P Q) ^ (i.val + 1))
    (decoratedPathSelectedTerminal P Q d hP hQ c).val

theorem decoratedPathArrival_reading (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) (i : Fin (decoratedPathLength P Q d hP hQ c)) :
    decoratedPathArrival P Q d hP hQ c i =
      if decoratedPathSelectedTerminal P Q d hP hQ c =
          compressedPathTerminal P Q (decoratedCompressedPathEquiv P Q d hP hQ c)
      then compressedPathArrival P Q (decoratedCompressedPathEquiv P Q d hP hQ c) i
      else partitionHalfEdgeFlip
        (compressedPathArrival P Q (decoratedCompressedPathEquiv P Q d hP hQ c) (Fin.rev i)) := by
  split_ifs with h
  · unfold decoratedPathArrival
    rw [h]
    rfl
  · have he := (decoratedPathSelectedTerminal_cases P Q d hP hQ c).resolve_left h
    unfold decoratedPathArrival
    rw [he]
    exact compressedPath_reverse_arrival P Q _ i

theorem decoratedPathEdgeAssignment_reading (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e)
    (c : DecoratedCompressedPaths P Q d hP hQ) (i : Fin (decoratedPathLength P Q d hP hQ c)) :
    decoratedPathEdgeAssignment P Q d hP hQ hc ⟨c,i⟩ =
      Sum.elim id id (decoratedPathArrival P Q d hP hQ c i) := by
  change compressedPathOriginalEdge P Q
      ⟨decoratedCompressedPathEquiv P Q d hP hQ c, decoratedPathPositionEquiv P Q d hP hQ c i⟩ = _
  rw [decoratedPathArrival_reading]
  unfold decoratedPathPositionEquiv
  split_ifs
  · rfl
  · change Sum.elim id id (compressedPathArrival P Q _ (Fin.rev i)) =
      Sum.elim id id (partitionHalfEdgeFlip (compressedPathArrival P Q _ (Fin.rev i)))
    cases compressedPathArrival P Q (decoratedCompressedPathEquiv P Q d hP hQ c) (Fin.rev i) <;> rfl

end TournamentHamiltonian
