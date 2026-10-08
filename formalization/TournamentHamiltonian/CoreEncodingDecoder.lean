import TournamentHamiltonian.CoreDecorationIncidence

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {b : ℕ}

abbrev EncodedCoreHalfEdges (d : Fin b → ℕ) := Σ i : Fin b, Fin (d i)
abbrev EncodedCorePaths {d : Fin b → ℕ} (p : PairingMap (EncodedCoreHalfEdges d)) := Quotient (pairingSetoid p)
abbrev EncodedCoreVertexAddresses {d : Fin b → ℕ} (p : PairingMap (EncodedCoreHalfEdges d))
    (L : EncodedCorePaths p → ℕ) := Fin b ⊕ (Σ c : EncodedCorePaths p, Fin (L c - 1))

noncomputable def encodedDepartureAddress {d : Fin b → ℕ} (p : PairingMap (EncodedCoreHalfEdges d))
    (L : EncodedCorePaths p → ℕ) (c : EncodedCorePaths p) (i : Fin (L c)) :
    EncodedCoreVertexAddresses p L :=
  if hz : i.val=0 then .inl (Quotient.out c).1 else .inr ⟨c,⟨i.val-1, by have h := i.isLt; omega⟩⟩

noncomputable def encodedArrivalAddress {d : Fin b → ℕ} (p : PairingMap (EncodedCoreHalfEdges d))
    (L : EncodedCorePaths p → ℕ) (c : EncodedCorePaths p) (i : Fin (L c)) :
    EncodedCoreVertexAddresses p L :=
  if hz : i.val+1=L c then .inl (p.val (Quotient.out c)).1
    else .inr ⟨c,⟨i.val, by have h := i.isLt; omega⟩⟩

noncomputable def encodedDepartureSide {d : Fin b → ℕ} (colors : Fin b → Bool)
    (p : PairingMap (EncodedCoreHalfEdges d)) (c : EncodedCorePaths p) (k : ℕ) : Bool :=
  chainEndpointOrientation k (colors (Quotient.out c).1)

noncomputable def encodedHalfEdgeAddress {κ : Type*} {d : Fin b → ℕ} (colors : Fin b → Bool)
    (p : PairingMap (EncodedCoreHalfEdges d)) (L : EncodedCorePaths p → ℕ)
    (a : (Σ c : EncodedCorePaths p, Fin (L c)) ≃ κ) (s : Bool) (edge : κ) :
    EncodedCoreVertexAddresses p L :=
  let x := a.symm edge
  if s=encodedDepartureSide colors p x.1 x.2.val
    then encodedDepartureAddress p L x.1 x.2 else encodedArrivalAddress p L x.1 x.2

noncomputable def decodedCorePartition {κ : Type*} {d : Fin b → ℕ} (colors : Fin b → Bool)
    (p : PairingMap (EncodedCoreHalfEdges d)) (L : EncodedCorePaths p → ℕ)
    (a : (Σ c : EncodedCorePaths p, Fin (L c)) ≃ κ) (s : Bool) : Setoid κ :=
  Setoid.ker (encodedHalfEdgeAddress colors p L a s)

def halfEdgeAtSide {κ : Type*} (s : Bool) (edge : κ) : PartitionHalfEdges (κ := κ) :=
  if s then .inr edge else .inl edge

theorem halfEdgeAtSide_side_original {κ : Type*} (x : PartitionHalfEdges (κ := κ)) :
    halfEdgeAtSide (partitionHalfEdgeSide x) (Sum.elim id id x) = x := by cases x <;> rfl

theorem halfEdgeAtSide_departure_cases {κ : Type*} (x : PartitionHalfEdges (κ := κ)) (s : Bool) :
    halfEdgeAtSide s (Sum.elim id id x) =
      if s=partitionHalfEdgeSide (partitionHalfEdgeFlip x) then partitionHalfEdgeFlip x else x := by
  cases x <;> cases s <;> rfl

variable {κ : Type*} [Fintype κ]

theorem decoratedCoreColor_halfEdgeSide (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) (x : DecoratedCoreHalfEdges P Q d) :
    decoratedCoreColor P Q d x.1 = partitionHalfEdgeSide (decoratedHalfEdgeEquiv P Q d hP hQ x).val := by
  rw [← partitionHalfEdgeSide_vertex P Q, decoratedHalfEdgeEquiv_vertex]
  unfold decoratedCoreColor
  cases (d.1 x.1).val <;> rfl

theorem decoratedPathArrival_departure_side (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (c : DecoratedCompressedPaths P Q d hP hQ) (i : Fin (decoratedPathLength P Q d hP hQ c)) :
    partitionHalfEdgeSide (partitionHalfEdgeFlip (decoratedPathArrival P Q d hP hQ c i)) =
      encodedDepartureSide (decoratedCoreColor P Q d) (decoratedCompressedPairing P Q d hP hQ) c i.val := by
  unfold decoratedPathArrival
  rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, partitionHalfEdgeFlip_involutive]
  rw [partitionHalfEdgeSide_splice, partitionHalfEdgeSide_path_pow]
  unfold encodedDepartureSide
  rw [decoratedCoreColor_halfEdgeSide P Q d hP hQ (Quotient.out c)]
  rfl

theorem encodedHalfEdgeAddress_actual_vertex (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) (s : Bool) (edge : κ) :
    decoratedGraphVertexEquiv P Q d hP hQ hc
      (encodedHalfEdgeAddress (decoratedCoreColor P Q d) (decoratedCompressedPairing P Q d hP hQ)
        (decoratedPathLength P Q d hP hQ) (decoratedPathEdgeAssignment P Q d hP hQ hc) s edge) =
      partitionHalfEdgeVertex P Q (halfEdgeAtSide s edge) := by
  obtain ⟨⟨c,i⟩,rfl⟩ := (decoratedPathEdgeAssignment P Q d hP hQ hc).surjective edge
  unfold encodedHalfEdgeAddress
  rw [Equiv.symm_apply_apply]
  dsimp only
  rw [decoratedPathEdgeAssignment_reading, halfEdgeAtSide_departure_cases,
    decoratedPathArrival_departure_side]
  split_ifs
  · exact decoratedDepartureAddress_vertex P Q d hP hQ hc c i
  · exact decoratedArrivalAddress_vertex P Q d hP hQ hc c i

theorem decodedCorePartition_left (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    decodedCorePartition (decoratedCoreColor P Q d) (decoratedCompressedPairing P Q d hP hQ)
      (decoratedPathLength P Q d hP hQ) (decoratedPathEdgeAssignment P Q d hP hQ hc) false = P := by
  apply Setoid.ext
  intro x y
  change (_ = _) ↔ P.r x y
  rw [← (decoratedGraphVertexEquiv P Q d hP hQ hc).injective.eq_iff,
    encodedHalfEdgeAddress_actual_vertex, encodedHalfEdgeAddress_actual_vertex]
  change Sum.inl (Quotient.mk P x) = Sum.inl (Quotient.mk P y) ↔ P.r x y
  rw [Sum.inl.injEq]
  exact Quotient.eq_iff_equiv

theorem decodedCorePartition_right (P Q : Setoid κ) (d : HighVertexDecorations P Q)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    decodedCorePartition (decoratedCoreColor P Q d) (decoratedCompressedPairing P Q d hP hQ)
      (decoratedPathLength P Q d hP hQ) (decoratedPathEdgeAssignment P Q d hP hQ hc) true = Q := by
  apply Setoid.ext
  intro x y
  change (_ = _) ↔ Q.r x y
  rw [← (decoratedGraphVertexEquiv P Q d hP hQ hc).injective.eq_iff,
    encodedHalfEdgeAddress_actual_vertex, encodedHalfEdgeAddress_actual_vertex]
  change Sum.inr (Quotient.mk Q x) = Sum.inr (Quotient.mk Q y) ↔ Q.r x y
  rw [Sum.inr.injEq]
  exact Quotient.eq_iff_equiv

end TournamentHamiltonian
