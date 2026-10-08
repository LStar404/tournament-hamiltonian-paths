import TournamentHamiltonian.CoreCompressionInvolutions
import TournamentHamiltonian.GaussianCoreExcessCoefficients

/-! Canonical degree-two continuation on the actual partition graph half-edges. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

private theorem degreeTwoPartner_exists (P : Setoid κ) (x : κ)
    (hx : (partitionClass P x).card = 2) :
    ∃ y, (partitionClass P x).erase x = {y} := by
  apply Finset.card_eq_one.mp
  rw [Finset.card_erase_of_mem (by simp [partitionClass]), hx]

noncomputable def degreeTwoPartner (P : Setoid κ) (x : κ)
    (hx : (partitionClass P x).card = 2) : κ :=
  Classical.choose (degreeTwoPartner_exists P x hx)

theorem degreeTwoPartner_spec (P : Setoid κ) (x : κ)
    (hx : (partitionClass P x).card = 2) :
    P x (degreeTwoPartner P x hx) ∧ degreeTwoPartner P x hx ≠ x ∧
      ∀ z, P x z → z = x ∨ z = degreeTwoPartner P x hx := by
  have he : (partitionClass P x).erase x = {degreeTwoPartner P x hx} :=
    Classical.choose_spec (degreeTwoPartner_exists P x hx)
  have hm : degreeTwoPartner P x hx ∈ (partitionClass P x).erase x := by rw [he]; simp
  refine ⟨(Finset.mem_filter.mp (Finset.mem_erase.mp hm).2).2, (Finset.mem_erase.mp hm).1, ?_⟩
  intro z hz
  by_cases hn : z = x
  · exact Or.inl hn
  · right
    have hm : z ∈ (partitionClass P x).erase x := by simp [partitionClass, hn, hz]
    rw [he] at hm
    exact Finset.mem_singleton.mp hm

omit [DecidableEq κ] in
theorem partitionClass_eq_of_related (P : Setoid κ) {x y : κ} (hxy : P x y) :
    partitionClass P x = partitionClass P y := by
  ext z
  simp only [partitionClass, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hx => P.trans (P.symm hxy) hx, fun hy => P.trans hxy hy⟩

noncomputable def degreeTwoSplice (P : Setoid κ) (x : κ) : κ :=
  if hx : (partitionClass P x).card = 2 then degreeTwoPartner P x hx else x

theorem degreeTwoSplice_related (P : Setoid κ) (x : κ) : P x (degreeTwoSplice P x) := by
  unfold degreeTwoSplice
  split_ifs with hx
  · exact (degreeTwoPartner_spec P x hx).1
  · exact P.refl x

theorem degreeTwoSplice_fixed_iff (P : Setoid κ) (x : κ) :
    degreeTwoSplice P x = x ↔ (partitionClass P x).card ≠ 2 := by
  unfold degreeTwoSplice
  split_ifs with hx
  · simp [(degreeTwoPartner_spec P x hx).2.1, hx]
  · simp [hx]

theorem degreeTwoSplice_involutive (P : Setoid κ) : Function.Involutive (degreeTwoSplice P) := by
  intro x
  by_cases hx : (partitionClass P x).card = 2
  · have hp := degreeTwoPartner_spec P x hx
    have hy : (partitionClass P (degreeTwoPartner P x hx)).card = 2 := by
      rw [← partitionClass_eq_of_related P hp.1]
      exact hx
    simp only [degreeTwoSplice, dite_eq_left hx, dite_eq_left hy]
    have hh := (degreeTwoPartner_spec P (degreeTwoPartner P x hx) hy).2.2 x (P.symm hp.1)
    rcases hh with hh | hh
    · exact (hp.2.1 hh.symm).elim
    · exact hh.symm
  · simp only [degreeTwoSplice, dite_eq_right hx]

abbrev PartitionHalfEdges := κ ⊕ κ

noncomputable def partitionHalfEdgeVertex (P Q : Setoid κ) :
    PartitionHalfEdges (κ := κ) → PartitionGraphVertices P Q :=
  Sum.map (Quotient.mk P) (Quotient.mk Q)

noncomputable def partitionHalfEdgeSplice (P Q : Setoid κ) : Equiv.Perm (PartitionHalfEdges (κ := κ)) :=
  (degreeTwoSplice_involutive (sumPartition P Q)).toPerm _

def partitionHalfEdgeFlip : Equiv.Perm (PartitionHalfEdges (κ := κ)) := Equiv.sumComm κ κ

omit [Fintype κ] [DecidableEq κ] in
theorem partitionHalfEdgeFlip_involutive :
    Function.Involutive (partitionHalfEdgeFlip (κ := κ)) := by
  intro x
  cases x <;> rfl

omit [Fintype κ] [DecidableEq κ] in
theorem partitionHalfEdgeFlip_ne (x : PartitionHalfEdges (κ := κ)) :
    partitionHalfEdgeFlip x ≠ x := by
  cases x <;> simp [partitionHalfEdgeFlip]

theorem partitionHalfEdgeSplice_involutive (P Q : Setoid κ) :
    Function.Involutive (partitionHalfEdgeSplice P Q) := degreeTwoSplice_involutive _

theorem partitionClass_sum_left (P Q : Setoid κ) (x : κ) :
    partitionClass (sumPartition P Q) (.inl x) = (partitionClass P x).image Sum.inl := by
  ext z
  cases z <;> simp [partitionClass] <;> first | exact Iff.rfl | exact not_false

theorem partitionClass_sum_right (P Q : Setoid κ) (x : κ) :
    partitionClass (sumPartition P Q) (.inr x) = (partitionClass Q x).image Sum.inr := by
  ext z
  cases z <;> simp [partitionClass] <;> first | exact Iff.rfl | exact not_false

theorem partitionHalfEdge_class_card (P Q : Setoid κ) (x : PartitionHalfEdges (κ := κ)) :
    (partitionClass (sumPartition P Q) x).card =
      partitionGraphDegree P Q (partitionHalfEdgeVertex P Q x) := by
  cases x with
  | inl x =>
      rw [partitionClass_sum_left, Finset.card_image_of_injective _ Sum.inl_injective,
        partitionClass_card, partitionBlock_card_eq_degree]
      rfl
  | inr x =>
      rw [partitionClass_sum_right, Finset.card_image_of_injective _ Sum.inr_injective,
        partitionClass_card, partitionBlock_card_eq_degree]
      rfl

theorem partitionHalfEdgeSplice_vertex (P Q : Setoid κ) (x : PartitionHalfEdges (κ := κ)) :
    partitionHalfEdgeVertex P Q (partitionHalfEdgeSplice P Q x) = partitionHalfEdgeVertex P Q x := by
  have hr := degreeTwoSplice_related (sumPartition P Q) x
  change sumPartition P Q x (partitionHalfEdgeSplice P Q x) at hr
  generalize hy : partitionHalfEdgeSplice P Q x = y at *
  cases x <;> cases y
  · exact congrArg Sum.inl (Quotient.sound ((P.symm hr)))
  · exact hr.elim
  · exact hr.elim
  · exact congrArg Sum.inr (Quotient.sound ((Q.symm hr)))

theorem partitionHalfEdgeSplice_fixed_iff (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (x : PartitionHalfEdges (κ := κ)) :
    partitionHalfEdgeSplice P Q x = x ↔
      3 ≤ partitionGraphDegree P Q (partitionHalfEdgeVertex P Q x) := by
  change degreeTwoSplice (sumPartition P Q) x = x ↔ _
  rw [degreeTwoSplice_fixed_iff, partitionHalfEdge_class_card]
  have h2 := partitionGraphDegree_ge_two P Q hP hQ (partitionHalfEdgeVertex P Q x)
  omega

noncomputable def partitionCoreTerminalPairing (P Q : Setoid κ) :
    PairingMap (TerminalHalfEdges (partitionHalfEdgeSplice P Q)) :=
  terminalPairingMap partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q)
    partitionHalfEdgeFlip_involutive (partitionHalfEdgeSplice_involutive P Q) partitionHalfEdgeFlip_ne

noncomputable def highIncidentBlockEquiv (P : Setoid κ) :
    {x : κ // 3 ≤ coordinatePartitionDegree P (Quotient.mk P x)} ≃
      Σ v : {v : Quotient P // 3 ≤ coordinatePartitionDegree P v}, PartitionBlock P v.val where
  toFun x := ⟨⟨Quotient.mk P x.val, x.property⟩, ⟨x.val, rfl⟩⟩
  invFun v := ⟨v.2.val, by rw [v.2.property]; exact v.1.property⟩
  left_inv _ := rfl
  right_inv v := by
    rcases v with ⟨⟨v, hv⟩, ⟨x, hx⟩⟩
    dsimp at hx
    cases hx
    rfl

omit [DecidableEq κ] in
theorem coordinateDegree_high_incidence_card (P : Setoid κ) :
    Fintype.card {x : κ // 3 ≤ coordinatePartitionDegree P (Quotient.mk P x)} =
      ∑ v : Quotient P, if 3 ≤ coordinatePartitionDegree P v then coordinatePartitionDegree P v else 0 := by
  rw [Fintype.card_congr (highIncidentBlockEquiv P), Fintype.card_sigma]
  simp_rw [partitionBlock_card_eq_degree]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun v : Quotient P => 3 ≤ coordinatePartitionDegree P v))
    (by simp) (coordinatePartitionDegree P)]
  exact Finset.sum_filter _ _

theorem partitionCoreTerminal_card (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    Fintype.card (TerminalHalfEdges (partitionHalfEdgeSplice P Q)) =
      2 * ((highDegreeVertices P Q).card + partitionGraphExcess P Q) := by
  let e : TerminalHalfEdges (partitionHalfEdgeSplice P Q) ≃
      {x : PartitionHalfEdges (κ := κ) //
        3 ≤ partitionGraphDegree P Q (partitionHalfEdgeVertex P Q x)} :=
    Equiv.subtypeEquivRight (partitionHalfEdgeSplice_fixed_iff P Q hP hQ)
  rw [Fintype.card_congr e, Fintype.card_congr (Equiv.subtypeSum), Fintype.card_sum]
  change Fintype.card {x : κ // 3 ≤ coordinatePartitionDegree P (Quotient.mk P x)} +
    Fintype.card {x : κ // 3 ≤ coordinatePartitionDegree Q (Quotient.mk Q x)} = _
  rw [coordinateDegree_high_incidence_card, coordinateDegree_high_incidence_card]
  rw [← highDegreeVertices_degree_sum P Q hP hQ]
  rw [highDegreeVertices, Finset.sum_filter, Fintype.sum_sum_type]
  rfl

noncomputable def actualCompressedPairPartition (P Q : Setoid κ) :
    Setoid (TerminalHalfEdges (partitionHalfEdgeSplice P Q)) :=
  pairingSetoid (partitionCoreTerminalPairing P Q)

theorem actualCompressedPairPartition_pairing (P Q : Setoid κ) :
    IsPairingPartition (actualCompressedPairPartition P Q) := pairingSetoid_isPairing _

/-- The constructed terminal pairing realizes the required compressed edge count. -/
theorem actualCompressedPairPartition_card (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    Fintype.card (Quotient (actualCompressedPairPartition P Q)) =
      (highDegreeVertices P Q).card + partitionGraphExcess P Q := by
  have hs := coordinatePartitionDegree_sum (actualCompressedPairPartition P Q)
  have hd : ∀ v : Quotient (actualCompressedPairPartition P Q),
      coordinatePartitionDegree (actualCompressedPairPartition P Q) v = 2 := by
    intro v
    rw [← partitionBlock_card_eq_degree]
    exact actualCompressedPairPartition_pairing P Q v
  simp_rw [hd] at hs
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  rw [partitionCoreTerminal_card P Q hP hQ] at hs
  omega

theorem partitionCoreTerminal_pairings_card (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    Fintype.card (PairingMap (TerminalHalfEdges (partitionHalfEdgeSplice P Q))) =
      (2 * ((highDegreeVertices P Q).card + partitionGraphExcess P Q) - 1).doubleFactorial := by
  rw [pairingMap_card_eq_doubleFactorial, partitionCoreTerminal_card P Q hP hQ]
  simp

end TournamentHamiltonian
