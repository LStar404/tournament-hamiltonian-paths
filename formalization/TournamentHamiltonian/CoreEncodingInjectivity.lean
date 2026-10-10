import TournamentHamiltonian.CoreEncodingTerminals
import TournamentHamiltonian.CoreEncodingData

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ]

abbrev DecoratedCenteredCore :=
  Σ c : CenteredCorePartitionPair κ, HighVertexDecorations c.val.val.1 c.val.val.2

noncomputable def actualCoreEncodingData (c : CenteredCorePartitionPair κ)
    (d : HighVertexDecorations c.val.val.1 c.val.val.2) :
    EncodedCoreData κ (partitionGraphExcess c.val.val.1 c.val.val.2)
      (Fintype.card (HighGraphVertices c.val.val.1 c.val.val.2)) where
  degree := ⟨decoratedCoreDegree _ _ d, decoratedCoreDegree_mem _ _ d c.property.1 c.property.2⟩
  colors := decoratedCoreColor _ _ d
  pairing := decoratedCompressedPairing _ _ d c.property.1 c.property.2
  lengths p := ⟨decoratedPathLength _ _ d c.property.1 c.property.2 p, by
    apply Nat.lt_succ_iff.mpr
    calc
      _ ≤ ∑ q : DecoratedCompressedPaths _ _ d c.property.1 c.property.2,
          decoratedPathLength _ _ d c.property.1 c.property.2 q :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
      _ = _ := decoratedPathLength_sum _ _ d c.property.1 c.property.2 c.val.property⟩
  positive := decoratedPathLength_pos _ _ d c.property.1 c.property.2
  total := decoratedPathLength_sum _ _ d c.property.1 c.property.2 c.val.property
  assignment := decoratedPathEdgeAssignment _ _ d c.property.1 c.property.2 c.val.property

abbrev PackedCoreEncoding := Σ j : ℕ, Σ b : ℕ, EncodedCoreData κ j b

noncomputable def actualPackedCoreEncoding (x : DecoratedCenteredCore (κ := κ)) :
    PackedCoreEncoding (κ := κ) :=
  ⟨partitionGraphExcess x.1.val.val.1 x.1.val.val.2,
    Fintype.card (HighGraphVertices x.1.val.val.1 x.1.val.val.2), actualCoreEncodingData x.1 x.2⟩

noncomputable def encodedCoreDataPartition {j b : ℕ} (x : EncodedCoreData κ j b) (s : Bool) : Setoid κ :=
  decodedCorePartition x.colors x.pairing (fun c => (x.lengths c).val) x.assignment s

noncomputable def packedCoreEncodingPartition (x : PackedCoreEncoding (κ := κ)) (s : Bool) : Setoid κ :=
  encodedCoreDataPartition x.2.2 s

theorem actualPackedCoreEncoding_left (x : DecoratedCenteredCore (κ := κ)) :
    packedCoreEncodingPartition (actualPackedCoreEncoding x) false = x.1.val.val.1 :=
  decodedCorePartition_left _ _ x.2 x.1.property.1 x.1.property.2 x.1.val.property

theorem actualPackedCoreEncoding_right (x : DecoratedCenteredCore (κ := κ)) :
    packedCoreEncodingPartition (actualPackedCoreEncoding x) true = x.1.val.val.2 :=
  decodedCorePartition_right _ _ x.2 x.1.property.1 x.1.property.2 x.1.val.property

noncomputable def encodedCoreTerminalLookup {j b : ℕ} (x : EncodedCoreData κ j b) (i : Fin b) (k : ℕ) :
    Option (PartitionHalfEdges (κ := κ)) :=
  if hk : k<x.degree.val i then some (encodedTerminalHalfEdge x.colors x.pairing
    (fun c => (x.lengths c).val) x.positive x.assignment ⟨i,⟨k,hk⟩⟩) else none

theorem actualCoreEncodingData_terminal_lookup (c : CenteredCorePartitionPair κ)
    (d : HighVertexDecorations c.val.val.1 c.val.val.2)
    (i : Fin (Fintype.card (HighGraphVertices c.val.val.1 c.val.val.2))) (k : ℕ)
    (hk : k<decoratedCoreDegree c.val.val.1 c.val.val.2 d i) :
    encodedCoreTerminalLookup (actualCoreEncodingData c d) i k =
      some (decoratedHalfEdgeEquiv _ _ d c.property.1 c.property.2 ⟨i,⟨k,hk⟩⟩).val := by
  unfold encodedCoreTerminalLookup
  dsimp only [actualCoreEncodingData]
  rw [dite_eq_left hk]
  exact congrArg some (encodedTerminalHalfEdge_actual _ _ d c.property.1 c.property.2 c.val.property _)

theorem actualPackedCoreEncoding_injective :
    Function.Injective (actualPackedCoreEncoding (κ := κ)) := by
  rintro ⟨c,d⟩ ⟨e,f⟩ h
  have hP := congrArg (fun x : PackedCoreEncoding (κ := κ) => packedCoreEncodingPartition x false) h
  have hQ := congrArg (fun x : PackedCoreEncoding (κ := κ) => packedCoreEncodingPartition x true) h
  rw [actualPackedCoreEncoding_left, actualPackedCoreEncoding_left] at hP
  rw [actualPackedCoreEncoding_right, actualPackedCoreEncoding_right] at hQ
  have hce : c=e := Subtype.ext (Subtype.ext (Prod.ext hP hQ))
  subst e
  have hdata : actualCoreEncodingData c d = actualCoreEncodingData c f :=
    eq_of_heq (Sigma.mk.inj_iff.mp (eq_of_heq (Sigma.mk.inj_iff.mp h).2)).2
  have hdf : d=f := decoratedHalfEdgeEquiv_injective_decorations _ _ c.property.1 c.property.2 d f (by
    intro i k hd hf
    have ht := congrArg (fun x => encodedCoreTerminalLookup x i k) hdata
    rw [actualCoreEncodingData_terminal_lookup c d i k hd,
      actualCoreEncodingData_terminal_lookup c f i k hf] at ht
    exact Option.some.inj ht)
  subst f
  rfl

noncomputable def actualCoreFiberEncoding {j b : ℕ} (x : DecoratedCoreOfExcessAndHigh κ j b) :
    EncodedCoreData κ j b :=
  cast (congrArg₂ (EncodedCoreData κ) x.1.property.1 x.1.property.2)
    (actualCoreEncodingData x.1.val x.2)

theorem actualCoreFiberEncoding_packed {j b : ℕ} (x : DecoratedCoreOfExcessAndHigh κ j b) :
    (⟨j,b,actualCoreFiberEncoding x⟩ : PackedCoreEncoding (κ := κ)) =
      actualPackedCoreEncoding ⟨x.1.val,x.2⟩ := by
  rcases x with ⟨⟨c,hex,hb⟩,d⟩
  subst j
  subst b
  rfl

theorem actualCoreFiberEncoding_injective (j b : ℕ) :
    Function.Injective (actualCoreFiberEncoding (κ := κ) (j := j) (b := b)) := by
  rintro ⟨c,d⟩ ⟨e,f⟩ h
  have hp := congrArg (fun z : EncodedCoreData κ j b =>
    (⟨j,b,z⟩ : PackedCoreEncoding (κ := κ))) h
  rw [actualCoreFiberEncoding_packed,actualCoreFiberEncoding_packed] at hp
  have hs := actualPackedCoreEncoding_injective hp
  have hce : c=e := Subtype.ext (congrArg Sigma.fst hs)
  subst e
  have hdf : d=f := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  subst f
  rfl

theorem actualCoreEncodingData_weight (n : ℕ) (C q R : ℝ) (c : CenteredCorePartitionPair κ)
    (d : HighVertexDecorations c.val.val.1 c.val.val.2) :
    encodedCorePathWeight n C q R (actualCoreEncodingData c d) =
      (∏ p : ActualCompressedPaths c.val.val.1 c.val.val.2,
        positiveChainWeight C q R (compressedPathLength c.val.val.1 c.val.val.2 p - 1)) /
        ((Fintype.card (HighGraphVertices c.val.val.1 c.val.val.2)).factorial *
          (∏ v : HighGraphVertices c.val.val.1 c.val.val.2,
            (partitionGraphDegree c.val.val.1 c.val.val.2 v.val : ℝ)) *
          (n : ℝ) ^ partitionGraphExcess c.val.val.1 c.val.val.2) := by
  unfold encodedCorePathWeight
  have hp : (∏ p : Quotient (pairingSetoid (actualCoreEncodingData c d).pairing),
      positiveChainWeight C q R (((actualCoreEncodingData c d).lengths p).val - 1)) =
      ∏ p : ActualCompressedPaths c.val.val.1 c.val.val.2,
        positiveChainWeight C q R (compressedPathLength _ _ p - 1) := by
    apply Fintype.prod_equiv (decoratedCompressedPathEquiv _ _ d c.property.1 c.property.2)
    intro p
    rfl
  have hd : (∏ i, (decoratedCoreDegree c.val.val.1 c.val.val.2 d i : ℝ)) =
      ∏ v : HighGraphVertices c.val.val.1 c.val.val.2,
        (partitionGraphDegree _ _ v.val : ℝ) := by
    unfold decoratedCoreDegree
    simp_rw [highIncidentHalfEdges_card]
    exact Fintype.prod_equiv d.1 _ _ (fun _ => rfl)
  rw [hp]
  change _ / (_ * (∏ i, (decoratedCoreDegree _ _ d i : ℝ)) * _) = _
  rw [hd]

theorem actualCoreFiberEncoding_weight (n : ℕ) (C q R : ℝ) {j b : ℕ}
    (x : DecoratedCoreOfExcessAndHigh κ j b) :
    encodedCorePathWeight n C q R (actualCoreFiberEncoding x) =
      (∏ p : ActualCompressedPaths x.1.val.val.val.1 x.1.val.val.val.2,
        positiveChainWeight C q R (compressedPathLength x.1.val.val.val.1 x.1.val.val.val.2 p - 1)) /
        ((b.factorial : ℝ) *
          (∏ v : HighGraphVertices x.1.val.val.val.1 x.1.val.val.val.2,
            (partitionGraphDegree x.1.val.val.val.1 x.1.val.val.val.2 v.val : ℝ)) * (n : ℝ)^j) := by
  rcases x with ⟨⟨c,hex,hb⟩,d⟩
  subst j
  subst b
  exact actualCoreEncodingData_weight n C q R c d

theorem decoratedCorePathMass_le_encoded (n : ℕ) (C q R : ℝ) (j b : ℕ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hR : 0 ≤ R) :
    decoratedCorePathMass (κ := κ) n C q R j b ≤
      ∑ x : EncodedCoreData κ j b, encodedCorePathWeight n C q R x := by
  unfold decoratedCorePathMass
  simp_rw [← actualCoreFiberEncoding_weight]
  calc
    _ = ∑ x ∈ Finset.univ.image (actualCoreFiberEncoding (κ := κ) (j := j) (b := b)),
        encodedCorePathWeight n C q R x :=
      (Finset.sum_image (actualCoreFiberEncoding_injective j b).injOn).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => encodedCorePathWeight_nonneg n C q R x hC hq hR)

end TournamentHamiltonian
