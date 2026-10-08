import TournamentHamiltonian.GaussianCoreComponents

/-! Actual high-degree vertex counts and degree balances preceding core compression. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

abbrev PartitionGraphVertices (P Q : Setoid κ) := Quotient P ⊕ Quotient Q

noncomputable def partitionGraphDegree (P Q : Setoid κ) : PartitionGraphVertices P Q → ℕ
  | .inl v => coordinatePartitionDegree P v
  | .inr v => coordinatePartitionDegree Q v

noncomputable def partitionGraphExcess (P Q : Setoid κ) : ℕ :=
  Fintype.card κ - Fintype.card (PartitionGraphVertices P Q)

noncomputable def highDegreeVertices (P Q : Setoid κ) : Finset (PartitionGraphVertices P Q) :=
  Finset.univ.filter (fun v => 3 ≤ partitionGraphDegree P Q v)

omit [DecidableEq κ] in
theorem partitionGraphDegree_sum (P Q : Setoid κ) :
    (∑ v : PartitionGraphVertices P Q, partitionGraphDegree P Q v) = 2 * Fintype.card κ := by
  rw [Fintype.sum_sum_type]
  simp only [partitionGraphDegree, coordinatePartitionDegree_sum]
  omega

theorem partitionGraphDegree_ge_two (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) (v : PartitionGraphVertices P Q) :
    2 ≤ partitionGraphDegree P Q v := by
  cases v with
  | inl v => exact singletonFree_coordinateDegree_ge_two P hP v
  | inr v => exact singletonFree_coordinateDegree_ge_two Q hQ v

theorem partitionGraph_vertex_count_le (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    Fintype.card (PartitionGraphVertices P Q) ≤ Fintype.card κ := by
  have hp := singletonFree_partition_vertex_bound P hP
  have hq := singletonFree_partition_vertex_bound Q hQ
  rw [Fintype.card_sum]
  omega

/-- The actual sum of the excess degrees is twice the graph excess. -/
theorem partitionGraph_excess_degree_sum (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    (∑ v : PartitionGraphVertices P Q, (partitionGraphDegree P Q v - 2)) =
      2 * partitionGraphExcess P Q := by
  rw [Finset.sum_tsub_distrib _ (fun v _ => partitionGraphDegree_ge_two P Q hP hQ v),
    partitionGraphDegree_sum]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, partitionGraphExcess]
  omega

/-- There are at most `2j` high-degree vertices; this follows from actual partition degrees. -/
theorem highDegreeVertices_card_le (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    (highDegreeVertices P Q).card ≤ 2 * partitionGraphExcess P Q := by
  rw [Finset.card_eq_sum_ones, highDegreeVertices, Finset.sum_filter]
  rw [← partitionGraph_excess_degree_sum P Q hP hQ]
  apply Finset.sum_le_sum
  intro v _
  split_ifs with hv <;> omega

theorem highDegreeVertices_nonempty (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hpair : ¬ (IsPairingPartition P ∧ IsPairingPartition Q)) :
    (highDegreeVertices P Q).Nonempty := by
  by_contra hn
  have he : highDegreeVertices P Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hd : ∀ v, partitionGraphDegree P Q v = 2 := by
    intro v
    have h2 := partitionGraphDegree_ge_two P Q hP hQ v
    have h3 : ¬ 3 ≤ partitionGraphDegree P Q v := by
      intro h3
      have hv : v ∈ highDegreeVertices P Q := by simp [highDegreeVertices, h3]
      rw [he] at hv
      simp at hv
    omega
  apply hpair
  constructor
  · intro v
    rw [partitionBlock_card_eq_degree]
    exact hd (.inl v)
  · intro v
    rw [partitionBlock_card_eq_degree]
    exact hd (.inr v)

theorem highDegreeVertices_card_pos (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hpair : ¬ (IsPairingPartition P ∧ IsPairingPartition Q)) :
    1 ≤ (highDegreeVertices P Q).card := by
  exact (Finset.card_pos.mpr (highDegreeVertices_nonempty P Q hP hQ hpair))

theorem highDegreeVertices_excess_sum (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    (∑ v ∈ highDegreeVertices P Q, (partitionGraphDegree P Q v - 2)) =
      2 * partitionGraphExcess P Q := by
  rw [← partitionGraph_excess_degree_sum P Q hP hQ]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v _ hv
  have h2 := partitionGraphDegree_ge_two P Q hP hQ v
  have h3 : ¬ 3 ≤ partitionGraphDegree P Q v := by simpa [highDegreeVertices] using hv
  omega

/-- The number of incident high-degree half-edges is exactly `2(b+j)`. -/
theorem highDegreeVertices_degree_sum (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    (∑ v ∈ highDegreeVertices P Q, partitionGraphDegree P Q v) =
      2 * ((highDegreeVertices P Q).card + partitionGraphExcess P Q) := by
  have he := highDegreeVertices_excess_sum P Q hP hQ
  rw [Finset.sum_tsub_distrib _ (fun v _ => partitionGraphDegree_ge_two P Q hP hQ v)] at he
  have hs : 2 * (highDegreeVertices P Q).card ≤
      ∑ v ∈ highDegreeVertices P Q, partitionGraphDegree P Q v := by
    have h := Finset.sum_le_sum (s := highDegreeVertices P Q)
      (fun v _ => partitionGraphDegree_ge_two P Q hP hQ v)
    simpa [mul_comm] using h
  simp only [Finset.sum_const, smul_eq_mul] at he
  omega

/-- The finite half-edge count that compression must realize as its edge count. -/
noncomputable def compressedHalfEdgeCount (P Q : Setoid κ) : ℕ :=
  (∑ v ∈ highDegreeVertices P Q, partitionGraphDegree P Q v) / 2

theorem compressedHalfEdgeCount_eq (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    compressedHalfEdgeCount P Q = (highDegreeVertices P Q).card + partitionGraphExcess P Q := by
  rw [compressedHalfEdgeCount, highDegreeVertices_degree_sum P Q hP hQ]
  omega

theorem compressedHalfEdgeCount_le (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    compressedHalfEdgeCount P Q ≤ 3 * partitionGraphExcess P Q := by
  rw [compressedHalfEdgeCount_eq P Q hP hQ]
  have h := highDegreeVertices_card_le P Q hP hQ
  omega

end TournamentHamiltonian
