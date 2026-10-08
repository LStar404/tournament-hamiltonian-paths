import TournamentHamiltonian.PartitionHalfEdges
import Mathlib.Data.Fintype.Perm

/-! Actual Möbius weights and finite decoration fibers at the high-degree vertices. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem partition_mu_abs_degree_weights (P : Setoid κ) :
    |IncidenceAlgebra.mu ℝ (⊥ : Setoid κ) P| =
      ∏ v : Quotient P, ((coordinatePartitionDegree P v - 1).factorial : ℝ) := by
  rw [partition_mu_degree_weights κ P, Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro v _
  rw [abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg (Nat.cast_nonneg _)]

theorem partition_mu_product_abs_high (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    |IncidenceAlgebra.mu ℝ (⊥ : Setoid κ) P * IncidenceAlgebra.mu ℝ ⊥ Q| =
      ∏ v ∈ highDegreeVertices P Q, ((partitionGraphDegree P Q v - 1).factorial : ℝ) := by
  rw [abs_mul, partition_mu_abs_degree_weights, partition_mu_abs_degree_weights]
  have hsum : (∏ v : PartitionGraphVertices P Q, ((partitionGraphDegree P Q v - 1).factorial : ℝ)) =
      (∏ v : Quotient P, ((coordinatePartitionDegree P v - 1).factorial : ℝ)) *
      (∏ v : Quotient Q, ((coordinatePartitionDegree Q v - 1).factorial : ℝ)) := by
    rw [Fintype.prod_sum_type]
    rfl
  rw [← hsum]
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro v _ hv
  have h2 := partitionGraphDegree_ge_two P Q hP hQ v
  have h3 : ¬ 3 ≤ partitionGraphDegree P Q v := by simpa [highDegreeVertices] using hv
  have hd : partitionGraphDegree P Q v = 2 := by omega
  simp [hd]

abbrev HighGraphVertices (P Q : Setoid κ) :=
  {v : PartitionGraphVertices P Q // 3 ≤ partitionGraphDegree P Q v}

abbrev HighIncidentHalfEdges (P Q : Setoid κ) (v : HighGraphVertices P Q) :=
  {x : PartitionHalfEdges (κ := κ) // partitionHalfEdgeVertex P Q x = v.val}

abbrev HighVertexDecorations (P Q : Setoid κ) :=
  (Fin (Fintype.card (HighGraphVertices P Q)) ≃ HighGraphVertices P Q) ×
    (∀ v : HighGraphVertices P Q,
      Fin (Fintype.card (HighIncidentHalfEdges P Q v)) ≃ HighIncidentHalfEdges P Q v)

theorem highVertexDecorations_card (P Q : Setoid κ) :
    Fintype.card (HighVertexDecorations P Q) =
      (Fintype.card (HighGraphVertices P Q)).factorial *
        ∏ v : HighGraphVertices P Q, (Fintype.card (HighIncidentHalfEdges P Q v)).factorial := by
  unfold HighVertexDecorations
  rw [Fintype.card_prod, Fintype.card_pi]
  rw [Fintype.card_equiv (Fintype.equivFin _).symm, Fintype.card_fin]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [Fintype.card_equiv (Fintype.equivFin _).symm, Fintype.card_fin]

omit [DecidableEq κ] in
theorem highIncidentHalfEdges_card (P Q : Setoid κ) (v : HighGraphVertices P Q) :
    Fintype.card (HighIncidentHalfEdges P Q v) = partitionGraphDegree P Q v.val := by
  unfold HighIncidentHalfEdges
  rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
  have hzero : Fintype.card {x : κ // False} = 0 := by rw [Fintype.card_subtype]; simp
  rcases v with ⟨v, hv⟩
  cases v with
  | inl v =>
      simp only [partitionHalfEdgeVertex, Sum.map_inl, Sum.map_inr, Sum.inl.injEq,
        Sum.inr_ne_inl, hzero, add_zero, partitionGraphDegree]
      exact partitionBlock_card_eq_degree P v
  | inr v =>
      simp only [partitionHalfEdgeVertex, Sum.map_inl, Sum.map_inr, Sum.inr.injEq,
        Sum.inl_ne_inr, hzero, zero_add, partitionGraphDegree]
      exact partitionBlock_card_eq_degree Q v

theorem highVertexDecorations_card_degrees (P Q : Setoid κ) :
    Fintype.card (HighVertexDecorations P Q) =
      (Fintype.card (HighGraphVertices P Q)).factorial *
        ∏ v : HighGraphVertices P Q, (partitionGraphDegree P Q v.val).factorial := by
  rw [highVertexDecorations_card]
  simp_rw [highIncidentHalfEdges_card]

theorem partition_mu_product_abs_high_subtype (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    |IncidenceAlgebra.mu ℝ (⊥ : Setoid κ) P * IncidenceAlgebra.mu ℝ ⊥ Q| =
      ∏ v : HighGraphVertices P Q, ((partitionGraphDegree P Q v.val - 1).factorial : ℝ) := by
  rw [partition_mu_product_abs_high P Q hP hQ]
  exact Finset.prod_subtype (highDegreeVertices P Q) (by simp [highDegreeVertices]) _

theorem highVertexDecorations_card_real (P Q : Setoid κ) :
    (Fintype.card (HighVertexDecorations P Q) : ℝ) =
      ((Fintype.card (HighGraphVertices P Q)).factorial : ℝ) *
        ∏ v : HighGraphVertices P Q, ((partitionGraphDegree P Q v.val).factorial : ℝ) := by
  exact_mod_cast highVertexDecorations_card_degrees P Q

theorem highVertexDecoration_weight_identity (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    (Fintype.card (HighVertexDecorations P Q) : ℝ) =
      ((Fintype.card (HighGraphVertices P Q)).factorial : ℝ) *
        (∏ v : HighGraphVertices P Q, (partitionGraphDegree P Q v.val : ℝ)) *
        |IncidenceAlgebra.mu ℝ (⊥ : Setoid κ) P * IncidenceAlgebra.mu ℝ ⊥ Q| := by
  rw [highVertexDecorations_card_real, partition_mu_product_abs_high_subtype P Q hP hQ,
    mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  have hd : 0 < partitionGraphDegree P Q v.val := by have h := v.property; omega
  have hf := Nat.factorial_succ (partitionGraphDegree P Q v.val - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ partitionGraphDegree P Q v.val)] at hf
  exact_mod_cast hf

omit [DecidableEq κ] in
theorem partition_mu_product_abs_pos (P Q : Setoid κ) :
    0 < |IncidenceAlgebra.mu ℝ (⊥ : Setoid κ) P * IncidenceAlgebra.mu ℝ ⊥ Q| := by
  rw [abs_mul, partition_mu_abs_degree_weights, partition_mu_abs_degree_weights]
  apply mul_pos <;> apply Finset.prod_pos <;> intro v _ <;>
    exact_mod_cast Nat.factorial_pos _

/-- The genuine decoration fiber cancels exactly one degree factor at every
high-degree vertex; no unproved graph-counting coefficient is introduced. -/
theorem highVertexDecoration_mobius_ratio (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q) :
    |IncidenceAlgebra.mu ℝ (⊥ : Setoid κ) P * IncidenceAlgebra.mu ℝ ⊥ Q| /
      (Fintype.card (HighVertexDecorations P Q) : ℝ) =
        1 / (((Fintype.card (HighGraphVertices P Q)).factorial : ℝ) *
          ∏ v : HighGraphVertices P Q, (partitionGraphDegree P Q v.val : ℝ)) := by
  rw [highVertexDecoration_weight_identity P Q hP hQ]
  have hmu := (partition_mu_product_abs_pos P Q).ne'
  have hb : ((Fintype.card (HighGraphVertices P Q)).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hd : (∏ v : HighGraphVertices P Q, (partitionGraphDegree P Q v.val : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    have hv := v.property
    exact_mod_cast (by omega : partitionGraphDegree P Q v.val ≠ 0)
  field_simp

theorem highVertexDecorations_card_pos (P Q : Setoid κ) :
    0 < Fintype.card (HighVertexDecorations P Q) := by
  rw [highVertexDecorations_card_degrees]
  apply Nat.mul_pos (Nat.factorial_pos _)
  apply Finset.prod_pos
  intro v _
  exact Nat.factorial_pos _

theorem highVertexDecoration_mobius_average (P Q : Setoid κ) :
    (∑ _d : HighVertexDecorations P Q,
      |IncidenceAlgebra.mu ℝ (⊥ : Setoid κ) P * IncidenceAlgebra.mu ℝ ⊥ Q| /
        (Fintype.card (HighVertexDecorations P Q) : ℝ)) =
      |IncidenceAlgebra.mu ℝ (⊥ : Setoid κ) P * IncidenceAlgebra.mu ℝ ⊥ Q| := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card (HighVertexDecorations P Q) : ℝ) ≠ 0 := by
    exact_mod_cast (highVertexDecorations_card_pos P Q).ne'
  exact mul_div_cancel₀ _ hn

end TournamentHamiltonian
