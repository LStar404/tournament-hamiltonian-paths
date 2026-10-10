import TournamentHamiltonian.CoreCompressionTensor
import TournamentHamiltonian.CoreCompressionWeights

/-! Dimension-uniform bounds for the actual compressed graph tensor. -/

namespace TournamentHamiltonian

open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

/-- The index is the chain length minus one. -/
def positiveChainWeight (C q R : ℝ) : ℕ → ℝ
  | 0 => C * R
  | k + 1 => C ^ 2 * R ^ 2 * (R * q) ^ k

theorem positiveChainWeight_nonneg (C q R : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hR : 0 ≤ R) (k : ℕ) : 0 ≤ positiveChainWeight C q R k := by
  cases k <;> simp only [positiveChainWeight] <;> positivity

theorem positiveChainWeight_summable (C q R : ℝ) (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hgap : R * q < 1) : Summable (positiveChainWeight C q R) := by
  apply (summable_nat_add_iff 1).mp
  exact (hasSum_geometric_of_lt_one (mul_nonneg hR hq) hgap).summable.mul_left (C ^ 2 * R ^ 2)

theorem positiveChainWeight_tsum (C q R : ℝ) (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hgap : R * q < 1) :
    (∑' k, positiveChainWeight C q R k) = C * R + C ^ 2 * R ^ 2 / (1 - R * q) := by
  have hs := positiveChainWeight_summable C q R hq hR hgap
  rw [← hs.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, positiveChainWeight]
  rw [((hasSum_geometric_of_lt_one (mul_nonneg hR hq) hgap).mul_left (C ^ 2 * R ^ 2)).tsum_eq]
  ring

/-- Arbitrarily selected finite length vectors are bounded by the full independent chain sum. -/
theorem positiveChainWeight_finite_length_sum_le {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset (α → ℕ)) (C q R : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hgap : R * q < 1) :
    (∑ l ∈ s, ∏ a, positiveChainWeight C q R (l a)) ≤
      (C * R + C ^ 2 * R ^ 2 / (1 - R * q)) ^ Fintype.card α := by
  let t : α → Finset ℕ := fun a => s.image (fun l => l a)
  have hsub : s ⊆ Fintype.piFinset t := by
    intro l hl
    exact Fintype.mem_piFinset.mpr (fun a => Finset.mem_image.mpr ⟨l, hl, rfl⟩)
  have hnonneg := positiveChainWeight_nonneg C q R hC hq hR
  calc
    _ ≤ ∑ l ∈ Fintype.piFinset t, ∏ a, positiveChainWeight C q R (l a) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ =>
        Finset.prod_nonneg (fun a _ => hnonneg (l a)))
    _ = ∏ a, ∑ k ∈ t a, positiveChainWeight C q R k := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _a : α, ∑' k, positiveChainWeight C q R k := by
      apply Finset.prod_le_prod₀
      · intro a _
        exact Finset.sum_nonneg (fun k _ => hnonneg k)
      · intro a _
        exact (positiveChainWeight_summable C q R hq hR hgap).sum_le_tsum (t a) (fun k _ => hnonneg k)
    _ = _ := by rw [positiveChainWeight_tsum C q R hq hR hgap]; simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem alternatingChain_weighted_entry_le (B : Matrix ι ι ℝ) (C q R : ℝ)
    (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i j, |B i j| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (k : ℕ) (s : Bool) (i j : ι) :
    |alternatingChain B (k + 1) s i j| * R ^ (k + 1) ≤
      positiveChainWeight C q R k / (Fintype.card ι : ℝ) := by
  cases k with
  | zero =>
      simp only [zero_add, pow_one, positiveChainWeight]
      have hb : |alternatingChain B 1 s i j| ≤ C / (Fintype.card ι : ℝ) := by
        cases s
        · simpa [alternatingChain, orientedChainFactor] using hB i j
        · simpa [alternatingChain, orientedChainFactor] using hB j i
      calc
        _ ≤ C / (Fintype.card ι : ℝ) * R := mul_le_mul_of_nonneg_right hb hR
        _ = _ := by ring
  | succ k =>
      calc
        _ ≤ (C ^ 2 / (Fintype.card ι : ℝ) * q ^ k) * R ^ (k + 2) :=
          mul_le_mul_of_nonneg_right (alternatingChain_entry_abs_le B C q hC hn hB hq k s i j)
            (pow_nonneg hR _)
        _ = _ := by simp only [positiveChainWeight, pow_add, mul_pow]; ring

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem compressedPathLength_sum (P Q : Setoid κ)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    (∑ c : ActualCompressedPaths P Q, compressedPathLength P Q c) = Fintype.card κ := by
  have h := compressedPathPosition_card P Q hc
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

/-- Every actual compressed core has one power of the ambient dimension per excess. -/
theorem partitionContraction_weighted_path_le (B : Matrix ι ι ℝ) (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e)
    (C q R : ℝ) (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i j, |B i j| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q) :
    |partitionContraction B P Q| * R ^ Fintype.card κ ≤
      (∏ c : ActualCompressedPaths P Q,
        positiveChainWeight C q R (compressedPathLength P Q c - 1)) /
        (Fintype.card ι : ℝ) ^ partitionGraphExcess P Q := by
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hq0 : 0 ≤ q := (norm_nonneg B).trans hq
  have hlen : R ^ Fintype.card κ = ∏ c : ActualCompressedPaths P Q,
      R ^ compressedPathLength P Q c := by
    rw [← compressedPathLength_sum P Q hc, Finset.prod_pow_eq_pow_sum]
  rw [partitionContraction_alternating_chains B P Q hP hQ hc]
  calc
    _ ≤ (∑ r : HighGraphVertices P Q → ι,
        |∏ c : ActualCompressedPaths P Q, alternatingChain B (compressedPathLength P Q c)
          (partitionHalfEdgeSide (compressedPathTerminal P Q c).val)
          (r (compressedPathStartVertex P Q hP hQ c))
          (r (compressedPathEndVertex P Q hP hQ c))|) * R ^ Fintype.card κ :=
      mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hR _)
    _ = ∑ r : HighGraphVertices P Q → ι,
        ∏ c : ActualCompressedPaths P Q,
          |alternatingChain B (compressedPathLength P Q c)
            (partitionHalfEdgeSide (compressedPathTerminal P Q c).val)
            (r (compressedPathStartVertex P Q hP hQ c))
            (r (compressedPathEndVertex P Q hP hQ c))| * R ^ compressedPathLength P Q c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.abs_prod, hlen, ← Finset.prod_mul_distrib]
    _ ≤ ∑ _r : HighGraphVertices P Q → ι,
        ∏ c : ActualCompressedPaths P Q,
          positiveChainWeight C q R (compressedPathLength P Q c - 1) / (Fintype.card ι : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.prod_le_prod₀
      · intro c _
        exact mul_nonneg (abs_nonneg _) (pow_nonneg hR _)
      · intro c _
        have hL : compressedPathLength P Q c - 1 + 1 = compressedPathLength P Q c := by
          have h := compressedPathLength_pos P Q c
          omega
        simpa only [hL] using alternatingChain_weighted_entry_le B C q R hC hn hR hB hq
          (compressedPathLength P Q c - 1) (partitionHalfEdgeSide (compressedPathTerminal P Q c).val)
          (r (compressedPathStartVertex P Q hP hQ c)) (r (compressedPathEndVertex P Q hP hQ c))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
        Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Nat.cast_pow]
      rw [highGraphVertices_card, actualCompressedPairPartition_card P Q hP hQ, pow_add]
      field_simp

theorem partitionContraction_decoration_weighted_path_le (B : Matrix ι ι ℝ) (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e)
    (C q R : ℝ) (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i j, |B i j| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q) :
    |IncidenceAlgebra.mu ℝ (⊥ : Setoid κ) P * IncidenceAlgebra.mu ℝ ⊥ Q *
        partitionContraction B P Q| * R ^ Fintype.card κ /
      (Fintype.card (HighVertexDecorations P Q) : ℝ) ≤
    (∏ c : ActualCompressedPaths P Q, positiveChainWeight C q R (compressedPathLength P Q c - 1)) /
      (((Fintype.card (HighGraphVertices P Q)).factorial : ℝ) *
        (∏ v : HighGraphVertices P Q, (partitionGraphDegree P Q v.val : ℝ)) *
        (Fintype.card ι : ℝ) ^ partitionGraphExcess P Q) := by
  calc
    _ = (|IncidenceAlgebra.mu ℝ (⊥ : Setoid κ) P * IncidenceAlgebra.mu ℝ ⊥ Q| /
        (Fintype.card (HighVertexDecorations P Q) : ℝ)) *
        (|partitionContraction B P Q| * R ^ Fintype.card κ) := by rw [abs_mul]; ring
    _ ≤ (|IncidenceAlgebra.mu ℝ (⊥ : Setoid κ) P * IncidenceAlgebra.mu ℝ ⊥ Q| /
        (Fintype.card (HighVertexDecorations P Q) : ℝ)) *
        ((∏ c : ActualCompressedPaths P Q,
          positiveChainWeight C q R (compressedPathLength P Q c - 1)) /
          (Fintype.card ι : ℝ) ^ partitionGraphExcess P Q) :=
      mul_le_mul_of_nonneg_left (partitionContraction_weighted_path_le B P Q hP hQ hc C q R hC hn hR hB hq)
        (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by rw [highVertexDecoration_mobius_ratio P Q hP hQ]; ring

end TournamentHamiltonian
