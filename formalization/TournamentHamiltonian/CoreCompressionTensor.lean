import TournamentHamiltonian.CoreCompressionEndpoints
import TournamentHamiltonian.GaussianChainWords

/-! Actual partition contractions in compressed numerical coordinates. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

noncomputable def partitionVertexContraction (B : Matrix ι ι ℝ) (P Q : Setoid κ)
    (f : PartitionGraphVertices P Q → ι) : ℝ :=
  ∏ e : κ, B (f (.inl (Quotient.mk P e))) (f (.inr (Quotient.mk Q e)))

omit [DecidableEq κ] [DecidableEq ι] in
theorem partitionContraction_vertex_sum (B : Matrix ι ι ℝ) (P Q : Setoid κ) :
    partitionContraction B P Q = ∑ f : PartitionGraphVertices P Q → ι, partitionVertexContraction B P Q f := by
  unfold partitionContraction
  calc
    _ = ∑ rc : (Quotient P → ι) × (Quotient Q → ι),
        ∏ e : κ, B (rc.1 (Quotient.mk P e)) (rc.2 (Quotient.mk Q e)) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow (Quotient P) (Quotient Q) ι).symm
      intro rc
      rfl

noncomputable def compressedNumericalLabels (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e)
    (r : HighGraphVertices P Q → ι) (w : CompressedInternalPositions P Q → ι) :
    PartitionGraphVertices P Q → ι :=
  Sum.elim r w ∘ (compressedGraphVertexEquiv P Q hP hQ hc).symm

omit [Fintype ι] [DecidableEq ι] in
theorem compressedNumericalLabels_high (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e)
    (r : HighGraphVertices P Q → ι) (w : CompressedInternalPositions P Q → ι) (v : HighGraphVertices P Q) :
    compressedNumericalLabels P Q hP hQ hc r w v.val = r v := by
  rw [← compressedGraphVertexEquiv_high P Q hP hQ hc v]
  change Sum.elim r w ((compressedGraphVertexEquiv P Q hP hQ hc).symm
    ((compressedGraphVertexEquiv P Q hP hQ hc) (.inl v))) = r v
  rw [Equiv.symm_apply_apply]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem compressedNumericalLabels_internal (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e)
    (r : HighGraphVertices P Q → ι) (w : CompressedInternalPositions P Q → ι) (v : CompressedInternalPositions P Q) :
    compressedNumericalLabels P Q hP hQ hc r w (compressedInternalVertex P Q v) = w v := by
  rw [← compressedGraphVertexEquiv_internal P Q hP hQ hc v]
  change Sum.elim r w ((compressedGraphVertexEquiv P Q hP hQ hc).symm
    ((compressedGraphVertexEquiv P Q hP hQ hc) (.inr v))) = w v
  rw [Equiv.symm_apply_apply]
  rfl

omit [DecidableEq ι] in
theorem partitionContraction_compressed_label_sum (B : Matrix ι ι ℝ) (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    partitionContraction B P Q = ∑ r : HighGraphVertices P Q → ι,
      ∑ w : CompressedInternalPositions P Q → ι,
        partitionVertexContraction B P Q (compressedNumericalLabels P Q hP hQ hc r w) := by
  rw [partitionContraction_vertex_sum]
  let e := (Equiv.sumArrowEquivProdArrow (HighGraphVertices P Q) (CompressedInternalPositions P Q) ι).symm.trans
    (Equiv.arrowCongr (compressedGraphVertexEquiv P Q hP hQ hc) (Equiv.refl ι))
  symm
  calc
    _ = ∑ rw : (HighGraphVertices P Q → ι) × (CompressedInternalPositions P Q → ι),
        partitionVertexContraction B P Q (compressedNumericalLabels P Q hP hQ hc rw.1 rw.2) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv e
      intro rw
      rfl

omit [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
theorem partitionHalfEdge_matrix_factor (B : Matrix ι ι ℝ) (P Q : Setoid κ)
    (f : PartitionGraphVertices P Q → ι) (h : PartitionHalfEdges (κ := κ)) :
    B (f (.inl (Quotient.mk P (Sum.elim id id h))))
        (f (.inr (Quotient.mk Q (Sum.elim id id h)))) =
      orientedChainFactor B (partitionHalfEdgeSide (partitionHalfEdgeFlip h))
        (f (partitionHalfEdgeVertex P Q (partitionHalfEdgeFlip h))) (f (partitionHalfEdgeVertex P Q h)) := by
  cases h <;> rfl

omit [Fintype ι] [DecidableEq ι] in
theorem partitionVertexContraction_path_product (B : Matrix ι ι ℝ) (P Q : Setoid κ)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) (f : PartitionGraphVertices P Q → ι) :
    partitionVertexContraction B P Q f = ∏ c : ActualCompressedPaths P Q,
      ∏ i : Fin (compressedPathLength P Q c),
        orientedChainFactor B
          (chainEndpointOrientation i.val (partitionHalfEdgeSide (compressedPathTerminal P Q c).val))
          (f (partitionHalfEdgeVertex P Q (partitionHalfEdgeFlip (compressedPathArrival P Q c i))))
          (f (partitionHalfEdgeVertex P Q (compressedPathArrival P Q c i))) := by
  unfold partitionVertexContraction
  calc
    _ = ∏ x : Σ c : ActualCompressedPaths P Q, Fin (compressedPathLength P Q c),
        B (f (.inl (Quotient.mk P (compressedPathOriginalEdge P Q x))))
          (f (.inr (Quotient.mk Q (compressedPathOriginalEdge P Q x)))) := by
      symm
      apply Fintype.prod_equiv (compressedPathEdgeEquiv P Q hc)
      intro x
      rfl
    _ = _ := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro c _
      apply Finset.prod_congr rfl
      intro i _
      change B (f (.inl (Quotient.mk P (Sum.elim id id (compressedPathArrival P Q c i)))))
        (f (.inr (Quotient.mk Q (Sum.elim id id (compressedPathArrival P Q c i))))) = _
      exact (partitionHalfEdge_matrix_factor B P Q f (compressedPathArrival P Q c i)).trans
        (by rw [compressedPathArrival_departure_side])

omit [Fintype ι] [DecidableEq ι] in
theorem compressedNumericalLabels_departure_word (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e)
    (r : HighGraphVertices P Q → ι) (w : CompressedInternalPositions P Q → ι)
    (c : ActualCompressedPaths P Q) (m : ℕ) (hL : compressedPathLength P Q c = m + 1)
    (i : Fin (m + 1)) :
    compressedNumericalLabels P Q hP hQ hc r w
      (partitionHalfEdgeVertex P Q (partitionHalfEdgeFlip
        (compressedPathArrival P Q c (Fin.cast hL.symm i)))) =
      chainWordVertices m (r (compressedPathStartVertex P Q hP hQ c))
        (r (compressedPathEndVertex P Q hP hQ c))
        (fun j => w ⟨c, ⟨j.val, by omega⟩⟩) i.castSucc := by
  cases i using Fin.cases with
  | zero =>
      have hi : Fin.cast hL.symm (0 : Fin (m + 1)) =
          ⟨0, compressedPathLength_pos P Q c⟩ := Fin.ext rfl
      rw [hi, compressedPathArrival_first_departure_vertex,
        compressedNumericalLabels_high]
      rfl
  | succ i =>
      have hi : Fin.cast hL.symm i.succ =
          ⟨i.val + 1, by omega⟩ := Fin.ext rfl
      rw [hi]
      have hv := compressedPathArrival_previous_departure_vertex P Q c
        (⟨i.val, by omega⟩ : Fin (compressedPathLength P Q c - 1))
      rw [hv, compressedNumericalLabels_internal]
      simp only [chainWordVertices, Fin.castSucc_succ, Fin.cons_succ, Fin.snoc_castSucc]

omit [Fintype ι] [DecidableEq ι] in
theorem compressedNumericalLabels_arrival_word (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e)
    (r : HighGraphVertices P Q → ι) (w : CompressedInternalPositions P Q → ι)
    (c : ActualCompressedPaths P Q) (m : ℕ) (hL : compressedPathLength P Q c = m + 1)
    (i : Fin (m + 1)) :
    compressedNumericalLabels P Q hP hQ hc r w
      (partitionHalfEdgeVertex P Q (compressedPathArrival P Q c (Fin.cast hL.symm i))) =
      chainWordVertices m (r (compressedPathStartVertex P Q hP hQ c))
        (r (compressedPathEndVertex P Q hP hQ c))
        (fun j => w ⟨c, ⟨j.val, by omega⟩⟩) i.succ := by
  cases i using Fin.lastCases with
  | last =>
      have hi : Fin.cast hL.symm (Fin.last m) =
          ⟨compressedPathLength P Q c - 1, by have h := compressedPathLength_pos P Q c; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [hi, compressedPathArrival_last_vertex P Q hP hQ c, compressedNumericalLabels_high]
      simp only [chainWordVertices, Fin.cons_succ, Fin.snoc_last]
  | cast i =>
      have hi : Fin.cast hL.symm i.castSucc = ⟨i.val, by omega⟩ := Fin.ext rfl
      rw [hi]
      have hv := compressedPathArrival_internal_vertex P Q c
        (⟨i.val, by omega⟩ : Fin (compressedPathLength P Q c - 1))
      rw [hv, compressedNumericalLabels_internal]
      simp only [chainWordVertices, Fin.cons_succ, Fin.snoc_castSucc]

omit [Fintype ι] [DecidableEq ι] in
theorem compressedPath_factor_word (B : Matrix ι ι ℝ) (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e)
    (r : HighGraphVertices P Q → ι) (w : CompressedInternalPositions P Q → ι)
    (c : ActualCompressedPaths P Q) :
    (∏ i : Fin (compressedPathLength P Q c), orientedChainFactor B
      (chainEndpointOrientation i.val (partitionHalfEdgeSide (compressedPathTerminal P Q c).val))
      (compressedNumericalLabels P Q hP hQ hc r w
        (partitionHalfEdgeVertex P Q (partitionHalfEdgeFlip (compressedPathArrival P Q c i))))
      (compressedNumericalLabels P Q hP hQ hc r w
        (partitionHalfEdgeVertex P Q (compressedPathArrival P Q c i)))) =
    alternatingChainWord B (compressedPathLength P Q c - 1)
      (partitionHalfEdgeSide (compressedPathTerminal P Q c).val)
      (r (compressedPathStartVertex P Q hP hQ c))
      (r (compressedPathEndVertex P Q hP hQ c)) (fun i => w ⟨c, i⟩) := by
  have hL : compressedPathLength P Q c = (compressedPathLength P Q c - 1) + 1 := by
    have h := compressedPathLength_pos P Q c
    omega
  rw [alternatingChainWord_eq_prod]
  symm
  apply Fintype.prod_equiv (finCongr hL.symm)
  intro i
  exact congrArg₂ (fun x y : ι => orientedChainFactor B
      (chainEndpointOrientation i.val (partitionHalfEdgeSide (compressedPathTerminal P Q c).val)) x y)
    (compressedNumericalLabels_departure_word P Q hP hQ hc r w c _ hL i).symm
    (compressedNumericalLabels_arrival_word P Q hP hQ hc r w c _ hL i).symm

theorem partitionContraction_alternating_chains (B : Matrix ι ι ℝ) (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    partitionContraction B P Q = ∑ r : HighGraphVertices P Q → ι,
      ∏ c : ActualCompressedPaths P Q, alternatingChain B (compressedPathLength P Q c)
        (partitionHalfEdgeSide (compressedPathTerminal P Q c).val)
        (r (compressedPathStartVertex P Q hP hQ c))
        (r (compressedPathEndVertex P Q hP hQ c)) := by
  rw [partitionContraction_compressed_label_sum B P Q hP hQ hc]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ∑ w : CompressedInternalPositions P Q → ι,
        ∏ c : ActualCompressedPaths P Q, alternatingChainWord B (compressedPathLength P Q c - 1)
          (partitionHalfEdgeSide (compressedPathTerminal P Q c).val)
          (r (compressedPathStartVertex P Q hP hQ c))
          (r (compressedPathEndVertex P Q hP hQ c)) (fun i => w ⟨c, i⟩) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [partitionVertexContraction_path_product B P Q hc]
      apply Finset.prod_congr rfl
      intro c _
      exact compressedPath_factor_word B P Q hP hQ hc r w c
    _ = ∑ w : ∀ c : ActualCompressedPaths P Q, Fin (compressedPathLength P Q c - 1) → ι,
        ∏ c : ActualCompressedPaths P Q, alternatingChainWord B (compressedPathLength P Q c - 1)
          (partitionHalfEdgeSide (compressedPathTerminal P Q c).val)
          (r (compressedPathStartVertex P Q hP hQ c))
          (r (compressedPathEndVertex P Q hP hQ c)) (w c) := by
      apply Fintype.sum_equiv (Equiv.piCurry (fun (c : ActualCompressedPaths P Q)
        (_ : Fin (compressedPathLength P Q c - 1)) => ι))
      intro w
      rfl
    _ = ∏ c : ActualCompressedPaths P Q,
        ∑ w : Fin (compressedPathLength P Q c - 1) → ι,
          alternatingChainWord B (compressedPathLength P Q c - 1)
            (partitionHalfEdgeSide (compressedPathTerminal P Q c).val)
            (r (compressedPathStartVertex P Q hP hQ c))
            (r (compressedPathEndVertex P Q hP hQ c)) w := (Fintype.prod_sum _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro c _
      rw [alternatingChainWord_sum]
      have hL : compressedPathLength P Q c - 1 + 1 = compressedPathLength P Q c := by
        have h := compressedPathLength_pos P Q c
        omega
      rw [hL]

end TournamentHamiltonian
