import TournamentHamiltonian.PathConvolution
import TournamentHamiltonian.PathConvolutionCoefficients
import Mathlib.GroupTheory.Perm.Fin

/-! The marked-cycle expansion for the final Hamiltonian path convolution.
This file builds on the exact inverse convolution and keeps the actual
weighted permutation definition of paths. -/

namespace TournamentHamiltonian

open scoped Classical

/-- A rank-one all-ones perturbation has no determinant terms involving two
or more perturbed rows. This identity requires no nonsingularity assumption. -/
theorem det_add_ones_eq_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) :
    (M + Matrix.of (fun _ _ => (1 : ℝ))).det =
      M.det + ∑ i, (M.updateRow i (fun _ => 1)).det := by
  let J : Matrix ι ι ℝ := Matrix.of (fun _ _ => 1)
  let D := (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).toMultilinearMap
  change D ((fun i => M i) + (fun i => J i)) =
    D M + ∑ i, D (Function.update M i (fun _ => 1))
  rw [D.map_add_eq_map_add_linearDeriv_add]
  have hz : (∑ s : Finset ι with 2 ≤ s.card, D (s.piecewise J M)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hcard : 1 < s.card := by
      have := (Finset.mem_filter.mp hs).2
      omega
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
    change Matrix.det (s.piecewise J M : Matrix ι ι ℝ) = 0
    apply Matrix.det_zero_of_row_eq hij
    funext k
    simp [Finset.piecewise, hi, hj, J]
  rw [hz, add_zero, D.linearDeriv_apply]
  rfl

/-- Column form of the unconditional rank-one expansion, convenient for the
column-indexed permutation product in `Matrix.det_apply'`. -/
theorem det_add_ones_eq_cols {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) :
    (M + Matrix.of (fun _ _ => (1 : ℝ))).det =
      M.det + ∑ i, (M.updateCol i (fun _ => 1)).det := by
  have h := det_add_ones_eq_rows M.transpose
  have ht : (M + Matrix.of (fun _ _ => (1 : ℝ))).transpose =
      M.transpose + Matrix.of (fun _ _ => (1 : ℝ)) := rfl
  rw [← ht, Matrix.det_transpose, Matrix.det_transpose] at h
  simpa only [Matrix.updateRow_transpose, Matrix.det_transpose] using h

/-- The selected all-ones column marks one removed edge in each permutation
cycle cover. All other columns retain their actual adjacency factors. -/
theorem det_marked_column_eq_permutation_sum {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ) (r : ι) :
    ((-A).updateCol r (fun _ => 1)).det =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        (-1 : ℝ) ^ (Fintype.card ι - 1) *
          ∏ i ∈ (Finset.univ : Finset ι).erase r, A (σ i) i := by
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
    (fun i => ((-A).updateCol r (fun _ => (1 : ℝ))) (σ i) i) (Finset.mem_univ r)]
  simp only [Matrix.updateCol_self, one_mul]
  have heq : (∏ i ∈ (Finset.univ : Finset ι).erase r,
        ((-A).updateCol r (fun _ => (1 : ℝ))) (σ i) i) =
      ∏ i ∈ (Finset.univ : Finset ι).erase r, -A (σ i) i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hir : i ≠ r := (Finset.mem_erase.mp hi).1
    simp [hir]
  rw [heq, Finset.prod_neg, Finset.card_erase_of_mem (Finset.mem_univ r),
    Finset.card_univ]
  ring

theorem sum_cycle_colors_eq_zero_pow {κ : Type*} [Fintype κ] [DecidableEq κ] :
    (∑ colors : κ → Bool, ∏ k : κ, if colors k then (-1 : ℝ) else 1) =
      (0 : ℝ) ^ Fintype.card κ := by
  rw [← Fintype.prod_sum (fun (_ : κ) (b : Bool) => if b then (-1 : ℝ) else 1)]
  simp [Fintype.univ_bool]

/-- Selecting the marked cycle forces its determinant color. All other
cycles cancel, leaving one precisely when the marked cycle covers every
vertex. -/
theorem sum_marked_cycle_colors {κ : Type*} [Fintype κ] [DecidableEq κ] (r : κ) :
    (∑ colors : κ → Bool,
      if colors r then -(∏ k : κ, if colors k then (-1 : ℝ) else 1) else 0) =
      if Fintype.card κ = 1 then 1 else 0 := by
  calc
    _ = ∑ v : Bool × ({k : κ // k ≠ r} → Bool),
        if v.1 then (∏ k : {k : κ // k ≠ r}, if v.2 k then (-1 : ℝ) else 1) else 0 := by
      apply Fintype.sum_equiv (Equiv.funSplitAt r Bool)
      intro colors
      change (if colors r then -(∏ k : κ, if colors k then (-1 : ℝ) else 1) else 0) =
        (if colors r then (∏ k : {k : κ // k ≠ r},
          if colors k.val then (-1 : ℝ) else 1) else 0)
      rw [Fintype.prod_eq_mul_prod_subtype_ne (fun k => if colors k then (-1 : ℝ) else 1) r]
      cases colors r <;> simp
    _ = ∑ b : Bool, ∑ colors : {k : κ // k ≠ r} → Bool,
        if b then (∏ k : {k : κ // k ≠ r}, if colors k then (-1 : ℝ) else 1) else 0 :=
      Fintype.sum_prod_type _
    _ = (0 : ℝ) ^ Fintype.card {k : κ // k ≠ r} := by
      simpa [Fintype.univ_bool] using
        (sum_cycle_colors_eq_zero_pow (κ := {k : κ // k ≠ r}))
    _ = _ := by
      have hc : Fintype.card {k : κ // k ≠ r} = Fintype.card κ - 1 := by
        rw [Fintype.card_subtype_compl]
        simp
      rw [hc]
      have hpos : 0 < Fintype.card κ := Fintype.card_pos_iff.mpr ⟨r⟩
      by_cases heq : Fintype.card κ = 1
      · simp [heq]
      · have hn : Fintype.card κ - 1 ≠ 0 := by omega
        simp [heq, hn]

/-- Marking a vertex in the determinant factor leaves only permutations
whose one complete cycle covers the entire vertex type. -/
theorem sum_invariant_marked_determinant_sign {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) (r : α) :
    (∑ f : {f : α → Bool // ∀ i, f (σ i) = f i},
      if f.val r then
        -((-1 : ℝ) ^ Fintype.card {i : α // f.val i = true} *
          ((Equiv.Perm.sign (σ.subtypePerm (p := fun i => f.val i = true)
            (fun i => by rw [f.property i])) : ℤ) : ℝ)) else 0) =
      if Fintype.card (CoverCycles σ) = 1 then 1 else 0 := by
  calc
    _ = ∑ colors : CoverCycles σ → Bool,
        if colors (coverCycleOf σ r) then
          -(∏ k : CoverCycles σ, if colors k then (-1 : ℝ) else 1) else 0 := by
      symm
      apply Fintype.sum_equiv (cycleColoringEquiv σ)
      intro colors
      have hsign := restriction_determinant_weight_eq_colors σ
        ((cycleColoringEquiv σ) colors).val ((cycleColoringEquiv σ) colors).property
      change _ = ∏ k : CoverCycles σ,
        if (cycleColoringEquiv σ).symm ((cycleColoringEquiv σ) colors) k
          then (-1 : ℝ) else 1 at hsign
      rw [Equiv.symm_apply_apply] at hsign
      change (if colors (coverCycleOf σ r) then -_ else 0) =
        (if colors (coverCycleOf σ r) then -_ else 0)
      rw [hsign]
    _ = _ := sum_marked_cycle_colors (coverCycleOf σ r)

theorem prod_updateCol_neg_one_eq_neg_erase {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℝ) (σ : Equiv.Perm α) (r : α) :
    (∏ i : α, (A.updateCol r (fun _ => (-1 : ℝ))) (σ i) i) =
      -(∏ i ∈ (Finset.univ : Finset α).erase r, A (σ i) i) := by
  rw [← Finset.mul_prod_erase (Finset.univ : Finset α)
    (fun i => (A.updateCol r (fun _ => (-1 : ℝ))) (σ i) i) (Finset.mem_univ r)]
  simp only [Matrix.updateCol_self, neg_one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp [(Finset.mem_erase.mp hi).1]

noncomputable def brokenCycleWeight {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (σ : Equiv.Perm α) (r : α) : ℝ :=
  ∏ i ∈ (Finset.univ : Finset α).erase r, A (σ i) i

noncomputable def markedInvariantCoverWeight {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (r : α) (σ : Equiv.Perm α)
    (f : {f : α → Bool // ∀ i, f (σ i) = f i}) : ℝ :=
  (if f.val r then
    -((-1 : ℝ) ^ Fintype.card {i : α // f.val i = true} *
      ((Equiv.Perm.sign (σ.subtypePerm (p := fun i => f.val i = true)
        (fun i => by rw [f.property i])) : ℤ) : ℝ)) else 0) * brokenCycleWeight A σ r

set_option maxHeartbeats 1000000 in
/-- The marked rank-one coefficient eliminates every unmarked cycle and
retains exactly complete single-cycle covers with one deleted edge. -/
theorem marked_det_per_sum_eq_single_cycles {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℝ) (r : α) :
    (∑ f : α → Bool, if f r then
      ((-(A.updateCol r (fun _ => (-1 : ℝ)))).submatrix
        (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
      ((A.updateCol r (fun _ => (-1 : ℝ))).submatrix
        (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent else 0) =
    ∑ σ : Equiv.Perm α, if Fintype.card (CoverCycles σ) = 1
      then brokenCycleWeight A σ r else 0 := by
  calc
    _ = ∑ f : α → Bool, ∑ σ : {σ : Equiv.Perm α // ∀ i, f (σ i) = f i},
        markedInvariantCoverWeight A r σ.val ⟨f, σ.property⟩ := by
      apply Finset.sum_congr rfl
      intro f _
      rw [det_per_colorClass_eq_sum_preserving]
      by_cases hr : f r = true
      · rw [ite_eq_left hr]
        apply Finset.sum_congr rfl
        intro σ _
        unfold markedInvariantCoverWeight brokenCycleWeight
        rw [ite_eq_left hr, prod_updateCol_neg_one_eq_neg_erase]
        ring
      · rw [ite_eq_right hr]
        symm
        apply Finset.sum_eq_zero
        intro σ _
        simp [markedInvariantCoverWeight, hr]
    _ = ∑ x : (Σ f : α → Bool, {σ : Equiv.Perm α // ∀ i, f (σ i) = f i}),
        markedInvariantCoverWeight A r x.2.val ⟨x.1, x.2.property⟩ :=
      (Fintype.sum_sigma (fun x : (Σ f : α → Bool,
        {σ : Equiv.Perm α // ∀ i, f (σ i) = f i}) =>
          markedInvariantCoverWeight A r x.2.val ⟨x.1, x.2.property⟩)).symm
    _ = ∑ x : (Σ σ : Equiv.Perm α, {f : α → Bool // ∀ i, f (σ i) = f i}),
        markedInvariantCoverWeight A r x.1 x.2 := by
      apply Fintype.sum_equiv swapInvariantColoring
      intro x
      rfl
    _ = ∑ σ : Equiv.Perm α, ∑ f : {f : α → Bool // ∀ i, f (σ i) = f i},
        markedInvariantCoverWeight A r σ f :=
      Fintype.sum_sigma (fun x : (Σ σ : Equiv.Perm α,
        {f : α → Bool // ∀ i, f (σ i) = f i}) => markedInvariantCoverWeight A r x.1 x.2)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      unfold markedInvariantCoverWeight
      rw [← Finset.sum_mul]
      rw [sum_invariant_marked_determinant_sign]
      split_ifs <;> simp

theorem marked_column_positive_class {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (f : α → Bool) (r : {i : α // f i = true}) :
    (-(A.updateCol r.val (fun _ => (-1 : ℝ)))).submatrix
      (Subtype.val : {i : α // f i = true} → α) (Subtype.val : {i : α // f i = true} → α) =
      (-(A.submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val)).updateCol
        r (fun _ => 1) := by
  ext i j
  by_cases hj : j = r
  · subst j
    simp
  · have hjv : j.val ≠ r.val := fun h => hj (Subtype.ext h)
    simp [hj, hjv]

theorem marked_column_negative_class {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (f : α → Bool) (r : {i : α // f i = true}) :
    (A.updateCol r.val (fun _ => (-1 : ℝ))).submatrix
      (Subtype.val : {i : α // f i ≠ true} → α)
      (Subtype.val : {i : α // f i ≠ true} → α) =
      A.submatrix (Subtype.val : {i : α // f i ≠ true} → α)
        (Subtype.val : {i : α // f i ≠ true} → α) := by
  ext i j
  have hjr : j.val ≠ r.val := by
    intro h
    apply j.property
    rw [h]
    exact r.property
  simp [hjr]

theorem sum_marked_columns_eq_vertex_sum {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (f : α → Bool) :
    (∑ r : {i : α // f i = true},
      ((-(A.submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val)).updateCol
        r (fun _ => 1)).det *
        (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent) =
    ∑ r : α, if f r then
      ((-(A.updateCol r (fun _ => (-1 : ℝ)))).submatrix
        (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
      ((A.updateCol r (fun _ => (-1 : ℝ))).submatrix
        (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent else 0 := by
  let G (r : α) : ℝ :=
    ((-(A.updateCol r (fun _ => (-1 : ℝ)))).submatrix
      (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
    ((A.updateCol r (fun _ => (-1 : ℝ))).submatrix
      (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent
  calc
    _ = ∑ r : {i : α // f i = true}, G r.val := by
      apply Finset.sum_congr rfl
      intro r _
      dsimp [G]
      rw [marked_column_positive_class, marked_column_negative_class]
    _ = ∑ r ∈ (Finset.univ : Finset α).filter (fun r => f r = true), G r :=
      (Finset.sum_subtype _ (by simp) G).symm
    _ = _ := by rw [Finset.sum_filter]

theorem det_complement_class_eq_marked_columns {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℝ) (f : α → Bool) :
    ((Matrix.of (fun _ _ => (1 : ℝ)) - A).submatrix
      (Subtype.val : {i : α // f i = true} → α) Subtype.val).det =
      ((-A).submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det +
        ∑ r : {i : α // f i = true},
          ((-(A.submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val)).updateCol
            r (fun _ => 1)).det := by
  have heq : (Matrix.of (fun _ _ => (1 : ℝ)) - A).submatrix
      (Subtype.val : {i : α // f i = true} → α) (Subtype.val : {i : α // f i = true} → α) =
      -(A.submatrix (Subtype.val : {i : α // f i = true} → α) (Subtype.val : {i : α // f i = true} → α)) +
        Matrix.of (fun _ _ => (1 : ℝ)) := by
    ext i j
    simp
    ring
  rw [heq, det_add_ones_eq_cols]
  rfl

set_option maxHeartbeats 1000000 in
/-- Exact positive-complement convolution reduced to complete marked cycles.
The separate empty term preserves the empty-order convention. -/
theorem complement_det_per_convolution_bool_eq_cycles {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℝ) :
    (∑ f : α → Bool,
      ((Matrix.of (fun _ _ => (1 : ℝ)) - A).submatrix
        (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
        (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent) =
      (if Fintype.card α = 0 then 1 else 0) +
        ∑ r : α, ∑ σ : Equiv.Perm α, if Fintype.card (CoverCycles σ) = 1
          then brokenCycleWeight A σ r else 0 := by
  calc
    _ = ∑ f : α → Bool,
        (((-A).submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det +
          ∑ r : {i : α // f i = true},
            ((-(A.submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val)).updateCol
              r (fun _ => 1)).det) *
          (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent := by
      simp_rw [det_complement_class_eq_marked_columns]
    _ = (∑ f : α → Bool,
        ((-A).submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
          (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent) +
      ∑ f : α → Bool, ∑ r : {i : α // f i = true},
        ((-(A.submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val)).updateCol
          r (fun _ => 1)).det *
          (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    _ = (if Fintype.card α = 0 then 1 else 0) +
      ∑ f : α → Bool, ∑ r : α, if f r then
        ((-(A.updateCol r (fun _ => (-1 : ℝ)))).submatrix
          (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
        ((A.updateCol r (fun _ => (-1 : ℝ))).submatrix
          (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent else 0 := by
      rw [det_per_inverse_convolution_bool_all]
      congr 1
      apply Finset.sum_congr rfl
      intro f _
      exact sum_marked_columns_eq_vertex_sum A f
    _ = _ := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      exact marked_det_per_sum_eq_single_cycles A r

/-- Convert the Bool partition convention to the manuscript's finite subsets. -/
theorem det_per_subset_sum_eq_bool {α : Type*} [Fintype α] [DecidableEq α]
    (B A : Matrix α α ℝ) :
    (∑ U : Finset α,
      (B.submatrix (Subtype.val : U → α) Subtype.val).det *
        (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent) =
    ∑ f : α → Bool,
      (B.submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
        (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent := by
  apply Fintype.sum_equiv vertexSubsetEquivBool
  intro U
  let ep : {i : α // vertexSubsetEquivBool U i = true} ≃ U :=
    Equiv.subtypeEquivRight (fun i => by simp [vertexSubsetEquivBool])
  let en : {i : α // vertexSubsetEquivBool U i ≠ true} ≃ (Uᶜ : Finset α) :=
    Equiv.subtypeEquivRight (fun i => by simp [vertexSubsetEquivBool])
  have hp : (B.submatrix
      (Subtype.val : {i : α // vertexSubsetEquivBool U i = true} → α) Subtype.val).det =
      (B.submatrix (Subtype.val : U → α) Subtype.val).det :=
    Matrix.det_submatrix_equiv_self ep (B.submatrix (Subtype.val : U → α) Subtype.val)
  have hn : (A.submatrix
      (Subtype.val : {i : α // vertexSubsetEquivBool U i ≠ true} → α) Subtype.val).permanent =
      (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent :=
    permanent_submatrix_equiv_self
      (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val) en
  rw [hp, hn]

theorem pathConvolutionSum_eq_marked_cycles {n : ℕ} (T : Tournament n) :
    pathConvolutionSum T = (if n = 0 then 1 else 0) +
      ∑ r : Fin n, ∑ σ : Equiv.Perm (Fin n),
        if Fintype.card (CoverCycles σ) = 1 then brokenCycleWeight (adjacency T) σ r else 0 := by
  unfold pathConvolutionSum
  have hdet : ∀ U : Finset (Fin n), (principalWeightMatrix T U).det =
      ((complementAdjacency T).submatrix (Subtype.val : U → Fin n) Subtype.val).det :=
    fun U => (complementAdjacency_principal_det T U).symm
  simp_rw [hdet]
  rw [det_per_subset_sum_eq_bool]
  simpa only [complementAdjacency, Fintype.card_fin] using
    complement_det_per_convolution_bool_eq_cycles (adjacency T)

/-- A single cover cycle includes the identity at order one. -/
theorem coverCycles_card_one_iff {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (σ : Equiv.Perm α) :
    Fintype.card (CoverCycles σ) = 1 ↔ σ.IsCycleOn Set.univ := by
  constructor
  · intro hc
    have hsub : Subsingleton (CoverCycles σ) :=
      Fintype.card_le_one_iff_subsingleton.mp hc.le
    refine ⟨?_, fun i _ j _ => (coverCycleOf_eq_iff_sameCycle σ i j).mp ?_⟩
    · exact σ.bijective.bijOn_univ
    · exact hsub.elim _ _
  · intro h
    obtain ⟨i⟩ := ‹Nonempty α›
    apply Fintype.card_eq_one_of_forall_eq (i := coverCycleOf σ i)
    intro k
    obtain ⟨j, rfl⟩ := coverCycleOf_surjective σ k
    exact (coverCycleOf_eq_iff_sameCycle σ j i).mpr (h.2 (by simp) (by simp))

theorem finRotate_isCycleOn_univ (n : ℕ) :
    (finRotate (n + 1)).IsCycleOn Set.univ := by
  cases n with
  | zero => simpa using (Equiv.Perm.isCycleOn_of_subsingleton (finRotate 1) Set.univ)
  | succ n =>
    have h := (isCycle_finRotate (n := n)).isCycleOn
    have hs : {i | (finRotate (n + 2)) i ≠ i} = Set.univ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact Equiv.Perm.mem_support.mp (by rw [support_finRotate]; simp)
    simpa only [hs] using h

/-- The vertex ordering obtained by following the inverse cycle from its break. -/
noncomputable def markedCycleOrdering {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : σ.IsCycleOn Set.univ) (r : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (fun i : Fin (n + 1) => (σ⁻¹ ^ i.val) r) (by
    have hinv : σ⁻¹.IsCycleOn (Finset.univ : Finset (Fin (n + 1))) := by
      simpa using hσ.inv
    constructor
    · intro i j hij
      have hp := hinv.pow_apply_eq_pow_apply (s := Finset.univ) (m := i.val) (n := j.val) (by simp : r ∈ Finset.univ)
      have hm := hp.mp hij
      apply Fin.ext
      simpa only [Finset.card_univ, Fintype.card_fin, Nat.ModEq,
        Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hm
    · intro j
      obtain ⟨k, hk, hkj⟩ := hinv.exists_pow_eq (s := Finset.univ)
        (by simp : r ∈ Finset.univ) (by simp : j ∈ Finset.univ)
      exact ⟨⟨k, by simpa using hk⟩, hkj⟩)

@[simp] theorem markedCycleOrdering_apply {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ.IsCycleOn Set.univ)
    (r i : Fin (n + 1)) : markedCycleOrdering σ hσ r i = (σ⁻¹ ^ i.val) r := rfl

@[simp] theorem markedCycleOrdering_zero {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ.IsCycleOn Set.univ)
    (r : Fin (n + 1)) : markedCycleOrdering σ hσ r 0 = r := by simp

theorem finRotate_castSucc {n : ℕ} (i : Fin n) :
    finRotate (n + 1) i.castSucc = i.succ := by
  exact finRotate_of_lt i.isLt

/-- Close an ordering by adding the omitted last-to-first edge. -/
noncomputable def cycleFromOrdering {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 1)) := ψ * (finRotate (n + 1))⁻¹ * ψ⁻¹

theorem cycleFromOrdering_isCycleOn {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1))) :
    (cycleFromOrdering ψ).IsCycleOn Set.univ := by
  simpa [cycleFromOrdering] using ((finRotate_isCycleOn_univ n).inv.conj (g := ψ))

@[simp] theorem cycleFromOrdering_inv_apply {n : ℕ}
    (ψ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (cycleFromOrdering ψ)⁻¹ (ψ i) = ψ (finRotate (n + 1) i) := by
  simp [cycleFromOrdering, Equiv.Perm.mul_apply]

theorem markedCycleOrdering_rotate {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ.IsCycleOn Set.univ)
    (r i : Fin (n + 1)) :
    markedCycleOrdering σ hσ r (finRotate (n + 1) i) =
      σ⁻¹ (markedCycleOrdering σ hσ r i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [finRotate_last, markedCycleOrdering_zero]
    simp only [markedCycleOrdering_apply, Fin.val_last]
    rw [← Equiv.Perm.mul_apply, ← pow_succ']
    have hs : σ⁻¹.IsCycleOn (Finset.univ : Finset (Fin (n + 1))) := by
      simpa using hσ.inv
    simpa using (hs.pow_card_apply (by simp : r ∈ Finset.univ)).symm
  · rw [finRotate_castSucc]
    simp only [markedCycleOrdering_apply, Fin.val_succ, Fin.val_castSucc,
      pow_succ', Equiv.Perm.mul_apply]

theorem cycleFromOrdering_markedCycleOrdering {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ.IsCycleOn Set.univ)
    (r : Fin (n + 1)) : cycleFromOrdering (markedCycleOrdering σ hσ r) = σ := by
  apply inv_injective
  apply Equiv.ext
  intro j
  obtain ⟨i, rfl⟩ := (markedCycleOrdering σ hσ r).surjective j
  rw [cycleFromOrdering_inv_apply, markedCycleOrdering_rotate]

theorem ordering_cycle_inv_pow {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) : ((cycleFromOrdering ψ)⁻¹ ^ i.val) (ψ 0) = ψ i := by
  have hp : ∀ m (hm : m < n + 1),
      ((cycleFromOrdering ψ)⁻¹ ^ m) (ψ 0) = ψ ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero => intro hm; simp
    | succ m ih =>
      intro hm
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega), cycleFromOrdering_inv_apply]
      congr 1
      exact finRotate_of_lt (by omega)
  exact hp i.val i.isLt

theorem markedCycleOrdering_cycleFromOrdering {n : ℕ}
    (ψ : Equiv.Perm (Fin (n + 1))) :
    markedCycleOrdering (cycleFromOrdering ψ) (cycleFromOrdering_isCycleOn ψ) (ψ 0) = ψ := by
  apply Equiv.ext
  intro i
  exact ordering_cycle_inv_pow ψ i

abbrev CompleteCycles (n : ℕ) :=
  {σ : Equiv.Perm (Fin (n + 1)) // Fintype.card (CoverCycles σ) = 1}

/-- Every linear ordering is uniquely a complete cycle together with its break. -/
noncomputable def orderingEquivMarkedCycle (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) ≃ CompleteCycles n × Fin (n + 1) where
  toFun ψ := (⟨cycleFromOrdering ψ,
    (coverCycles_card_one_iff _).mpr (cycleFromOrdering_isCycleOn ψ)⟩, ψ 0)
  invFun p := markedCycleOrdering p.1.val
    ((coverCycles_card_one_iff _).mp p.1.property) p.2
  left_inv ψ := markedCycleOrdering_cycleFromOrdering ψ
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact cycleFromOrdering_markedCycleOrdering _ _ _
    · exact markedCycleOrdering_zero _ _ _

/-- The omitted cycle edge is precisely the artificial last-to-first closure. -/
theorem brokenCycleWeight_cycleFromOrdering {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) :
    brokenCycleWeight A (cycleFromOrdering ψ) (ψ 0) =
      ∏ i : Fin n, A (ψ i.castSucc) (ψ i.succ) := by
  unfold brokenCycleWeight
  symm
  apply Finset.prod_bij (fun i _ => ψ i.succ)
  · intro i _
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
      EmbeddingLike.apply_eq_iff_eq, Fin.succ_ne_zero, not_false_eq_true]
  · intro i _ j _ hij
    exact Fin.succ_injective n (ψ.injective hij)
  · intro j hj
    obtain ⟨i, rfl⟩ := ψ.surjective j
    have hi : i ≠ 0 := by simpa using (Finset.mem_erase.mp hj).1
    exact ⟨i.pred hi, Finset.mem_univ _, congrArg ψ (Fin.succ_pred i hi)⟩
  · intro i _
    have hp : (cycleFromOrdering ψ) (ψ i.succ) = ψ i.castSucc := by
      apply (cycleFromOrdering ψ).symm.injective
      rw [Equiv.symm_apply_apply]
      change ψ i.succ = (cycleFromOrdering ψ)⁻¹ (ψ i.castSucc)
      rw [cycleFromOrdering_inv_apply, finRotate_castSucc]
    rw [hp]

/-- Weighted linear orderings are exactly complete cycles with one omitted edge. -/
theorem sum_path_products_eq_marked_cycles {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (∑ ψ : Equiv.Perm (Fin (n + 1)), ∏ i : Fin n, A (ψ i.castSucc) (ψ i.succ)) =
      ∑ r : Fin (n + 1), ∑ σ : Equiv.Perm (Fin (n + 1)),
        if Fintype.card (CoverCycles σ) = 1 then brokenCycleWeight A σ r else 0 := by
  calc
    _ = ∑ p : CompleteCycles n × Fin (n + 1), brokenCycleWeight A p.1.val p.2 := by
      apply Fintype.sum_equiv (orderingEquivMarkedCycle n)
      intro ψ
      exact (brokenCycleWeight_cycleFromOrdering A ψ).symm
    _ = ∑ σ : CompleteCycles n, ∑ r : Fin (n + 1), brokenCycleWeight A σ.val r :=
      Fintype.sum_prod_type (fun p : CompleteCycles n × Fin (n + 1) =>
        brokenCycleWeight A p.1.val p.2)
    _ = ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))).filter
        (fun σ => Fintype.card (CoverCycles σ) = 1),
        ∑ r : Fin (n + 1), brokenCycleWeight A σ r :=
      (Finset.sum_subtype _ (by simp) (fun σ => ∑ r : Fin (n + 1), brokenCycleWeight A σ r)).symm
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)), ∑ r : Fin (n + 1),
        if Fintype.card (CoverCycles σ) = 1 then brokenCycleWeight A σ r else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hc : Fintype.card (CoverCycles σ) = 1 <;> simp [hc]
    _ = _ := Finset.sum_comm

/-- The actual directed Hamiltonian path count, with the original permutation
predicate and empty-order convention, equals the manuscript's positive
permanent/determinant convolution. -/
theorem pathCount_eq_pathConvolutionSum {n : ℕ} (T : Tournament n) :
    (pathCount T : ℝ) = pathConvolutionSum T := by
  cases n with
  | zero =>
    rw [pathConvolutionSum_eq_marked_cycles, pathCount_eq_sum_pathWeight]
    simp [pathWeight]
  | succ n =>
    rw [pathCount_eq_sum_consecutive_product, sum_path_products_eq_marked_cycles,
      pathConvolutionSum_eq_marked_cycles]
    simp

/-- The manuscript's explicit principal-minor formula for the actual count. -/
theorem pathCount_eq_positive_convolution {n : ℕ} (T : Tournament n) :
    (pathCount T : ℝ) = ∑ U : Finset (Fin n),
      (principalWeightMatrix T U).det *
        ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n)
          Subtype.val).permanent := pathCount_eq_pathConvolutionSum T

theorem principal_weight_le_pathCount {n : ℕ} (T : Tournament n) :
    (principalWeightMatrix T Finset.univ).det ≤ (pathCount T : ℝ) := by
  rw [pathCount_eq_pathConvolutionSum]
  exact principal_weight_le_pathConvolutionSum T

/-- Determinant positivity and the exact positive convolution imply a path exists. -/
theorem pathCount_pos_from_convolution {n : ℕ} (T : Tournament n) : 0 < pathCount T := by
  have h : (0 : ℝ) < pathCount T := by
    rw [pathCount_eq_pathConvolutionSum]
    exact pathConvolutionSum_pos T
  exact_mod_cast h

end TournamentHamiltonian
