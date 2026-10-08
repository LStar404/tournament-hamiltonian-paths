import TournamentHamiltonian.Definitions
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.BigOperators.Pi

/-! Exact finite determinant/permanent inverse convolution, using cycle-color
cancellation. Both nontrivial cycles and fixed-point cycles are included.
The conversion from complementary-class permutations to independently
colored whole cycles and the determinant parity bridge are proved here.
The final Hamiltonian path convolution remains a separate coefficient
identification beyond this inverse-convolution lemma. -/

namespace TournamentHamiltonian

open scoped Classical

/-- Including singleton cycles is essential when the matrix has diagonal
entries. `cycleFactorsFinset` alone omits these cycles. -/
abbrev CoverCycles {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :=
  σ.cycleFactorsFinset ⊕ {i : α // σ i = i}

theorem coverCycles_nonempty {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (σ : Equiv.Perm α) : Nonempty (CoverCycles σ) := by
  classical
  obtain ⟨i⟩ := ‹Nonempty α›
  by_cases hi : σ i = i
  · exact ⟨Sum.inr ⟨i, hi⟩⟩
  · exact ⟨Sum.inl ⟨σ.cycleOf i,
      σ.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hi)⟩⟩

noncomputable def coverCycleOf {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (i : α) : CoverCycles σ :=
  if hi : σ i = i then Sum.inr ⟨i, hi⟩
  else Sum.inl ⟨σ.cycleOf i,
    σ.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hi)⟩

theorem coverCycleOf_apply {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (i : α) : coverCycleOf σ (σ i) = coverCycleOf σ i := by
  classical
  by_cases hi : σ i = i
  · rw [hi]
  · have hi' : σ (σ i) ≠ σ i := fun h => hi (σ.injective h)
    simp [coverCycleOf, hi, hi', Equiv.Perm.cycleOf_self_apply]

theorem coverCycleOf_surjective {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) : Function.Surjective (coverCycleOf σ) := by
  classical
  intro k
  cases k with
  | inr i =>
    exact ⟨i.val, by simp [coverCycleOf, i.property]⟩
  | inl c =>
    have hc := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1
    obtain ⟨i, hi⟩ := hc.nonempty_support
    have hiσ : σ i ≠ i := Equiv.Perm.mem_support.mp
      (Equiv.Perm.mem_cycleFactorsFinset_support_le c.property hi)
    refine ⟨i, ?_⟩
    simp only [coverCycleOf, dite_eq_right hiσ]
    congr 2
    exact (Equiv.Perm.cycle_is_cycleOf hi c.property).symm

theorem coverCycleOf_eq_iff_sameCycle {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (i j : α) :
    coverCycleOf σ i = coverCycleOf σ j ↔ σ.SameCycle i j := by
  classical
  by_cases hi : σ i = i <;> by_cases hj : σ j = j
  · simp only [coverCycleOf, dite_eq_left hi, dite_eq_left hj, Sum.inr.injEq, Subtype.mk.injEq]
    exact ⟨fun h => h.sameCycle σ, fun h => h.eq_of_left hi⟩
  · simp only [coverCycleOf, dite_eq_left hi, dite_eq_right hj, Sum.inr_ne_inl, false_iff]
    exact fun h => hj (h.apply_eq_self_iff.mp hi)
  · simp only [coverCycleOf, dite_eq_right hi, dite_eq_left hj, Sum.inl_ne_inr, false_iff]
    exact fun h => hi (h.apply_eq_self_iff.mpr hj)
  · simp only [coverCycleOf, dite_eq_right hi, dite_eq_right hj, Sum.inl.injEq, Subtype.mk.injEq]
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
      (Equiv.Perm.mem_support.mpr hi) (Equiv.Perm.mem_support.mpr hj)).symm

theorem invariant_color_sameCycle {α β : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (f : α → β) (hf : ∀ i, f (σ i) = f i)
    {i j : α} (hij : σ.SameCycle i j) : f i = f j := by
  obtain ⟨k, hk⟩ := hij.exists_nat_pow_eq
  have hp : ∀ k : ℕ, f ((σ ^ k) i) = f i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, hf, ih]
  rw [← hk]
  exact (hp k).symm

/-- Coloring permutation cycles is exactly the same finite object as coloring
vertices invariantly under the permutation. This is the reindexing needed
when the determinant subset and its complement are joined into one cover. -/
noncomputable def cycleColoringEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    (CoverCycles σ → Bool) ≃ {f : α → Bool // ∀ i, f (σ i) = f i} := by
  classical
  let toFun : (CoverCycles σ → Bool) → {f : α → Bool // ∀ i, f (σ i) = f i} :=
    fun colors => ⟨fun i => colors (coverCycleOf σ i),
      fun i => congrArg colors (coverCycleOf_apply σ i)⟩
  apply Equiv.ofBijective toFun
  constructor
  · intro c d h
    funext k
    obtain ⟨i, hi⟩ := coverCycleOf_surjective σ k
    have hh := congrArg (fun f : {f : α → Bool // ∀ i, f (σ i) = f i} => f.val i) h
    change c (coverCycleOf σ i) = d (coverCycleOf σ i) at hh
    simpa [hi] using hh
  · intro f
    let rep (k : CoverCycles σ) := Classical.choose (coverCycleOf_surjective σ k)
    have hrep (k : CoverCycles σ) : coverCycleOf σ (rep k) = k :=
      Classical.choose_spec (coverCycleOf_surjective σ k)
    refine ⟨fun k => f.val (rep k), ?_⟩
    apply Subtype.ext
    funext i
    change f.val (rep (coverCycleOf σ i)) = f.val i
    exact invariant_color_sameCycle σ f.val f.property
      ((coverCycleOf_eq_iff_sameCycle σ _ _).mp (hrep _))

/-- For a fixed coloring, permutations on its two color classes glue
bijectively to exactly the permutations preserving that coloring. -/
noncomputable def colorClassPermEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → Bool) :
    (Equiv.Perm {i : α // f i = true} × Equiv.Perm {i : α // f i ≠ true}) ≃
      {σ : Equiv.Perm α // ∀ i, f (σ i) = f i} where
  toFun pq := ⟨pq.1.subtypeCongr pq.2, by
    intro i
    by_cases hi : f i = true
    · rw [Equiv.Perm.subtypeCongr.left_apply (p := fun i : α => f i = true)
        (a := i) pq.1 pq.2 hi]
      exact (pq.1 ⟨i, hi⟩).property.trans hi.symm
    · rw [Equiv.Perm.subtypeCongr.right_apply (p := fun i : α => f i = true)
        (a := i) pq.1 pq.2 hi]
      have hq := (pq.2 ⟨i, hi⟩).property
      cases hfi : f i <;> cases hfq : f (pq.2 ⟨i, hi⟩).val <;> simp_all⟩
  invFun σ :=
    (σ.val.subtypePerm (fun i => by rw [σ.property i]),
      σ.val.subtypePerm (fun i => by rw [σ.property i]))
  left_inv pq := by
    apply Prod.ext
    · apply Equiv.ext
      intro i
      apply Subtype.ext
      simp only [Equiv.Perm.subtypePerm_apply, Equiv.Perm.subtypeCongr.left_apply_subtype]
    · apply Equiv.ext
      intro i
      apply Subtype.ext
      simp only [Equiv.Perm.subtypePerm_apply, Equiv.Perm.subtypeCongr.right_apply_subtype]
  right_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    rw [Equiv.Perm.subtypeCongr.apply]
    split_ifs <;> rfl

noncomputable def swapInvariantColoring {α : Type*} :
    (Σ f : α → Bool, {σ : Equiv.Perm α // ∀ i, f (σ i) = f i}) ≃
      (Σ σ : Equiv.Perm α, {f : α → Bool // ∀ i, f (σ i) = f i}) where
  toFun x := ⟨x.2.val, ⟨x.1, x.2.property⟩⟩
  invFun x := ⟨x.2.val, ⟨x.1, x.2.property⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- The complete finite reindexing of pairs of permutations on complementary
vertex color classes as one permutation with independently colored cycles. -/
noncomputable def coloredCoverEquiv {α : Type*} [Fintype α] [DecidableEq α] :
    (Σ f : α → Bool,
      Equiv.Perm {i : α // f i = true} × Equiv.Perm {i : α // f i ≠ true}) ≃
      (Σ σ : Equiv.Perm α, CoverCycles σ → Bool) :=
  (Equiv.sigmaCongrRight colorClassPermEquiv).trans
    (swapInvariantColoring.trans
      (Equiv.sigmaCongrRight fun σ => (cycleColoringEquiv σ).symm))

theorem colorClass_product_eq_cover_product {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℝ) (f : α → Bool)
    (p : Equiv.Perm {i : α // f i = true})
    (q : Equiv.Perm {i : α // f i ≠ true}) :
    (∏ i : {i : α // f i = true}, A (p i).val i.val) *
      (∏ i : {i : α // f i ≠ true}, A (q i).val i.val) =
        ∏ i : α, A ((p.subtypeCongr q) i) i := by
  let g : {i : α // f i = true} ⊕ {i : α // f i ≠ true} → ℝ :=
    Sum.elim (fun i => A (p i).val i.val) (fun i => A (q i).val i.val)
  calc
    _ = ∏ k, g k := (Fintype.prod_sum_type g).symm
    _ = _ := by
      apply Fintype.prod_equiv (Equiv.sumCompl (fun i : α => f i = true))
      intro k
      cases k <;> simp [g]

theorem cycleColoringEquiv_symm_apply_cycleOf {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) (f : α → Bool)
    (hf : ∀ i, f (σ i) = f i) (i : α) :
    (cycleColoringEquiv σ).symm ⟨f, hf⟩ (coverCycleOf σ i) = f i := by
  have h := (cycleColoringEquiv σ).apply_symm_apply ⟨f, hf⟩
  exact congrArg (fun q : {f : α → Bool // ∀ i, f (σ i) = f i} => q.val i) h

theorem subtypePerm_pow_val {α : Type*} (σ : Equiv.Perm α) (p : α → Prop)
    (hp : ∀ i, p (σ i) ↔ p i) (x : {i : α // p i}) (k : ℕ) :
    (((σ.subtypePerm hp) ^ k) x).val = (σ ^ k) x.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.subtypePerm_apply]
    exact congrArg σ ih

theorem subtypePerm_sameCycle_iff {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ i, p (σ i) ↔ p i) (x y : {i : α // p i}) :
    (σ.subtypePerm hp).SameCycle x y ↔ σ.SameCycle x.val y.val := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    refine ⟨(k : ℤ), ?_⟩
    rw [zpow_natCast]
    exact (subtypePerm_pow_val σ p hp x k).symm.trans (congrArg Subtype.val hk)
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    refine ⟨(k : ℤ), ?_⟩
    rw [zpow_natCast]
    apply Subtype.ext
    exact (subtypePerm_pow_val σ p hp x k).trans hk

noncomputable def coverCycleRep {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (k : CoverCycles σ) : α :=
  Classical.choose (coverCycleOf_surjective σ k)

theorem coverCycleRep_index {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (k : CoverCycles σ) :
    coverCycleOf σ (coverCycleRep σ k) = k :=
  Classical.choose_spec (coverCycleOf_surjective σ k)

/-- Cycles of an invariant restriction correspond exactly to whole cycles
of the original permutation selected by that restriction. -/
noncomputable def restrictionCyclesEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ i, p (σ i) ↔ p i) :
    CoverCycles (σ.subtypePerm hp) ≃ {k : CoverCycles σ // p (coverCycleRep σ k)} := by
  classical
  let τ := σ.subtypePerm hp
  let g : CoverCycles τ → {k : CoverCycles σ // p (coverCycleRep σ k)} := fun c =>
    ⟨coverCycleOf σ (coverCycleRep τ c).val, by
      have hsame := (coverCycleOf_eq_iff_sameCycle σ _ _).mp
        (coverCycleRep_index σ (coverCycleOf σ (coverCycleRep τ c).val))
      have heq := invariant_color_sameCycle σ p (fun i => propext (hp i)) hsame
      exact heq.mpr (coverCycleRep τ c).property⟩
  apply Equiv.ofBijective g
  constructor
  · intro c d h
    have hh := congrArg Subtype.val h
    change coverCycleOf σ (coverCycleRep τ c).val =
      coverCycleOf σ (coverCycleRep τ d).val at hh
    have hs := (subtypePerm_sameCycle_iff σ p hp _ _).mpr
      ((coverCycleOf_eq_iff_sameCycle σ _ _).mp hh)
    have hi := (coverCycleOf_eq_iff_sameCycle τ _ _).mpr hs
    simpa only [coverCycleRep_index] using hi
  · intro k
    let x : {i : α // p i} := ⟨coverCycleRep σ k.val, k.property⟩
    refine ⟨coverCycleOf τ x, ?_⟩
    apply Subtype.ext
    change coverCycleOf σ (coverCycleRep τ (coverCycleOf τ x)).val = k.val
    have hs := (coverCycleOf_eq_iff_sameCycle τ _ _).mp
      (coverCycleRep_index τ (coverCycleOf τ x))
    have hg := (subtypePerm_sameCycle_iff σ p hp _ _).mp hs
    exact ((coverCycleOf_eq_iff_sameCycle σ _ _).mpr hg).trans
      (coverCycleRep_index σ k.val)

/-- Every independently colored nonempty family of cycles cancels when the
two colors have weights `1` and `-1`. -/
theorem sum_cycle_colors_eq_zero {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] :
    (∑ c : κ → Bool, ∏ i : κ, if c i then (-1 : ℝ) else 1) = 0 := by
  rw [← Fintype.prod_sum (fun (_ : κ) (b : Bool) => if b then (-1 : ℝ) else 1)]
  simp [Fintype.univ_bool]

/-- The sign of a determinant cycle, combined with one negative matrix
factor at each vertex, is exactly `-1`, regardless of the cycle length. -/
theorem determinant_cycle_weight_eq_neg_one {α : Type*} [Fintype α]
    [DecidableEq α] (c : Equiv.Perm α) (hc : c.IsCycle) :
    (-1 : ℝ) ^ c.support.card * ((Equiv.Perm.sign c : ℤ) : ℝ) = -1 := by
  have hs : ((Equiv.Perm.sign c : ℤ) : ℝ) = -(-1 : ℝ) ^ c.support.card := by
    rw [hc.sign]
    simp
  rw [hs, mul_neg, ← mul_pow]
  norm_num

theorem coverCycles_card {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    Fintype.card (CoverCycles σ) = σ.cycleType.card +
      (Fintype.card α - σ.support.card) := by
  have hfixed : Fintype.card {i : α // σ i = i} =
      Fintype.card α - σ.support.card := by
    change Fintype.card (Function.fixedPoints σ) = _
    rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]
  simp only [CoverCycles, Fintype.card_sum, Fintype.card_coe, hfixed,
    Equiv.Perm.cycleType_def, Multiset.card_map, Finset.card_val]

/-- The complete determinant parity factor is one `-1` per cycle, including
singleton cycles. This is the sign needed in the determinant/permanent inverse
convolution rather than only the ordinary permutation sign. -/
theorem determinant_cover_weight_eq_cycle_parity {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) :
    (-1 : ℝ) ^ Fintype.card α * ((Equiv.Perm.sign σ : ℤ) : ℝ) =
      (-1 : ℝ) ^ Fintype.card (CoverCycles σ) := by
  have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ) =
      (-1 : ℝ) ^ (σ.support.card + σ.cycleType.card) := by
    rw [Equiv.Perm.sign_of_cycleType]
    simp [Equiv.Perm.sum_cycleType]
  have hn : Fintype.card α + (σ.support.card + σ.cycleType.card) =
      2 * σ.support.card + Fintype.card (CoverCycles σ) := by
    rw [coverCycles_card]
    have hle := Finset.card_le_univ σ.support
    omega
  rw [hs, ← pow_add, hn, pow_add, pow_mul]
  norm_num

theorem prod_color_sign_eq_card {κ : Type*} [Fintype κ] [DecidableEq κ]
    (colors : κ → Bool) :
    (∏ k : κ, if colors k then (-1 : ℝ) else 1) =
      (-1 : ℝ) ^ Fintype.card {k : κ // colors k = true} := by
  rw [Fintype.subtype_card]
  rw [← Finset.prod_filter]
  simp

/-- The determinant sign of an invariant principal restriction is exactly
the product of the `-1` weights of its selected whole cycles. -/
theorem restriction_determinant_weight_eq_colors {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) (f : α → Bool)
    (hf : ∀ i, f (σ i) = f i) :
    (-1 : ℝ) ^ Fintype.card {i : α // f i = true} *
        ((Equiv.Perm.sign (σ.subtypePerm (p := fun i => f i = true)
          (fun i => by rw [hf i])) : ℤ) : ℝ) =
      ∏ k : CoverCycles σ,
        if (cycleColoringEquiv σ).symm ⟨f, hf⟩ k then (-1 : ℝ) else 1 := by
  let colors := (cycleColoringEquiv σ).symm ⟨f, hf⟩
  have hc (k : CoverCycles σ) : colors k = f (coverCycleRep σ k) := by
    have h := cycleColoringEquiv_symm_apply_cycleOf σ f hf (coverCycleRep σ k)
    simpa only [coverCycleRep_index] using h
  let hp : ∀ i, (f (σ i) = true) ↔ (f i = true) := fun i => by rw [hf i]
  have hcard : Fintype.card (CoverCycles (σ.subtypePerm (p := fun i => f i = true) hp)) =
      Fintype.card {k : CoverCycles σ // colors k = true} := by
    apply Fintype.card_congr
    exact (restrictionCyclesEquiv σ (fun i => f i = true) hp).trans
      (Equiv.subtypeEquivRight fun k => by rw [hc k])
  calc
    _ = (-1 : ℝ) ^ Fintype.card
        (CoverCycles (σ.subtypePerm (p := fun i => f i = true) hp)) :=
      determinant_cover_weight_eq_cycle_parity _
    _ = (-1 : ℝ) ^ Fintype.card {k : CoverCycles σ // colors k = true} :=
      congrArg (fun n : ℕ => (-1 : ℝ) ^ n) hcard
    _ = _ := (prod_color_sign_eq_card colors).symm

/-- A fixed permutation's full adjacency product is unchanged by choosing
which of its cycles lie in the determinant factor. Thus the corresponding
cycle-color sum vanishes for every nonempty vertex set. -/
theorem signed_cycle_cover_sum_eq_zero {α : Type*} [Fintype α]
    [DecidableEq α] [Nonempty α] (A : Matrix α α ℝ) (σ : Equiv.Perm α) :
    (∑ colors : CoverCycles σ → Bool,
      (∏ k : CoverCycles σ, if colors k then (-1 : ℝ) else 1) *
        ∏ i, A (σ i) i) = 0 := by
  have : Nonempty (CoverCycles σ) := coverCycles_nonempty σ
  have hzero := sum_cycle_colors_eq_zero (κ := CoverCycles σ)
  calc
    _ = (∑ colors : CoverCycles σ → Bool,
        ∏ k : CoverCycles σ, if colors k then (-1 : ℝ) else 1) *
          (∏ i : α, A (σ i) i) := (Finset.sum_mul ..).symm
    _ = 0 := by
      simpa only [zero_mul] using congrArg (fun q : ℝ => q * (∏ i : α, A (σ i) i)) hzero

/-- Summing the determinant parity over all invariant vertex colorings
vanishes. The statement uses the actual restriction permutation and its
ordinary sign, not a separately postulated cycle sign. -/
theorem sum_invariant_determinant_sign_eq_zero {α : Type*} [Fintype α]
    [DecidableEq α] [Nonempty α] (σ : Equiv.Perm α) :
    (∑ f : {f : α → Bool // ∀ i, f (σ i) = f i},
      (-1 : ℝ) ^ Fintype.card {i : α // f.val i = true} *
        ((Equiv.Perm.sign (σ.subtypePerm (p := fun i => f.val i = true)
          (fun i => by rw [f.property i])) : ℤ) : ℝ)) = 0 := by
  have : Nonempty (CoverCycles σ) := coverCycles_nonempty σ
  calc
    _ = ∑ colors : CoverCycles σ → Bool,
        ∏ k : CoverCycles σ, if colors k then (-1 : ℝ) else 1 := by
      symm
      apply Fintype.sum_equiv (cycleColoringEquiv σ)
      intro colors
      have h := restriction_determinant_weight_eq_colors σ
        ((cycleColoringEquiv σ) colors).val ((cycleColoringEquiv σ) colors).property
      change _ = ∏ k : CoverCycles σ,
        if (cycleColoringEquiv σ).symm ((cycleColoringEquiv σ) colors) k
          then (-1 : ℝ) else 1 at h
      rw [Equiv.symm_apply_apply] at h
      exact h.symm
    _ = 0 := sum_cycle_colors_eq_zero

theorem det_per_colorClass_eq_sum_preserving {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℝ) (f : α → Bool) :
    ((-A).submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
      (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent =
    ∑ σ : {σ : Equiv.Perm α // ∀ i, f (σ i) = f i},
      ((-1 : ℝ) ^ Fintype.card {i : α // f i = true} *
        ((Equiv.Perm.sign (σ.val.subtypePerm (p := fun i => f i = true)
          (fun i => by rw [σ.property i])) : ℤ) : ℝ)) * ∏ i, A (σ.val i) i := by
  let term (pq : Equiv.Perm {i : α // f i = true} ×
      Equiv.Perm {i : α // f i ≠ true}) : ℝ :=
    ((-1 : ℝ) ^ Fintype.card {i : α // f i = true} *
      ((Equiv.Perm.sign pq.1 : ℤ) : ℝ)) *
      ((∏ i : {i : α // f i = true}, A (pq.1 i).val i.val) *
        ∏ i : {i : α // f i ≠ true}, A (pq.2 i).val i.val)
  calc
    _ = ∑ p : Equiv.Perm {i : α // f i = true},
        ∑ q : Equiv.Perm {i : α // f i ≠ true}, term (p, q) := by
      change (-A.submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
        (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent = _
      rw [Matrix.det_neg, Matrix.det_apply']
      simp only [Matrix.permanent, Finset.mul_sum, Finset.sum_mul, Matrix.submatrix_apply,
        term, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ pq, term pq := (Fintype.sum_prod_type term).symm
    _ = _ := by
      apply Fintype.sum_equiv (colorClassPermEquiv f)
      intro pq
      have hr : ((colorClassPermEquiv f) pq).val.subtypePerm
          (p := fun i => f i = true)
          (fun i => by rw [((colorClassPermEquiv f) pq).property i]) = pq.1 := by
        apply Equiv.ext
        intro i
        apply Subtype.ext
        change (pq.1.subtypeCongr pq.2) i.val = (pq.1 i).val
        exact Equiv.Perm.subtypeCongr.left_apply_subtype pq.1 pq.2 i
      change term pq = _
      rw [hr]
      change term pq = ((-1 : ℝ) ^ Fintype.card {i : α // f i = true} *
        ((Equiv.Perm.sign pq.1 : ℤ) : ℝ)) * ∏ i : α, A ((pq.1.subtypeCongr pq.2) i) i
      rw [← colorClass_product_eq_cover_product A f pq.1 pq.2]

noncomputable def invariantCoverWeight {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (σ : Equiv.Perm α)
    (f : {f : α → Bool // ∀ i, f (σ i) = f i}) : ℝ :=
  ((-1 : ℝ) ^ Fintype.card {i : α // f.val i = true} *
    ((Equiv.Perm.sign (σ.subtypePerm (p := fun i => f.val i = true)
      (fun i => by rw [f.property i])) : ℤ) : ℝ)) * ∏ i, A (σ i) i

set_option maxHeartbeats 1000000 in
/-- The squarefree determinant/permanent inverse identity, expressed using
Boolean vertex subsets. This already performs the full cycle cancellation. -/
theorem det_per_inverse_convolution_bool {α : Type*} [Fintype α]
    [DecidableEq α] [Nonempty α] (A : Matrix α α ℝ) :
    (∑ f : α → Bool,
      ((-A).submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
        (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent) = 0 := by
  calc
    _ = ∑ f : α → Bool, ∑ σ : {σ : Equiv.Perm α // ∀ i, f (σ i) = f i},
        invariantCoverWeight A σ.val ⟨f, σ.property⟩ := by
      apply Finset.sum_congr rfl
      intro f _
      exact det_per_colorClass_eq_sum_preserving A f
    _ = ∑ x : (Σ f : α → Bool, {σ : Equiv.Perm α // ∀ i, f (σ i) = f i}),
        invariantCoverWeight A x.2.val ⟨x.1, x.2.property⟩ :=
      (Fintype.sum_sigma (fun x : (Σ f : α → Bool,
        {σ : Equiv.Perm α // ∀ i, f (σ i) = f i}) =>
          invariantCoverWeight A x.2.val ⟨x.1, x.2.property⟩)).symm
    _ = ∑ x : (Σ σ : Equiv.Perm α, {f : α → Bool // ∀ i, f (σ i) = f i}),
        invariantCoverWeight A x.1 x.2 := by
      apply Fintype.sum_equiv swapInvariantColoring
      intro x
      rfl
    _ = ∑ σ : Equiv.Perm α,
        ∑ f : {f : α → Bool // ∀ i, f (σ i) = f i}, invariantCoverWeight A σ f :=
      Fintype.sum_sigma (fun x : (Σ σ : Equiv.Perm α,
        {f : α → Bool // ∀ i, f (σ i) = f i}) => invariantCoverWeight A x.1 x.2)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro σ _
      unfold invariantCoverWeight
      rw [← Finset.sum_mul]
      simpa only [zero_mul] using congrArg (fun r : ℝ => r * (∏ i, A (σ i) i))
        (sum_invariant_determinant_sign_eq_zero σ)

/-- The empty-order inverse coefficient is one; all nonempty coefficients
are zero. No assumption that the matrix is loopless is used. -/
theorem det_per_inverse_convolution_bool_all {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℝ) :
    (∑ f : α → Bool,
      ((-A).submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
        (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent) =
      if Fintype.card α = 0 then 1 else 0 := by
  by_cases hc : Fintype.card α = 0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hc
    simp [Matrix.det_isEmpty, Matrix.permanent_isEmpty]
  · have : Nonempty α := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hc)
    rw [det_per_inverse_convolution_bool]
    simp [hc]

theorem permanent_submatrix_equiv_self {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (M : Matrix ι ι ℝ) (e : κ ≃ ι) :
    (M.submatrix e e).permanent = M.permanent := by
  unfold Matrix.permanent
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  apply Fintype.prod_equiv e
  intro i
  simp [Equiv.permCongr_apply]

noncomputable def vertexSubsetEquivBool {α : Type*} [Fintype α] [DecidableEq α] :
    Finset α ≃ (α → Bool) where
  toFun U i := decide (i ∈ U)
  invFun f := Finset.univ.filter (fun i => f i = true)
  left_inv U := by ext i; simp
  right_inv f := by funext i; cases h : f i <;> simp [h]

/-- The same inverse convolution with the exact principal-submatrix Finset
indices used throughout the tournament manuscript. -/
theorem det_per_inverse_convolution {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) :
    (∑ U : Finset α,
      ((-A).submatrix (Subtype.val : U → α) Subtype.val).det *
        (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent) =
      if Fintype.card α = 0 then 1 else 0 := by
  calc
    _ = ∑ f : α → Bool,
      ((-A).submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
        (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent := by
      apply Fintype.sum_equiv vertexSubsetEquivBool
      intro U
      let ep : {i : α // vertexSubsetEquivBool U i = true} ≃ U :=
        Equiv.subtypeEquivRight (fun i => by simp [vertexSubsetEquivBool])
      let en : {i : α // vertexSubsetEquivBool U i ≠ true} ≃ (Uᶜ : Finset α) :=
        Equiv.subtypeEquivRight (fun i => by simp [vertexSubsetEquivBool])
      have hp : ((-A).submatrix (Subtype.val : {i : α // vertexSubsetEquivBool U i = true} → α)
          Subtype.val).det = ((-A).submatrix (Subtype.val : U → α) Subtype.val).det :=
        Matrix.det_submatrix_equiv_self ep
          ((-A).submatrix (Subtype.val : U → α) Subtype.val)
      have hn : (A.submatrix (Subtype.val : {i : α // vertexSubsetEquivBool U i ≠ true} → α)
          Subtype.val).permanent =
          (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent :=
        permanent_submatrix_equiv_self
          (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val) en
      rw [hp, hn]
    _ = _ := det_per_inverse_convolution_bool_all A

end TournamentHamiltonian
