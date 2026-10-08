import TournamentHamiltonian.FourBlockPermanent

/-! Weighted cross matchings bounded by unrestricted neighbor choices. -/

namespace TournamentHamiltonian

open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def subsetEnumerationFunction (x : Σ t : Finset β, α ≃ t) : α → β :=
  fun i => x.2 i

omit [Fintype β] [DecidableEq α] in
theorem subsetEnumerationFunction_image (x : Σ t : Finset β, α ≃ t) :
    Finset.univ.image (subsetEnumerationFunction x) = x.1 := by
  ext j
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact (x.2 i).property
  · intro hj
    refine Finset.mem_image.mpr ⟨x.2.symm ⟨j, hj⟩, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val (x.2.apply_symm_apply ⟨j, hj⟩)

omit [Fintype β] [DecidableEq α] in
theorem subsetEnumerationFunction_injective :
    Function.Injective (subsetEnumerationFunction (α := α) (β := β)) := by
  intro x y h
  have ht : x.1 = y.1 := by
    rw [← subsetEnumerationFunction_image x, ← subsetEnumerationFunction_image y, h]
  rcases x with ⟨t, e⟩
  rcases y with ⟨u, f⟩
  dsimp at ht
  subst u
  have he : e = f := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact congrFun h i
  subst f
  rfl

theorem sum_rectangularPermanent_le_prod_sum (B : β → α → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) :
    (∑ t : Finset β, bijectionPermanent (fun (i : t) (j : α) => B i j)) ≤
      ∏ j : α, ∑ i : β, B i j := by
  have h := finite_code_mass_le subsetEnumerationFunction subsetEnumerationFunction_injective
    (fun f : α → β => ∏ j, B (f j) j)
    (fun _ => Finset.prod_nonneg (fun _ _ => hB _ _))
  rw [Fintype.sum_sigma] at h
  exact h.trans_eq (Fintype.prod_sum (fun j i => B i j)).symm

theorem sum_finsets_subtype_eq_powerset (M : Finset α) (f : Finset α → ℝ) :
    (∑ t : Finset M, f (t.map (Function.Embedding.subtype _))) =
      ∑ t ∈ M.powerset, f t := by
  have he := (subsetsOfEquiv M).sum_comp (fun t : {t : Finset α // t ⊆ M} => f t.val)
  change (∑ t : Finset M, f (t.map (Function.Embedding.subtype _))) =
    (∑ t : {t : Finset α // t ⊆ M}, f t.val) at he
  let e : {t : Finset α // t ⊆ M} ≃ M.powerset :=
    (Equiv.refl (Finset α)).subtypeEquiv (fun _ => Finset.mem_powerset.symm)
  have hs := e.sum_comp (fun t : M.powerset => f t.val)
  change (∑ t : {t : Finset α // t ⊆ M}, f t.val) = (∑ t : M.powerset, f t.val) at hs
  exact he.trans (hs.trans (M.powerset.sum_coe_sort f))

theorem sum_selected_row_minors_le (B : Matrix α α ℝ) (cols M : Finset α)
    (hB : ∀ i j, 0 ≤ B i j) :
    (∑ I ∈ M.powerset, selectedPermanent B cols I) ≤
      ∏ j : cols, ∑ i : M, B i j := by
  have h := sum_rectangularPermanent_le_prod_sum (fun (i : M) (j : cols) => B i j)
    (fun _ _ => hB _ _)
  have he : (∑ t : Finset M, bijectionPermanent (fun (i : t) (j : cols) => B i.val.val j)) =
      ∑ t : Finset M, selectedPermanent B cols (t.map (Function.Embedding.subtype _)) := by
    apply Finset.sum_congr rfl
    intro t _
    exact rectangularPermanent_submatrix_equiv
      (fun (i : t.map (Function.Embedding.subtype _)) (j : cols) => B i j)
      (Equiv.refl cols) (t.equivMap (Function.Embedding.subtype _))
  rw [he, sum_finsets_subtype_eq_powerset] at h
  exact h

theorem sum_selected_column_minors_le (B : Matrix α α ℝ) (rows M : Finset α)
    (hB : ∀ i j, 0 ≤ B i j) :
    (∑ J ∈ M.powerset, selectedPermanent B J rows) ≤
      ∏ i : rows, ∑ j : M, B i j := by
  have h := sum_selected_row_minors_le B.transpose rows M (fun i j => hB j i)
  simp_rw [← selectedPermanent_transpose B] at h
  exact h

omit [Fintype α] in
theorem selectedPermanent_nonneg (B : Matrix α α ℝ) (s t : Finset α)
    (hB : ∀ i j, 0 ≤ B i j) : 0 ≤ selectedPermanent B s t :=
  Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => hB _ _))

omit [Fintype α] in
theorem selectedPermanent_row_weight (B : Matrix α α ℝ) (s t : Finset α) (w : α → ℝ) :
    selectedPermanent (fun i j => w i * B i j) s t =
      (∏ i ∈ t, w i) * selectedPermanent B s t := by
  unfold selectedPermanent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.prod_mul_distrib]
  congr 1
  exact (e.prod_comp (fun i : t => w i)).trans (t.prod_coe_sort w)

omit [Fintype α] in
theorem selectedPermanent_column_weight (B : Matrix α α ℝ) (s t : Finset α) (w : α → ℝ) :
    selectedPermanent (fun i j => B i j * w j) s t =
      selectedPermanent B s t * ∏ j ∈ s, w j := by
  unfold selectedPermanent
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.prod_mul_distrib, s.prod_coe_sort]

theorem weighted_cross_row_sum_le (B : Matrix α α ℝ) (cols M : Finset α) (k : ℕ)
    (w : α → ℝ) (hB : ∀ i j, 0 ≤ B i j) (hw : ∀ i, 0 ≤ w i) :
    (∑ I ∈ M.powersetCard k, (∏ i ∈ I, w i) * selectedPermanent B cols I) ≤
      ∏ j : cols, ∑ i : M, w i * B i j := by
  simp_rw [← selectedPermanent_row_weight B]
  apply (Finset.sum_le_sum_of_subset_of_nonneg (fun I hI =>
    Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hI).1)
    (fun I _ _ => selectedPermanent_nonneg _ _ _ (fun i j => mul_nonneg (hw i) (hB i j)))).trans
  exact sum_selected_row_minors_le _ cols M (fun i j => mul_nonneg (hw i) (hB i j))

theorem weighted_cross_column_sum_le (B : Matrix α α ℝ) (rows M : Finset α) (k : ℕ)
    (w : α → ℝ) (hB : ∀ i j, 0 ≤ B i j) (hw : ∀ i, 0 ≤ w i) :
    (∑ J ∈ M.powersetCard k, selectedPermanent B J rows * ∏ j ∈ J, w j) ≤
      ∏ i : rows, ∑ j : M, B i j * w j := by
  simp_rw [← selectedPermanent_column_weight B]
  apply (Finset.sum_le_sum_of_subset_of_nonneg (fun J hJ =>
    Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hJ).1)
    (fun J _ _ => selectedPermanent_nonneg _ _ _ (fun i j => mul_nonneg (hB i j) (hw j)))).trans
  exact sum_selected_column_minors_le _ rows M (fun i j => mul_nonneg (hB i j) (hw j))

theorem rectangularPermanent_le_factorial (B : β → α → ℝ)
    (h0 : ∀ i j, 0 ≤ B i j) (h1 : ∀ i j, B i j ≤ 1) :
    bijectionPermanent B ≤ (Fintype.card α).factorial := by
  by_cases hc : Fintype.card α = Fintype.card β
  · let e : α ≃ β := Fintype.equivOfCardEq hc
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (α ≃ β)))
      (fun f _ => Finset.prod_le_one₀ (s := Finset.univ) (fun i _ => h0 (f i) i) (fun i _ => h1 (f i) i))
    have he : Fintype.card (α ≃ β) = (Fintype.card α).factorial := Fintype.card_equiv e
    simpa [bijectionPermanent, he] using h
  · have : IsEmpty (α ≃ β) := ⟨fun e => hc (Fintype.card_congr e)⟩
    simp [bijectionPermanent]

omit [Fintype α] in
theorem selectedPermanent_le_factorial (B : Matrix α α ℝ) (s t : Finset α)
    (h0 : ∀ i j, 0 ≤ B i j) (h1 : ∀ i j, B i j ≤ 1) :
    selectedPermanent B s t ≤ s.card.factorial := by
  have h := rectangularPermanent_le_factorial (fun (i : t) (j : s) => B i j)
    (fun _ _ => h0 _ _) (fun _ _ => h1 _ _)
  simpa [bijectionPermanent, selectedPermanent] using h

end TournamentHamiltonian
