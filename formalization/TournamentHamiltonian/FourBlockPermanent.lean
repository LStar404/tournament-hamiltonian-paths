import TournamentHamiltonian.PermanentExpansion
import TournamentHamiltonian.DegreeDeletion

/-! Exact rectangular and four-block permanent decompositions. -/

namespace TournamentHamiltonian

open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {α β R : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  [CommSemiring R]

noncomputable def bijectionPermanent (B : β → α → R) : R :=
  ∑ e : α ≃ β, ∏ i : α, B (e i) i

noncomputable def splitBijectionGlue (s : Finset α) (t : Finset β)
    (e : s ≃ t) (f : {i // i ∉ s} ≃ {i // i ∉ t}) : α ≃ β :=
  (Equiv.sumCompl (fun i : α => i ∈ s)).symm.trans
    ((Equiv.sumCongr e f).trans (Equiv.sumCompl (fun i : β => i ∈ t)))

omit [Fintype α] [Fintype β] in
theorem splitBijectionGlue_mem (s : Finset α) (t : Finset β)
    (e : s ≃ t) (f : {i // i ∉ s} ≃ {i // i ∉ t}) (i : s) :
    splitBijectionGlue s t e f i = e i := by
  simp [splitBijectionGlue]

omit [Fintype α] [Fintype β] in
theorem splitBijectionGlue_notMem (s : Finset α) (t : Finset β)
    (e : s ≃ t) (f : {i // i ∉ s} ≃ {i // i ∉ t}) (i : {i // i ∉ s}) :
    splitBijectionGlue s t e f i = f i := by
  simp [splitBijectionGlue, Equiv.sumCompl_symm_apply_neg]

omit [Fintype α] [Fintype β] in
theorem splitBijectionGlue_image (s : Finset α) (t : Finset β)
    (e : s ≃ t) (f : {i // i ∉ s} ≃ {i // i ∉ t}) :
    s.image (splitBijectionGlue s t e f) = t := by
  ext j
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    rw [splitBijectionGlue_mem s t e f ⟨i, hi⟩]
    exact (e ⟨i, hi⟩).property
  · intro hj
    refine Finset.mem_image.mpr ⟨e.symm ⟨j, hj⟩, (e.symm ⟨j, hj⟩).property, ?_⟩
    rw [splitBijectionGlue_mem]
    simp

noncomputable def splitBijectionEquiv (s : Finset α) :
    (Σ t : Finset β, (s ≃ t) × ({i // i ∉ s} ≃ {i // i ∉ t})) ≃ (α ≃ β) :=
  Equiv.ofBijective (fun x => splitBijectionGlue s x.1 x.2.1 x.2.2) (by
    constructor
    · intro x y h
      change splitBijectionGlue s x.1 x.2.1 x.2.2 = splitBijectionGlue s y.1 y.2.1 y.2.2 at h
      have ht : x.1 = y.1 := by
        rw [← splitBijectionGlue_image s x.1 x.2.1 x.2.2,
          ← splitBijectionGlue_image s y.1 y.2.1 y.2.2, h]
      rcases x with ⟨t, e, f⟩
      rcases y with ⟨u, e', f'⟩
      dsimp at ht
      subst u
      have he : e = e' := by
        apply Equiv.ext
        intro i
        apply Subtype.ext
        simpa only [splitBijectionGlue_mem] using congrArg (fun σ => σ i) h
      have hf : f = f' := by
        apply Equiv.ext
        intro i
        apply Subtype.ext
        simpa only [splitBijectionGlue_notMem] using congrArg (fun σ => σ i) h
      subst e'
      subst f'
      rfl
    · intro σ
      let t := s.image σ
      have hm (i : α) : i ∈ s ↔ σ i ∈ t := by
        simp [t, Finset.mem_image, σ.injective.eq_iff]
      let e : s ≃ t := σ.subtypeEquiv hm
      let f : {i // i ∉ s} ≃ {i // i ∉ t} := σ.subtypeEquiv (fun i => not_congr (hm i))
      refine ⟨⟨t, e, f⟩, ?_⟩
      apply Equiv.ext
      intro i
      by_cases hi : i ∈ s
      · simpa [e] using splitBijectionGlue_mem s t e f ⟨i, hi⟩
      · simpa [f] using splitBijectionGlue_notMem s t e f ⟨i, hi⟩)

theorem rectangularPermanent_laplace (B : β → α → R) (s : Finset α) :
    bijectionPermanent B = ∑ t : Finset β,
      bijectionPermanent (fun (i : t) (j : s) => B i j) *
        bijectionPermanent (fun (i : {i // i ∉ t}) (j : {j // j ∉ s}) => B i j) := by
  unfold bijectionPermanent
  rw [← (splitBijectionEquiv (β := β) s).sum_comp (fun e : α ≃ β => ∏ i, B (e i) i)]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  change (∏ i, B (splitBijectionGlue s t e f i) i) =
    (∏ i : s, B (e i) i) * ∏ i : {i // i ∉ s}, B (f i) i
  have he := Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ s)
    (fun i => B (splitBijectionGlue s t e f i) i)
  simp only [splitBijectionGlue_mem, splitBijectionGlue_notMem] at he
  have hu : @Finset.univ s (Subtype.fintype (fun i => i ∈ s)) =
      @Finset.univ s (Finset.Subtype.fintype s) := by ext i; simp
  rw [hu] at he
  exact he.symm

theorem rectangularPermanent_transpose (B : β → α → R) :
    bijectionPermanent B = bijectionPermanent (fun j i => B i j) := by
  unfold bijectionPermanent
  apply Fintype.sum_equiv (Equiv.symmEquiv α β)
  intro e
  apply Fintype.prod_equiv e
  intro i
  simp

theorem rectangularPermanent_row_laplace (B : β → α → R) (t : Finset β) :
    bijectionPermanent B = ∑ s : Finset α,
      bijectionPermanent (fun (i : t) (j : s) => B i j) *
        bijectionPermanent (fun (i : {i // i ∉ t}) (j : {j // j ∉ s}) => B i j) := by
  rw [rectangularPermanent_transpose B, rectangularPermanent_laplace _ t]
  apply Finset.sum_congr rfl
  intro s _
  rw [rectangularPermanent_transpose (fun (j : s) (i : t) => B i j),
    rectangularPermanent_transpose (fun (j : {j // j ∉ s}) (i : {i // i ∉ t}) => B i j)]

theorem rectangularPermanent_submatrix_equiv {α' β' : Type*}
    [Fintype α'] [Fintype β'] [DecidableEq α'] [DecidableEq β']
    (B : β → α → R) (eα : α' ≃ α) (eβ : β' ≃ β) :
    bijectionPermanent (fun i j => B (eβ i) (eα j)) = bijectionPermanent B := by
  unfold bijectionPermanent
  apply Fintype.sum_equiv (Equiv.equivCongr eα eβ)
  intro e
  apply Fintype.prod_equiv eα
  intro i
  simp

noncomputable def subsetsOfEquiv (s : Finset α) : Finset s ≃ {t : Finset α // t ⊆ s} where
  toFun t := ⟨t.map (Function.Embedding.subtype _), fun x hx => t.property_of_mem_map_subtype hx⟩
  invFun t := t.val.subtype (fun i => i ∈ s)
  left_inv t := by
    ext i
    simp
  right_inv t := by
    apply Subtype.ext
    exact Finset.subtype_map_of_mem (fun _ hx => t.property hx)

noncomputable def memberSubsetEquiv (s t : Finset α) (ht : t ⊆ s) :
    (t.subtype (fun i => i ∈ s)) ≃ t where
  toFun i := ⟨i.val.val, Finset.mem_subtype.mp i.property⟩
  invFun i := ⟨⟨i.val, ht i.property⟩, Finset.mem_subtype.mpr i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def memberComplementSubsetEquiv (s t : Finset α) :
    {i : s // i ∉ t.subtype (fun i => i ∈ s)} ≃ (s \ t : Finset α) where
  toFun i := ⟨i.val.val, Finset.mem_sdiff.mpr ⟨i.val.property,
    fun h => i.property (Finset.mem_subtype.mpr h)⟩⟩
  invFun i := ⟨⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩,
    fun h => (Finset.mem_sdiff.mp i.property).2 (by simpa only [Finset.mem_subtype] using h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def flatFinsetComplementEquiv (s : Finset α) (t : Finset s) :
    {i : s // i ∉ t} ≃ (s \ t.map (Function.Embedding.subtype _) : Finset α) where
  toFun i := ⟨i.val.val, by
    refine Finset.mem_sdiff.mpr ⟨i.val.property, ?_⟩
    simpa using i.property⟩
  invFun i := ⟨⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩, by
    intro ht
    apply (Finset.mem_sdiff.mp i.property).2
    exact Finset.mem_map.mpr ⟨⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩, ht, rfl⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem selectedPermanent_laplace (B : Matrix α α R) (cols rows s : Finset α) (hs : s ⊆ cols) :
    selectedPermanent B cols rows = ∑ t ∈ rows.powerset,
      selectedPermanent B s t * selectedPermanent B (cols \ s) (rows \ t) := by
  change bijectionPermanent (fun (i : rows) (j : cols) => B i j) = _
  rw [rectangularPermanent_laplace _ (s.subtype (fun i => i ∈ cols))]
  have he : (∑ t : Finset rows,
      bijectionPermanent (fun (i : t) (j : s.subtype (fun i => i ∈ cols)) => B i.val.val j.val.val) *
        bijectionPermanent (fun (i : {i : rows // i ∉ t})
          (j : {j : cols // j ∉ s.subtype (fun i => i ∈ cols)}) => B i.val.val j.val.val)) =
      ∑ t : Finset rows,
        selectedPermanent B s (t.map (Function.Embedding.subtype _)) *
          selectedPermanent B (cols \ s) (rows \ t.map (Function.Embedding.subtype _)) := by
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    · exact rectangularPermanent_submatrix_equiv (fun (i : t.map (Function.Embedding.subtype _)) (j : s) => B i j)
        (memberSubsetEquiv cols s hs) (t.equivMap (Function.Embedding.subtype _))
    · exact rectangularPermanent_submatrix_equiv
        (fun (i : (rows \ t.map (Function.Embedding.subtype _) : Finset α)) (j : (cols \ s : Finset α)) => B i j)
        (memberComplementSubsetEquiv cols s) (flatFinsetComplementEquiv rows t)
  rw [he]
  have hh := (subsetsOfEquiv rows).sum_comp (fun t : {t : Finset α // t ⊆ rows} =>
    selectedPermanent B s t.val * selectedPermanent B (cols \ s) (rows \ t.val))
  change (∑ t : Finset rows,
    selectedPermanent B s (t.map (Function.Embedding.subtype _)) *
      selectedPermanent B (cols \ s) (rows \ t.map (Function.Embedding.subtype _))) =
      (∑ t : {t : Finset α // t ⊆ rows},
        selectedPermanent B s t.val * selectedPermanent B (cols \ s) (rows \ t.val)) at hh
  rw [hh]
  let e : {t : Finset α // t ⊆ rows} ≃ rows.powerset :=
    (Equiv.refl (Finset α)).subtypeEquiv (fun t => Finset.mem_powerset.symm)
  have hsum := e.sum_comp (fun t : rows.powerset =>
    selectedPermanent B s t.val * selectedPermanent B (cols \ s) (rows \ t.val))
  change (∑ t : {t : Finset α // t ⊆ rows},
    selectedPermanent B s t.val * selectedPermanent B (cols \ s) (rows \ t.val)) =
    (∑ t : rows.powerset, selectedPermanent B s t.val *
      selectedPermanent B (cols \ s) (rows \ t.val)) at hsum
  exact hsum.trans (rows.powerset.sum_coe_sort (fun t =>
    selectedPermanent B s t * selectedPermanent B (cols \ s) (rows \ t)))

omit [Fintype α] in
theorem selectedPermanent_transpose (B : Matrix α α R) (cols rows : Finset α) :
    selectedPermanent B cols rows = selectedPermanent B.transpose rows cols :=
  rectangularPermanent_transpose (fun (i : rows) (j : cols) => B i j)

theorem selectedPermanent_row_laplace (B : Matrix α α R) (cols rows t : Finset α)
    (ht : t ⊆ rows) :
    selectedPermanent B cols rows = ∑ s ∈ cols.powerset,
      selectedPermanent B s t * selectedPermanent B (cols \ s) (rows \ t) := by
  rw [selectedPermanent_transpose B, selectedPermanent_laplace B.transpose rows cols t ht]
  apply Finset.sum_congr rfl
  intro s _
  rw [← selectedPermanent_transpose B s t,
    ← selectedPermanent_transpose B (cols \ s) (rows \ t)]

noncomputable def finsetUnivEquiv : (Finset.univ : Finset α) ≃ α where
  toFun i := i.val
  invFun i := ⟨i, Finset.mem_univ i⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem selectedPermanent_univ (B : Matrix α α R) :
    selectedPermanent B Finset.univ Finset.univ = B.permanent :=
  rectangularPermanent_submatrix_equiv B finsetUnivEquiv finsetUnivEquiv

theorem permanent_laplace (B : Matrix α α R) (s : Finset α) :
    B.permanent = ∑ t : Finset α, selectedPermanent B s t * selectedPermanent B sᶜ tᶜ := by
  rw [← selectedPermanent_univ B, selectedPermanent_laplace B Finset.univ Finset.univ s (Finset.subset_univ s)]
  simp [← Finset.compl_eq_univ_sdiff]

theorem permanent_four_blocks_image (B : Matrix α α R) (F : Finset α) :
    B.permanent = ∑ t : Finset α, ∑ C ∈ F.powerset, ∑ J ∈ Fᶜ.powerset,
      selectedPermanent B C (t ∩ F) * selectedPermanent B J (F \ t) *
        selectedPermanent B (F \ C) (t \ F) * selectedPermanent B (Fᶜ \ J) (tᶜ \ F) := by
  rw [permanent_laplace B F]
  apply Finset.sum_congr rfl
  intro t _
  rw [selectedPermanent_row_laplace B F t (t ∩ F) Finset.inter_subset_left,
    selectedPermanent_row_laplace B Fᶜ tᶜ (F \ t) (by
      intro i hi
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2)]
  have hdiff : t \ (t ∩ F) = t \ F := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdiff' : tᶜ \ (F \ t) = tᶜ \ F := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_compl]
    tauto
  rw [hdiff, hdiff', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  ring

theorem split_union_identities (F R I : Finset α) (hR : R ⊆ F) (hI : I ⊆ Fᶜ) :
    (R ∪ I) ∩ F = R ∧ F \ (R ∪ I) = F \ R ∧
      (R ∪ I) \ F = I ∧ (R ∪ I)ᶜ \ F = Fᶜ \ I := by
  have hri (i : α) : (i ∈ R → i ∈ F) ∧ (i ∈ I → i ∉ F) :=
    ⟨fun h => hR h, fun h => Finset.mem_compl.mp (hI h)⟩
  constructor
  · ext i
    have hr := hri i
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  constructor
  · ext i
    have hr := hri i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  constructor
  · ext i
    have hr := hri i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  · ext i
    have hr := hri i
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_compl]
    tauto

theorem sum_finsets_split (F : Finset α) (f : Finset α → R) :
    (∑ t : Finset α, f t) = ∑ R ∈ F.powerset, ∑ I ∈ Fᶜ.powerset, f (R ∪ I) := by
  symm
  change (∑ r ∈ F.powerset, ∑ i ∈ Fᶜ.powerset,
    (fun p : Finset α × Finset α => f (p.1 ∪ p.2)) (r, i)) = _
  rw [← Finset.sum_product (f := fun p : Finset α × Finset α => f (p.1 ∪ p.2))]
  apply Finset.sum_bij (fun p _ => p.1 ∪ p.2)
  · intro p _
    exact Finset.mem_univ _
  · intro a ha b hb h
    have ha' := Finset.mem_product.mp ha
    have hb' := Finset.mem_product.mp hb
    have hA := split_union_identities F a.1 a.2 (Finset.mem_powerset.mp ha'.1) (Finset.mem_powerset.mp ha'.2)
    have hB := split_union_identities F b.1 b.2 (Finset.mem_powerset.mp hb'.1) (Finset.mem_powerset.mp hb'.2)
    apply Prod.ext
    · exact hA.1.symm.trans ((congrArg (fun t => t ∩ F) h).trans hB.1)
    · exact hA.2.2.1.symm.trans ((congrArg (fun t => t \ F) h).trans hB.2.2.1)
  · intro t _
    refine ⟨(t ∩ F, t \ F), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_powerset.mpr Finset.inter_subset_right
      · exact Finset.mem_powerset.mpr (fun i hi => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2)
    · ext i
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
  · intro _ _
    rfl

/-- Exact four-block expansion of the actual permanent. Each selected minor
uses all bijections between its actual, possibly different row and column
sets; unequal cardinalities vanish automatically. -/
theorem permanent_four_blocks (B : Matrix α α R) (F : Finset α) :
    B.permanent = ∑ R ∈ F.powerset, ∑ C ∈ F.powerset,
      ∑ I ∈ Fᶜ.powerset, ∑ J ∈ Fᶜ.powerset,
        selectedPermanent B C R * selectedPermanent B J (F \ R) *
          selectedPermanent B (F \ C) I * selectedPermanent B (Fᶜ \ J) (Fᶜ \ I) := by
  rw [permanent_four_blocks_image, sum_finsets_split F]
  apply Finset.sum_congr rfl
  intro R hR
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro I hI
  have h := split_union_identities F R I (Finset.mem_powerset.mp hR) (Finset.mem_powerset.mp hI)
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]

omit [Fintype α] [DecidableEq α] in
theorem sum_powerset_eq_sum_powersetCard (F : Finset α) (k : ℕ) (f : Finset α → R)
    (hz : ∀ s, s ⊆ F → s.card ≠ k → f s = 0) :
    (∑ s ∈ F.powerset, f s) = ∑ s ∈ F.powersetCard k, f s := by
  symm
  apply Finset.sum_subset
  · intro s hs
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hs).1
  · intro s hs hnot
    apply hz s (Finset.mem_powerset.mp hs)
    intro hc
    exact hnot (Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hs, hc⟩)

/-- Cardinality-organized four-block expansion, with exactly the row and
column deletion sets of the manuscript. -/
theorem permanent_four_blocks_by_size (B : Matrix α α R) (F : Finset α) :
    B.permanent = ∑ s ∈ Finset.range (F.card + 1),
      ∑ R ∈ F.powersetCard s, ∑ C ∈ F.powersetCard s,
        ∑ I ∈ Fᶜ.powersetCard (F.card - s), ∑ J ∈ Fᶜ.powersetCard (F.card - s),
          selectedPermanent B C R * selectedPermanent B J (F \ R) *
            selectedPermanent B (F \ C) I * selectedPermanent B (Fᶜ \ J) (Fᶜ \ I) := by
  rw [permanent_four_blocks, Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro R hR
  have hRsub := (Finset.mem_powersetCard.mp hR).1
  have hRcard := (Finset.mem_powersetCard.mp hR).2
  rw [sum_powerset_eq_sum_powersetCard F s _ (by
    intro C _ hC
    have hz := selectedPermanent_eq_zero_of_card_ne B C R (by rwa [hRcard])
    simp [hz])]
  apply Finset.sum_congr rfl
  intro C hC
  have hCsub := (Finset.mem_powersetCard.mp hC).1
  have hCcard := (Finset.mem_powersetCard.mp hC).2
  have hdiffC : (F \ C).card = F.card - s := by rw [Finset.card_sdiff_of_subset hCsub, hCcard]
  have hdiffR : (F \ R).card = F.card - s := by rw [Finset.card_sdiff_of_subset hRsub, hRcard]
  rw [sum_powerset_eq_sum_powersetCard Fᶜ (F.card - s) _ (by
    intro I _ hI
    have hz := selectedPermanent_eq_zero_of_card_ne B (F \ C) I (by
      rw [hdiffC]
      exact Ne.symm hI)
    simp [hz])]
  apply Finset.sum_congr rfl
  intro I _
  rw [sum_powerset_eq_sum_powersetCard Fᶜ (F.card - s) _ (by
    intro J _ hJ
    have hz := selectedPermanent_eq_zero_of_card_ne B J (F \ R) (by rwa [hdiffR])
    simp [hz])]

end TournamentHamiltonian
