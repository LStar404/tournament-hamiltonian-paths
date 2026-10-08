import TournamentHamiltonian.GaussianCoreComponents

/-! Genuine block and Möbius factorization across any invariant subset of edge labels. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

private noncomputable def splitQuotientLabel (P : Setoid κ) (s : κ → Prop) [DecidablePred s]
    (e : κ) : Quotient (Setoid.comap (Subtype.val : {e // s e} → κ) P) ⊕
      Quotient (Setoid.comap (Subtype.val : {e // ¬s e} → κ) P) :=
  if he : s e then .inl (Quotient.mk _ ⟨e, he⟩) else .inr (Quotient.mk _ ⟨e, he⟩)

omit [Fintype κ] [DecidableEq κ] in
private theorem splitQuotientLabel_rel (P : Setoid κ) (s : κ → Prop) [DecidablePred s]
    (hs : ∀ e f, P e f → (s e ↔ s f)) {e f : κ} (hef : P e f) :
    splitQuotientLabel P s e = splitQuotientLabel P s f := by
  unfold splitQuotientLabel
  by_cases he : s e
  · have hf := (hs e f hef).mp he
    simp only [he, hf, dite_true]
    congr 1
    exact Quotient.sound hef
  · have hf := (hs e f hef).not.mp he
    simp only [he, hf, dite_false]
    congr 1
    exact Quotient.sound hef

noncomputable def invariantSubsetQuotientEquiv (P : Setoid κ) (s : κ → Prop) [DecidablePred s]
    (hs : ∀ e f, P e f → (s e ↔ s f)) :
    (Quotient (Setoid.comap (Subtype.val : {e // s e} → κ) P) ⊕
      Quotient (Setoid.comap (Subtype.val : {e // ¬s e} → κ) P)) ≃ Quotient P where
  toFun := Sum.elim (Quotient.map Subtype.val (fun _ _ h => h))
    (Quotient.map Subtype.val (fun _ _ h => h))
  invFun := Quotient.lift (splitQuotientLabel P s) (fun _ _ h => splitQuotientLabel_rel P s hs h)
  left_inv x := by
    cases x with
    | inl x =>
      induction x using Quotient.inductionOn with
      | h e => simp [splitQuotientLabel, e.property]
    | inr x =>
      induction x using Quotient.inductionOn with
      | h e => simp [splitQuotientLabel, e.property]
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h e => by_cases he : s e <;> simp [splitQuotientLabel, he]

omit [DecidableEq κ] in
theorem invariantSubsetQuotientEquiv_degree (P : Setoid κ) (s : κ → Prop) [DecidablePred s]
    (hs : ∀ e f, P e f → (s e ↔ s f))
    (v : Quotient (Setoid.comap (Subtype.val : {e // s e} → κ) P) ⊕
      Quotient (Setoid.comap (Subtype.val : {e // ¬s e} → κ) P)) :
    coordinatePartitionDegree P (invariantSubsetQuotientEquiv P s hs v) =
      Sum.elim (coordinatePartitionDegree (Setoid.comap Subtype.val P))
        (coordinatePartitionDegree (Setoid.comap Subtype.val P)) v := by
  cases v with
  | inl v =>
    induction v using Quotient.inductionOn with
    | h e => exact (restrictedPartitionDegree_eq P s hs e).symm
  | inr v =>
    induction v using Quotient.inductionOn with
    | h e => exact (restrictedPartitionDegree_eq P (fun e => ¬s e)
        (fun e f h => (hs e f h).not) e).symm

omit [DecidableEq κ] in
theorem partition_mu_invariant_subset {R : Type*} [CommRing R]
    (P : Setoid κ) (s : κ → Prop) [DecidablePred s]
    (hs : ∀ e f, P e f → (s e ↔ s f)) :
    IncidenceAlgebra.mu R ⊥ P =
      IncidenceAlgebra.mu R ⊥ (Setoid.comap (Subtype.val : {e // s e} → κ) P) *
      IncidenceAlgebra.mu R ⊥ (Setoid.comap (Subtype.val : {e // ¬s e} → κ) P) := by
  rw [partition_mu_degree_weights κ P,
    partition_mu_degree_weights {e // s e}, partition_mu_degree_weights {e // ¬s e}]
  calc
    _ = ∏ v : Quotient (Setoid.comap (Subtype.val : {e // s e} → κ) P) ⊕
          Quotient (Setoid.comap (Subtype.val : {e // ¬s e} → κ) P),
        (-1 : R) ^ (coordinatePartitionDegree P (invariantSubsetQuotientEquiv P s hs v) - 1) *
          ((coordinatePartitionDegree P (invariantSubsetQuotientEquiv P s hs v) - 1).factorial : R) :=
      (Fintype.prod_equiv (invariantSubsetQuotientEquiv P s hs) _ _ (fun _ => rfl)).symm
    _ = _ := by
      simp only [invariantSubsetQuotientEquiv_degree, Fintype.prod_sum_type]
      rfl

variable {ι : Type*} [Fintype ι]

noncomputable def invariantSubsetLabelEquiv (P : Setoid κ) (s : κ → Prop) [DecidablePred s]
    (hs : ∀ e f, P e f → (s e ↔ s f)) :
    (Quotient P → ι) ≃
      ((Quotient (Setoid.comap (Subtype.val : {e // s e} → κ) P) → ι) ×
        (Quotient (Setoid.comap (Subtype.val : {e // ¬s e} → κ) P) → ι)) :=
  (Equiv.arrowCongr (invariantSubsetQuotientEquiv P s hs).symm (Equiv.refl ι)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

omit [Fintype κ] [DecidableEq κ] [Fintype ι] in
theorem invariantSubsetLabelEquiv_mk_pos (P : Setoid κ) (s : κ → Prop) [DecidablePred s]
    (hs : ∀ e f, P e f → (s e ↔ s f)) (r : Quotient P → ι) (e : {e // s e}) :
    (invariantSubsetLabelEquiv P s hs r).1 (Quotient.mk _ e) = r (Quotient.mk P e.val) := rfl

omit [Fintype κ] [DecidableEq κ] [Fintype ι] in
theorem invariantSubsetLabelEquiv_mk_neg (P : Setoid κ) (s : κ → Prop) [DecidablePred s]
    (hs : ∀ e f, P e f → (s e ↔ s f)) (r : Quotient P → ι) (e : {e // ¬s e}) :
    (invariantSubsetLabelEquiv P s hs r).2 (Quotient.mk _ e) = r (Quotient.mk P e.val) := rfl

omit [DecidableEq κ] [Fintype ι] in
private theorem coordinateProduct_split (B : Matrix ι ι ℝ) (P Q : Setoid κ)
    (s : κ → Prop) [DecidablePred s]
    (hsP : ∀ e f, P e f → (s e ↔ s f)) (hsQ : ∀ e f, Q e f → (s e ↔ s f))
    (r : Quotient P → ι) (c : Quotient Q → ι) :
    (∏ e : κ, B (r (Quotient.mk P e)) (c (Quotient.mk Q e))) =
      (∏ e : {e // s e},
        B ((invariantSubsetLabelEquiv P s hsP r).1 (Quotient.mk _ e))
          ((invariantSubsetLabelEquiv Q s hsQ c).1 (Quotient.mk _ e))) *
      (∏ e : {e // ¬s e},
        B ((invariantSubsetLabelEquiv P s hsP r).2 (Quotient.mk _ e))
          ((invariantSubsetLabelEquiv Q s hsQ c).2 (Quotient.mk _ e))) := by
  calc
    _ = ∏ x : {e // s e} ⊕ {e // ¬s e},
        B (r (Quotient.mk P (Equiv.sumCompl s x))) (c (Quotient.mk Q (Equiv.sumCompl s x))) :=
      (Fintype.prod_equiv (Equiv.sumCompl s) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      rfl

private theorem double_sum_equiv {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (e : α ≃ β) (f : γ ≃ δ) (w : β → δ → ℝ) :
    (∑ a : α, ∑ c : γ, w (e a) (f c)) = ∑ b : β, ∑ d : δ, w b d := by
  calc
    _ = ∑ a : α, ∑ d : δ, w (e a) d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Fintype.sum_equiv f _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_equiv e _ _ (fun _ => rfl)

omit [DecidableEq κ] in
theorem partitionContraction_invariant_subset (B : Matrix ι ι ℝ)
    (P Q : Setoid κ) (s : κ → Prop) [DecidablePred s]
    (hsP : ∀ e f, P e f → (s e ↔ s f)) (hsQ : ∀ e f, Q e f → (s e ↔ s f)) :
    partitionContraction B P Q =
      partitionContraction B
        (Setoid.comap (Subtype.val : {e // s e} → κ) P)
        (Setoid.comap (Subtype.val : {e // s e} → κ) Q) *
      partitionContraction B
        (Setoid.comap (Subtype.val : {e // ¬s e} → κ) P)
        (Setoid.comap (Subtype.val : {e // ¬s e} → κ) Q) := by
  unfold partitionContraction
  simp_rw [coordinateProduct_split B P Q s hsP hsQ]
  let wp : (Quotient (Setoid.comap (Subtype.val : {e // s e} → κ) P) → ι) →
      (Quotient (Setoid.comap (Subtype.val : {e // s e} → κ) Q) → ι) → ℝ :=
    fun r c => ∏ e : {e // s e}, B (r (Quotient.mk _ e)) (c (Quotient.mk _ e))
  let wn : (Quotient (Setoid.comap (Subtype.val : {e // ¬s e} → κ) P) → ι) →
      (Quotient (Setoid.comap (Subtype.val : {e // ¬s e} → κ) Q) → ι) → ℝ :=
    fun r c => ∏ e : {e // ¬s e}, B (r (Quotient.mk _ e)) (c (Quotient.mk _ e))
  let w := fun (r : (Quotient (Setoid.comap (Subtype.val : {e // s e} → κ) P) → ι) ×
      (Quotient (Setoid.comap (Subtype.val : {e // ¬s e} → κ) P) → ι))
    (c : (Quotient (Setoid.comap (Subtype.val : {e // s e} → κ) Q) → ι) ×
      (Quotient (Setoid.comap (Subtype.val : {e // ¬s e} → κ) Q) → ι)) =>
    wp r.1 c.1 * wn r.2 c.2
  change (∑ r : Quotient P → ι, ∑ c : Quotient Q → ι,
    w (invariantSubsetLabelEquiv P s hsP r) (invariantSubsetLabelEquiv Q s hsQ c)) =
      (∑ r, ∑ c, wp r c) * (∑ r, ∑ c, wn r c)
  rw [double_sum_equiv (invariantSubsetLabelEquiv P s hsP) (invariantSubsetLabelEquiv Q s hsQ) w]
  simp only [Fintype.sum_prod_type, w]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]

theorem coreComponent_mobius_product {R : Type*} [CommRing R] (P Q : Setoid κ) :
    IncidenceAlgebra.mu R ⊥ P * IncidenceAlgebra.mu R ⊥ Q =
      IncidenceAlgebra.mu R ⊥ (coreRowPartition P Q) *
        IncidenceAlgebra.mu R ⊥ (coreColumnPartition P Q) := by
  have hp := partition_mu_invariant_subset (R := R) P (IsPureDegreeTwoComponent P Q)
    (fun _ _ h => isPureDegreeTwoComponent_row_invariant P Q h)
  have hq := partition_mu_invariant_subset (R := R) Q (IsPureDegreeTwoComponent P Q)
    (fun _ _ h => isPureDegreeTwoComponent_column_invariant P Q h)
  change IncidenceAlgebra.mu R ⊥ P = IncidenceAlgebra.mu R ⊥ (pureRowPartition P Q) *
    IncidenceAlgebra.mu R ⊥ (coreRowPartition P Q) at hp
  change IncidenceAlgebra.mu R ⊥ Q = IncidenceAlgebra.mu R ⊥ (pureColumnPartition P Q) *
    IncidenceAlgebra.mu R ⊥ (coreColumnPartition P Q) at hq
  rw [hp, hq]
  calc
    _ = (IncidenceAlgebra.mu R ⊥ (pureRowPartition P Q) *
        IncidenceAlgebra.mu R ⊥ (pureColumnPartition P Q)) *
      (IncidenceAlgebra.mu R ⊥ (coreRowPartition P Q) *
        IncidenceAlgebra.mu R ⊥ (coreColumnPartition P Q)) := by ring
    _ = _ := by rw [pair_partition_mu_product _ _ (pureRowPartition_isPairing P Q)
      (pureColumnPartition_isPairing P Q), one_mul]

omit [DecidableEq κ] in
theorem coreComponent_contraction_product (B : Matrix ι ι ℝ) (P Q : Setoid κ) :
    partitionContraction B P Q =
      partitionContraction B (pureRowPartition P Q) (pureColumnPartition P Q) *
        partitionContraction B (coreRowPartition P Q) (coreColumnPartition P Q) := by
  exact partitionContraction_invariant_subset B P Q (IsPureDegreeTwoComponent P Q)
    (fun _ _ h => isPureDegreeTwoComponent_row_invariant P Q h)
    (fun _ _ h => isPureDegreeTwoComponent_column_invariant P Q h)

/-- The actual weighted graph splits into its Wick components and its signed core weight. -/
theorem coreComponent_weighted_contraction_product (B : Matrix ι ι ℝ) (P Q : Setoid κ) :
    IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ Q * partitionContraction B P Q =
      partitionContraction B (pureRowPartition P Q) (pureColumnPartition P Q) *
        (IncidenceAlgebra.mu ℝ ⊥ (coreRowPartition P Q) *
          IncidenceAlgebra.mu ℝ ⊥ (coreColumnPartition P Q) *
            partitionContraction B (coreRowPartition P Q) (coreColumnPartition P Q)) := by
  rw [coreComponent_mobius_product, coreComponent_contraction_product]
  ring

end TournamentHamiltonian
