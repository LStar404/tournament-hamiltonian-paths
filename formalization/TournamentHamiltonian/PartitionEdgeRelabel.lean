import TournamentHamiltonian.GaussianCoreConvolution

/-! Relabeling of actual partition graphs and their core weights. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ η ι : Type*} [Fintype κ] [Fintype η] [DecidableEq κ] [DecidableEq η] [Fintype ι]

noncomputable def setoidEdgeOrderIso (e : κ ≃ η) : Setoid κ ≃o Setoid η where
  toFun P := Setoid.comap e.symm P
  invFun P := Setoid.comap e P
  left_inv P := by
    apply Setoid.ext
    intro a b
    change P (e.symm (e a)) (e.symm (e b)) ↔ P a b
    simp
  right_inv P := by
    apply Setoid.ext
    intro a b
    change P (e (e.symm a)) (e (e.symm b)) ↔ P a b
    simp
  map_rel_iff' := by
    intro P Q
    change (Setoid.comap e.symm P ≤ Setoid.comap e.symm Q) ↔ P ≤ Q
    constructor
    · intro h a b hab
      have hp : Setoid.comap e.symm P (e a) (e b) := by
        change P (e.symm (e a)) (e.symm (e b))
        simpa using hab
      have hh := h hp
      change Q (e.symm (e a)) (e.symm (e b)) at hh
      simpa using hh
    · intro h a b hab
      exact h hab

noncomputable def quotientEdgeEquiv (e : κ ≃ η) (P : Setoid κ) :
    Quotient P ≃ Quotient (setoidEdgeOrderIso e P) :=
  Quotient.congr e (fun a b => by
    change P a b ↔ P (e.symm (e a)) (e.symm (e b))
    simp)

noncomputable def relabeledPartitionBlockEquiv (e : κ ≃ η) (P : Setoid κ) (v : Quotient P) :
    PartitionBlock P v ≃ PartitionBlock (setoidEdgeOrderIso e P) (quotientEdgeEquiv e P v) where
  toFun x := ⟨e x.val, by
    have h := congrArg (quotientEdgeEquiv e P) x.property
    exact h⟩
  invFun y := ⟨e.symm y.val, by
    apply (quotientEdgeEquiv e P).injective
    simpa only [quotientEdgeEquiv, Quotient.congr_mk, Equiv.apply_symm_apply] using y.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

omit [DecidableEq κ] [DecidableEq η] in
theorem relabeledPartitionDegree_eq (e : κ ≃ η) (P : Setoid κ) (v : Quotient P) :
    coordinatePartitionDegree (setoidEdgeOrderIso e P) (quotientEdgeEquiv e P v) =
      coordinatePartitionDegree P v := by
  rw [← partitionBlock_card_eq_degree, ← partitionBlock_card_eq_degree]
  exact (Fintype.card_congr (relabeledPartitionBlockEquiv e P v)).symm

omit [DecidableEq κ] [DecidableEq η] in
theorem relabeledPartition_mu {R : Type*} [CommRing R] (e : κ ≃ η) (P : Setoid κ) :
    IncidenceAlgebra.mu R ⊥ (setoidEdgeOrderIso e P) = IncidenceAlgebra.mu R ⊥ P :=
  mu_bottom_orderIso (setoidEdgeOrderIso e) P

omit [DecidableEq κ] [DecidableEq η] [Fintype ι] in
private theorem relabeled_coordinateProduct (e : κ ≃ η) (B : Matrix ι ι ℝ) (P Q : Setoid κ)
    (r : Quotient P → ι) (c : Quotient Q → ι) :
    (∏ b : η,
      B ((Equiv.arrowCongr (quotientEdgeEquiv e P) (Equiv.refl ι) r)
          (Quotient.mk (setoidEdgeOrderIso e P) b))
        ((Equiv.arrowCongr (quotientEdgeEquiv e Q) (Equiv.refl ι) c)
          (Quotient.mk (setoidEdgeOrderIso e Q) b))) =
      ∏ a : κ, B (r (Quotient.mk P a)) (c (Quotient.mk Q a)) := by
  symm
  apply Fintype.prod_equiv e
  intro a
  change B (r (Quotient.mk P a)) (c (Quotient.mk Q a)) =
    B (r ((quotientEdgeEquiv e P).symm (quotientEdgeEquiv e P (Quotient.mk P a))))
      (c ((quotientEdgeEquiv e Q).symm (quotientEdgeEquiv e Q (Quotient.mk Q a))))
  simp

omit [DecidableEq κ] [DecidableEq η] in
theorem relabeledPartitionContraction (e : κ ≃ η) (B : Matrix ι ι ℝ) (P Q : Setoid κ) :
    partitionContraction B (setoidEdgeOrderIso e P) (setoidEdgeOrderIso e Q) =
      partitionContraction B P Q := by
  unfold partitionContraction
  let ep := Equiv.arrowCongr (quotientEdgeEquiv e P) (Equiv.refl ι)
  let eq := Equiv.arrowCongr (quotientEdgeEquiv e Q) (Equiv.refl ι)
  calc
    _ = ∑ r : Quotient P → ι, ∑ c : Quotient Q → ι,
        ∏ b : η, B (ep r (Quotient.mk _ b)) (eq c (Quotient.mk _ b)) := by
      symm
      apply Fintype.sum_equiv ep
      intro r
      exact Fintype.sum_equiv eq _ _ (fun _ => rfl)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro c _
      exact relabeled_coordinateProduct e B P Q r c

omit [DecidableEq κ] [DecidableEq η] in
theorem relabeled_pure_component_iff (e : κ ≃ η) (P Q : Setoid κ) (a : κ) :
    IsPureDegreeTwoComponent (setoidEdgeOrderIso e P) (setoidEdgeOrderIso e Q) (e a) ↔
      IsPureDegreeTwoComponent P Q a := by
  have hrel (f : κ) :
      (setoidEdgeOrderIso e P ⊔ setoidEdgeOrderIso e Q) (e f) (e a) ↔ (P ⊔ Q) f a := by
    rw [← (setoidEdgeOrderIso e).map_sup]
    change (P ⊔ Q) (e.symm (e f)) (e.symm (e a)) ↔ (P ⊔ Q) f a
    simp
  constructor
  · intro h f hf
    have hd := h (e f) ((hrel f).mpr hf)
    change coordinatePartitionDegree (setoidEdgeOrderIso e P) (quotientEdgeEquiv e P (Quotient.mk P f)) = 2 ∧
      coordinatePartitionDegree (setoidEdgeOrderIso e Q) (quotientEdgeEquiv e Q (Quotient.mk Q f)) = 2 at hd
    rwa [relabeledPartitionDegree_eq, relabeledPartitionDegree_eq] at hd
  · intro h b hb
    have hfb : (P ⊔ Q) (e.symm b) a := (hrel (e.symm b)).mp (by simpa using hb)
    have hd := h (e.symm b) hfb
    have hp := relabeledPartitionDegree_eq e P (Quotient.mk P (e.symm b))
    have hq := relabeledPartitionDegree_eq e Q (Quotient.mk Q (e.symm b))
    have hp' : coordinatePartitionDegree (setoidEdgeOrderIso e P) (Quotient.mk _ b) =
        coordinatePartitionDegree P (Quotient.mk P (e.symm b)) := by
      simpa only [quotientEdgeEquiv, Quotient.congr_mk, Equiv.apply_symm_apply] using hp
    have hq' : coordinatePartitionDegree (setoidEdgeOrderIso e Q) (Quotient.mk _ b) =
        coordinatePartitionDegree Q (Quotient.mk Q (e.symm b)) := by
      simpa only [quotientEdgeEquiv, Quotient.congr_mk, Equiv.apply_symm_apply] using hq
    rw [hp', hq']
    exact hd

noncomputable def corePartitionPairEdgeEquiv (e : κ ≃ η) : CorePartitionPair κ ≃ CorePartitionPair η :=
  Equiv.subtypeEquiv (Equiv.prodCongr (setoidEdgeOrderIso e).toEquiv (setoidEdgeOrderIso e).toEquiv)
    (by
      intro PQ
      constructor
      · intro h b
        change ¬ IsPureDegreeTwoComponent (setoidEdgeOrderIso e PQ.1) (setoidEdgeOrderIso e PQ.2) b
        have hb := h (e.symm b)
        have he := relabeled_pure_component_iff e PQ.1 PQ.2 (e.symm b)
        simpa only [Equiv.apply_symm_apply] using he.not.mpr hb
      · intro h a
        change (∀ b : η, ¬ IsPureDegreeTwoComponent (setoidEdgeOrderIso e PQ.1)
          (setoidEdgeOrderIso e PQ.2) b) at h
        exact (relabeled_pure_component_iff e PQ.1 PQ.2 a).not.mp (h (e a)))

omit [DecidableEq κ] [DecidableEq η] in
theorem coreCoordinateSum_edge_relabel (e : κ ≃ η) (B : Matrix ι ι ℝ) :
    coreCoordinateSum (κ := κ) B = coreCoordinateSum (κ := η) B := by
  unfold coreCoordinateSum
  apply Fintype.sum_equiv (corePartitionPairEdgeEquiv e)
  intro c
  change IncidenceAlgebra.mu ℝ ⊥ c.val.1 * IncidenceAlgebra.mu ℝ ⊥ c.val.2 *
      partitionContraction B c.val.1 c.val.2 =
    IncidenceAlgebra.mu ℝ ⊥ (setoidEdgeOrderIso e c.val.1) *
      IncidenceAlgebra.mu ℝ ⊥ (setoidEdgeOrderIso e c.val.2) *
        partitionContraction B (setoidEdgeOrderIso e c.val.1) (setoidEdgeOrderIso e c.val.2)
  rw [relabeledPartition_mu, relabeledPartition_mu, relabeledPartitionContraction]

omit [DecidableEq κ] in
theorem coreCoordinateSum_eq_card (B : Matrix ι ι ℝ) :
    coreCoordinateSum (κ := κ) B = coreCoordinateSum (κ := Fin (Fintype.card κ)) B :=
  coreCoordinateSum_edge_relabel (Fintype.equivFin κ) B

end TournamentHamiltonian
