import TournamentHamiltonian.CircularRadialMoments
import TournamentHamiltonian.GaussianWick
import Mathlib.GroupTheory.Perm.DomMulAct

open MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

omit [Fintype ι] in
theorem tupleMultiplicity_eq_fiber_card (f : κ → ι) (j : ι) :
    tupleMultiplicity f j = Fintype.card {i : κ // f i = j} := by
  simp [tupleMultiplicity, Fintype.card_subtype]

omit [Fintype ι] in
theorem exists_perm_of_tupleMultiplicity_eq (f g : κ → ι)
    (h : tupleMultiplicity f = tupleMultiplicity g) :
    ∃ σ : Equiv.Perm κ, f ∘ σ = g := by
  let ef : ∀ j, {i : κ // g i = j} ≃ {i : κ // f i = j} := fun j =>
    Fintype.equivOfCardEq (by
      simpa only [← tupleMultiplicity_eq_fiber_card] using
        (congrFun h j).symm)
  exact ⟨Equiv.ofFiberEquiv ef, funext (Equiv.ofFiberEquiv_map ef)⟩

omit [Fintype ι] in
theorem tupleMultiplicity_comp_equiv (f : κ → ι) (σ : Equiv.Perm κ) :
    tupleMultiplicity (f ∘ σ) = tupleMultiplicity f := by
  funext j
  rw [tupleMultiplicity_eq_fiber_card, tupleMultiplicity_eq_fiber_card]
  exact Fintype.card_congr (σ.subtypeEquiv (by intro i; rfl))

noncomputable def matchingPermEquiv (f g : κ → ι) (σ : Equiv.Perm κ)
    (hσ : f ∘ σ = g) :
    {τ : Equiv.Perm κ // f ∘ τ = f} ≃ {τ : Equiv.Perm κ // f ∘ τ = g} where
  toFun τ := ⟨σ.trans τ.val, by
    ext i
    change f (τ.val (σ i)) = g i
    rw [show f (τ.val (σ i)) = f (σ i) from congrFun τ.property (σ i)]
    exact congrFun hσ i⟩
  invFun τ := ⟨σ.symm.trans τ.val, by
    ext i
    change f (τ.val (σ.symm i)) = f i
    rw [show f (τ.val (σ.symm i)) = g (σ.symm i) from congrFun τ.property (σ.symm i)]
    rw [← congrFun hσ (σ.symm i)]
    simp only [Function.comp_apply, σ.apply_symm_apply]⟩
  left_inv τ := by apply Subtype.ext; ext i; simp
  right_inv τ := by apply Subtype.ext; ext i; simp

theorem matching_perm_card (f g : κ → ι) :
    Fintype.card {σ : Equiv.Perm κ // f ∘ σ = g} =
      if tupleMultiplicity f = tupleMultiplicity g then
        ∏ j, (tupleMultiplicity f j).factorial else 0 := by
  by_cases h : tupleMultiplicity f = tupleMultiplicity g
  · rw [ite_eq_left h]
    obtain ⟨σ, hσ⟩ := exists_perm_of_tupleMultiplicity_eq f g h
    rw [← Fintype.card_congr (matchingPermEquiv f g σ hσ), DomMulAct.stabilizer_card]
    simp only [← tupleMultiplicity_eq_fiber_card]
  · rw [ite_eq_right h]
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun σ => h ?_⟩
    rw [← σ.property, tupleMultiplicity_comp_equiv]

theorem circular_radial_tuple_average {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (hdegree : Fintype.card κ < N)
    (f g : κ → ι) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    finitePhaseAverage N (fun θ =>
      (∏ i, radialPhaseValue ζ (r (f i)) (θ (f i)).val) *
      star (∏ i, radialPhaseValue ζ (r (g i)) (θ (g i)).val)) =
      if tupleMultiplicity f = tupleMultiplicity g then
        ((∏ i, r i ^ tupleMultiplicity f i : ℝ) : ℂ) else 0 := by
  have hbound : ∀ (a : κ → ι) j, tupleMultiplicity a j < N := by
    intro a j
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_lt
      (by simpa using hdegree)
  have hexpand : finitePhaseAverage N (fun θ =>
      (∏ i, radialPhaseValue ζ (r (f i)) (θ (f i)).val) *
      star (∏ i, radialPhaseValue ζ (r (g i)) (θ (g i)).val)) =
      finitePhaseAverage N (fun θ => ∏ j,
        (radialPhaseValue ζ (r j) (θ j).val) ^ tupleMultiplicity f j *
        star ((radialPhaseValue ζ (r j) (θ j).val) ^ tupleMultiplicity g j)) := by
    congr 1
    funext θ
    rw [tuple_prod_eq_prod_powers f (fun j => radialPhaseValue ζ (r j) (θ j).val),
      tuple_prod_eq_prod_powers g (fun j => radialPhaseValue ζ (r j) (θ j).val), star_prod,
      Finset.prod_mul_distrib]
  rw [hexpand]
  exact circular_radial_product_mixed_average hζ hN r hr _ _ (hbound f) (hbound g)

theorem circular_radial_tuple_integrable {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (hdegree : Fintype.card κ < N)
    (f g : κ → ι) :
    Integrable (fun r : ι → ℝ => finitePhaseAverage N (fun θ =>
      (∏ i, radialPhaseValue ζ (r (f i)) (θ (f i)).val) *
      star (∏ i, radialPhaseValue ζ (r (g i)) (θ (g i)).val)))
      (radialProductMeasure ι) := by
  have hpos : ∀ᵐ r : ι → ℝ ∂radialProductMeasure ι, ∀ i, 0 < r i := by
    rw [ae_all_iff]
    intro i
    exact Measure.tendsto_eval_ae_ae.eventually radialExpMeasure_ae_pos
  have hreal := radial_product_pow_integrable (tupleMultiplicity f)
  have h : Integrable (fun r : ι → ℝ =>
      if tupleMultiplicity f = tupleMultiplicity g then
        ((∏ i, r i ^ tupleMultiplicity f i : ℝ) : ℂ) else 0) (radialProductMeasure ι) := by
    split_ifs
    · exact hreal.ofReal
    · exact integrable_zero _ _ _
  apply h.congr
  filter_upwards [hpos] with r hr
  exact (circular_radial_tuple_average hζ hN hdegree f g r (fun i => (hr i).le)).symm

/-- Complex Wick's formula, realized by the actual finite phase average and radial measure. -/
theorem circular_radial_tuple_moment {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (hdegree : Fintype.card κ < N)
    (f g : κ → ι) :
    (∫ r : ι → ℝ, finitePhaseAverage N (fun θ =>
      (∏ i, radialPhaseValue ζ (r (f i)) (θ (f i)).val) *
      star (∏ i, radialPhaseValue ζ (r (g i)) (θ (g i)).val))
      ∂radialProductMeasure ι) =
      ∑ σ : Equiv.Perm κ, if f ∘ σ = g then (1 : ℂ) else 0 := by
  have hbound : ∀ (a : κ → ι) j, tupleMultiplicity a j < N := by
    intro a j
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_lt
      (by simpa using hdegree)
  have hexpand : (fun r : ι → ℝ => finitePhaseAverage N (fun θ =>
      (∏ i, radialPhaseValue ζ (r (f i)) (θ (f i)).val) *
      star (∏ i, radialPhaseValue ζ (r (g i)) (θ (g i)).val))) =
      (fun r => finitePhaseAverage N (fun θ => ∏ j,
        (radialPhaseValue ζ (r j) (θ j).val) ^ tupleMultiplicity f j *
        star ((radialPhaseValue ζ (r j) (θ j).val) ^ tupleMultiplicity g j))) := by
    funext r
    congr 1
    funext θ
    change (∏ i, (fun j => radialPhaseValue ζ (r j) (θ j).val) (f i)) *
      star (∏ i, (fun j => radialPhaseValue ζ (r j) (θ j).val) (g i)) = _
    rw [tuple_prod_eq_prod_powers f (fun j => radialPhaseValue ζ (r j) (θ j).val),
      tuple_prod_eq_prod_powers g (fun j => radialPhaseValue ζ (r j) (θ j).val), star_prod,
      Finset.prod_mul_distrib]
  rw [hexpand, circular_radial_product_mixed_moment hζ hN _ _ (hbound f) (hbound g)]
  have hcard : (∑ σ : Equiv.Perm κ, if f ∘ σ = g then (1 : ℂ) else 0) =
      (Fintype.card {σ : Equiv.Perm κ // f ∘ σ = g} : ℂ) := by
    simp [Fintype.card_subtype]
  rw [hcard, matching_perm_card]
  split_ifs <;> simp

end TournamentHamiltonian
