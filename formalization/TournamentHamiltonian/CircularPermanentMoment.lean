import TournamentHamiltonian.CircularWickFinite
import TournamentHamiltonian.PSDGaussianAMGM

open MeasureTheory Matrix
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

noncomputable def linearFormProduct (A : Matrix κ ι ℂ) (z : ι → ℂ) : ℂ :=
  ∏ i, ∑ j, A i j * z j

noncomputable def linearFormProductCoefficient (A : Matrix κ ι ℂ) (f : κ → ι) : ℂ :=
  ∏ i, A i (f i)

theorem linearFormProduct_expansion (A : Matrix κ ι ℂ) (z : ι → ℂ) :
    linearFormProduct A z =
      ∑ f : κ → ι, linearFormProductCoefficient A f * ∏ i, z (f i) := by
  rw [linearFormProduct, Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib, linearFormProductCoefficient]

theorem linearFormProduct_squared_expansion (A : Matrix κ ι ℂ) (z : ι → ℂ) :
    linearFormProduct A z * star (linearFormProduct A z) =
      ∑ f : κ → ι, ∑ g : κ → ι,
        (linearFormProductCoefficient A f * star (linearFormProductCoefficient A g)) *
          ((∏ i, z (f i)) * star (∏ i, z (g i))) := by
  rw [linearFormProduct_expansion, star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  simp only [star_mul]
  ring

theorem finitePhaseAverage_sum {α : Type*} [Fintype α] (N : ℕ)
    (f : α → (ι → Fin N) → ℂ) :
    finitePhaseAverage N (fun θ => ∑ a, f a θ) = ∑ a, finitePhaseAverage N (f a) := by
  rw [finitePhaseAverage, Finset.sum_comm, Finset.sum_div]
  rfl

theorem finitePhaseAverage_const_mul (N : ℕ) (c : ℂ) (f : (ι → Fin N) → ℂ) :
    finitePhaseAverage N (fun θ => c * f θ) = c * finitePhaseAverage N f := by
  rw [finitePhaseAverage, ← Finset.mul_sum, finitePhaseAverage]
  ring

noncomputable def circularLinearProductSquared (N : ℕ) (ζ : ℂ)
    (A : Matrix κ ι ℂ) (r : ι → ℝ) : ℂ :=
  finitePhaseAverage N (fun θ =>
    linearFormProduct A (fun j => radialPhaseValue ζ (r j) (θ j).val) *
    star (linearFormProduct A (fun j => radialPhaseValue ζ (r j) (θ j).val)))

theorem circularLinearProductSquared_expansion (N : ℕ) (ζ : ℂ) (A : Matrix κ ι ℂ) :
    circularLinearProductSquared N ζ A = (fun r =>
      ∑ f : κ → ι, ∑ g : κ → ι,
        (linearFormProductCoefficient A f * star (linearFormProductCoefficient A g)) *
          finitePhaseAverage N (fun θ =>
            (∏ i, radialPhaseValue ζ (r (f i)) (θ (f i)).val) *
            star (∏ i, radialPhaseValue ζ (r (g i)) (θ (g i)).val))) := by
  funext r
  unfold circularLinearProductSquared
  simp_rw [linearFormProduct_squared_expansion]
  rw [finitePhaseAverage_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [finitePhaseAverage_sum]
  apply Finset.sum_congr rfl
  intro g _
  exact finitePhaseAverage_const_mul _ _ _

theorem circularLinearProductSquared_integrable {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (hdegree : Fintype.card κ < N)
    (A : Matrix κ ι ℂ) :
    Integrable (circularLinearProductSquared N ζ A) (radialProductMeasure ι) := by
  rw [circularLinearProductSquared_expansion]
  apply integrable_finsetSum
  intro f _
  apply integrable_finsetSum
  intro g _
  exact (circular_radial_tuple_integrable hζ hN hdegree f g).const_mul _

theorem circularLinearProductSquared_moment_expansion {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (hdegree : Fintype.card κ < N)
    (A : Matrix κ ι ℂ) :
    (∫ r, circularLinearProductSquared N ζ A r ∂radialProductMeasure ι) =
      ∑ f : κ → ι, ∑ g : κ → ι,
        (linearFormProductCoefficient A f * star (linearFormProductCoefficient A g)) *
          (∑ σ : Equiv.Perm κ, if f ∘ σ = g then (1 : ℂ) else 0) := by
  rw [circularLinearProductSquared_expansion, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro f _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro g _
      rw [integral_const_mul, circular_radial_tuple_moment hζ hN hdegree]
    · intro g _
      exact (circular_radial_tuple_integrable hζ hN hdegree f g).const_mul _
  · intro f _
    apply integrable_finsetSum
    intro g _
    exact (circular_radial_tuple_integrable hζ hN hdegree f g).const_mul _

theorem gramPermanent_coordinate_expansion (A : Matrix κ ι ℂ) :
    (A * A.conjTranspose).permanent =
      ∑ σ : Equiv.Perm κ, ∑ f : κ → ι,
        (∏ i, A (σ i) (f i)) * star (linearFormProductCoefficient A f) := by
  rw [Matrix.permanent]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  simp only [Finset.prod_mul_distrib, linearFormProductCoefficient, star_prod]

theorem wick_permutation_contraction (A : Matrix κ ι ℂ) :
    (∑ f : κ → ι, ∑ g : κ → ι,
        (linearFormProductCoefficient A f * star (linearFormProductCoefficient A g)) *
          (∑ σ : Equiv.Perm κ, if f ∘ σ = g then (1 : ℂ) else 0)) =
      (A * A.conjTranspose).permanent := by
  simp_rw [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  have hcollapse : (∑ f : κ → ι, ∑ g : κ → ι, ∑ σ : Equiv.Perm κ,
      if f ∘ σ = g then linearFormProductCoefficient A f *
        star (linearFormProductCoefficient A g) else 0) =
      ∑ σ : Equiv.Perm κ, ∑ f : κ → ι,
        linearFormProductCoefficient A f * star (linearFormProductCoefficient A (f ∘ σ)) := by
    calc
      _ = ∑ f : κ → ι, ∑ σ : Equiv.Perm κ, ∑ g : κ → ι,
          if f ∘ σ = g then linearFormProductCoefficient A f *
            star (linearFormProductCoefficient A g) else 0 := by
        apply Finset.sum_congr rfl
        intro f _
        rw [Finset.sum_comm]
      _ = ∑ σ : Equiv.Perm κ, ∑ f : κ → ι, ∑ g : κ → ι,
          if f ∘ σ = g then linearFormProductCoefficient A f *
            star (linearFormProductCoefficient A g) else 0 := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.sum_congr rfl
        intro f _
        simp only [eq_comm (a := f ∘ σ), Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hcollapse, gramPermanent_coordinate_expansion]
  apply Finset.sum_congr rfl
  intro σ _
  let e : (κ → ι) ≃ (κ → ι) := Equiv.arrowCongr σ.symm (Equiv.refl ι)
  apply Fintype.sum_equiv e
  intro f
  have he : e f = f ∘ σ := rfl
  rw [he]
  simp only [linearFormProductCoefficient, Function.comp_apply]
  congr 1
  exact (Equiv.prod_comp σ (fun i => A i (f i))).symm

/-- The actual Gram permanent is the actual circular Gaussian polynomial moment.
The finite phases match all moments through the displayed degree. -/
theorem gramPermanent_eq_circular_moment {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (hdegree : Fintype.card κ < N)
    (A : Matrix κ ι ℂ) :
    (A * A.conjTranspose).permanent =
      ∫ r, circularLinearProductSquared N ζ A r ∂radialProductMeasure ι := by
  rw [circularLinearProductSquared_moment_expansion hζ hN hdegree,
    wick_permutation_contraction]

end TournamentHamiltonian
