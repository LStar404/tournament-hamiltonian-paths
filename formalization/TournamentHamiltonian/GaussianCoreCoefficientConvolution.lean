import TournamentHamiltonian.PartitionEdgeRelabel
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! The true finite coefficient convolution of Wick moments and actual pure-free cores. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

private noncomputable def setFinsetEdgeEquiv : Set κ ≃ Finset κ where
  toFun s := Finset.univ.filter (fun e => s e)
  invFun s := (s : Set κ)
  left_inv s := by ext e; simp; rfl
  right_inv s := by ext e; simp; rfl

omit [DecidableEq κ] in
private theorem setFinsetEdgeEquiv_card (s : Set κ) :
    Fintype.card {e // s e} = (setFinsetEdgeEquiv s).card := by
  exact Fintype.card_of_subtype (Finset.univ.filter (fun e => s e)) (by simp)

omit [DecidableEq κ] in
theorem finite_subset_card_sum (h : ℕ → ℝ) :
    (∑ s : Set κ, h (Fintype.card {e // s e})) =
      ∑ j ∈ Finset.range (Fintype.card κ + 1), (Fintype.card κ).choose j * h j := by
  calc
    _ = ∑ s : Finset κ, h s.card := Fintype.sum_equiv setFinsetEdgeEquiv _ _
      (fun s => by rw [setFinsetEdgeEquiv_card])
    _ = ∑ s ∈ (Finset.univ : Finset κ).powerset, h s.card := by
      have he : (Finset.univ : Finset (Finset κ)) = (Finset.univ : Finset κ).powerset := by
        ext s
        simp
      rw [he]
    _ = _ := by
      rw [Finset.sum_powerset]
      apply Finset.sum_congr (by simp)
      intro j _
      rw [Finset.sum_powersetCard]
      simp

theorem partitionGraphSum_gaussian_core_card_sum (B : Matrix ι ι ℝ) :
    (∑ P : Setoid κ, ∑ Q : Setoid κ,
      IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ Q * partitionContraction B P Q) =
      ∑ j ∈ Finset.range (Fintype.card κ + 1),
        (Fintype.card κ).choose j * gaussianBilinearMoment B j *
          coreCoordinateSum (κ := Fin (Fintype.card κ - j)) B := by
  rw [partitionGraphSum_gaussian_core_subset_sum]
  calc
    _ = ∑ s : Set κ,
        gaussianBilinearMoment B (Fintype.card {e // s e}) *
          coreCoordinateSum (κ := Fin (Fintype.card κ - Fintype.card {e // s e})) B := by
      apply Finset.sum_congr rfl
      intro s _
      rw [coreCoordinateSum_eq_card, Fintype.card_subtype_compl]
    _ = _ := by
      let h : ℕ → ℝ := fun j => gaussianBilinearMoment B j *
        coreCoordinateSum (κ := Fin (Fintype.card κ - j)) B
      change (∑ s : Set κ, h (Fintype.card {e // s e})) = _
      rw [finite_subset_card_sum h]
      apply Finset.sum_congr rfl
      intro j _
      ring

variable [DecidableEq ι]

/-- Actual signed, pure-component-free graph coefficients, with the exponential generating factor. -/
noncomputable def actualCoreCoefficient (B : Matrix ι ι ℝ) (k : ℕ) : ℝ :=
  coreCoordinateSum (κ := Fin k) B / (k.factorial : ℝ)

theorem distinctCoordinateSum_div_gaussian_core_convolution (B : Matrix ι ι ℝ) (k : ℕ) :
    distinctCoordinateSum B k / (k.factorial : ℝ) =
      ∑ j ∈ Finset.range (k + 1), bilinearGaussianCoefficient B j * actualCoreCoefficient B (k - j) := by
  rw [distinctCoordinateSum_partition_expansion,
    partitionGraphSum_gaussian_core_card_sum (κ := Fin k)]
  simp only [Fintype.card_fin, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by simpa using (Finset.mem_range.mp hj)
  rw [Nat.cast_choose ℝ hjk]
  unfold bilinearGaussianCoefficient actualCoreCoefficient
  have hk0 : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring_nf
  exact congrArg (fun m : ℕ => gaussianBilinearMoment B j *
    coreCoordinateSum (κ := Fin (m - j)) B) (Fintype.card_fin k)

/-- The exact manuscript coefficient identity `F=G*C`, in every finite degree without a convergence assertion for C. -/
theorem normalized_coeff_gaussian_core_convolution (E : Matrix ι ι ℝ) (k : ℕ) :
    (((Fintype.card ι).descFactorial k : ℝ) / (Fintype.card ι : ℝ) ^ k) *
        (normalizedPermanentPolynomial E).coeff k =
      ∑ j ∈ Finset.range (k + 1),
        bilinearGaussianCoefficient (fun i j => E i j / (Fintype.card ι : ℝ)) j *
          actualCoreCoefficient (fun i j => E i j / (Fintype.card ι : ℝ)) (k - j) := by
  rw [normalized_coeff_distinct_coordinates, distinctCoordinateSum_div_gaussian_core_convolution]

theorem actualCoreCoefficient_zero (B : Matrix ι ι ℝ) : actualCoreCoefficient B 0 = 1 := by
  have h := distinctCoordinateSum_div_gaussian_core_convolution B 0
  simp only [Nat.zero_add, distinctCoordinateSum_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    Finset.sum_range_one, Nat.sub_self] at h
  have hg : bilinearGaussianCoefficient B 0 = 1 := by
    simp [bilinearGaussianCoefficient, gaussianBilinearMoment_zero]
  rw [hg, one_mul] at h
  exact h.symm

end TournamentHamiltonian
