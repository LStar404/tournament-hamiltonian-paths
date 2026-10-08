import TournamentHamiltonian.GaussianCoreDecomposition
import TournamentHamiltonian.GaussianWickFinite

/-! Actual Gaussian/core coefficient decomposition over complementary finite edge subsets. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

theorem pairingPartitionPair_contraction_sum (B : Matrix ι ι ℝ) :
    (∑ p : PairingPartitionPair κ, partitionContraction B p.val.1 p.val.2) =
      gaussianBilinearMoment B (Fintype.card κ) := by
  calc
    _ = ∑ p ∈ Finset.univ.filter (fun p : Setoid κ × Setoid κ =>
          IsPairingPartition p.1 ∧ IsPairingPartition p.2),
        partitionContraction B p.1 p.2 :=
      (Finset.sum_subtype _ (by simp) (fun p : Setoid κ × Setoid κ =>
        partitionContraction B p.1 p.2)).symm
    _ = ∑ P : Setoid κ, ∑ Q : Setoid κ,
        if IsPairingPartition P ∧ IsPairingPartition Q then partitionContraction B P Q else 0 := by
      rw [Finset.sum_filter, Fintype.sum_prod_type]
    _ = _ := by
      rw [gaussianBilinearMoment_pairing_expansion_finite (κ := κ)]
      simp only [rectangularPartitionContraction_square, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro P _
      by_cases hp : IsPairingPartition P <;> simp [hp]

/-- The signed sum of actual partition graphs having no pure degree-two component. -/
noncomputable def coreCoordinateSum (B : Matrix ι ι ℝ) : ℝ :=
  ∑ c : CorePartitionPair κ,
    IncidenceAlgebra.mu ℝ ⊥ c.val.1 * IncidenceAlgebra.mu ℝ ⊥ c.val.2 *
      partitionContraction B c.val.1 c.val.2

/-- The finite component identity uses actual Gaussian moments, with arbitrary finite edge types. -/
theorem partitionGraphSum_gaussian_core_subset_sum (B : Matrix ι ι ℝ) :
    (∑ P : Setoid κ, ∑ Q : Setoid κ,
      IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ Q * partitionContraction B P Q) =
      ∑ s : Set κ, gaussianBilinearMoment B (Fintype.card {e // s e}) *
        coreCoordinateSum (κ := {e // ¬s e}) B := by
  rw [partitionGraphSum_pure_core_decomposition]
  apply Finset.sum_congr rfl
  intro s _
  rw [pairingPartitionPair_contraction_sum]
  rfl

variable [DecidableEq ι]

theorem distinctCoordinateSum_gaussian_core_subset_sum (B : Matrix ι ι ℝ) (k : ℕ) :
    distinctCoordinateSum B k =
      ∑ s : Set (Fin k), gaussianBilinearMoment B (Fintype.card {e // s e}) *
        coreCoordinateSum (κ := {e // ¬s e}) B := by
  rw [distinctCoordinateSum_partition_expansion]
  exact partitionGraphSum_gaussian_core_subset_sum B

theorem normalized_coeff_gaussian_core_subset_sum (E : Matrix ι ι ℝ) (k : ℕ) :
    (((Fintype.card ι).descFactorial k : ℝ) / (Fintype.card ι : ℝ) ^ k) *
        (normalizedPermanentPolynomial E).coeff k =
      (∑ s : Set (Fin k),
        gaussianBilinearMoment (fun i j => E i j / (Fintype.card ι : ℝ)) (Fintype.card {e // s e}) *
          coreCoordinateSum (κ := {e // ¬s e}) (fun i j => E i j / (Fintype.card ι : ℝ))) /
        (k.factorial : ℝ) := by
  rw [normalized_coeff_distinct_coordinates, distinctCoordinateSum_gaussian_core_subset_sum]

end TournamentHamiltonian
