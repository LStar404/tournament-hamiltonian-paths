import TournamentHamiltonian.GaussianAnalytic

/-! Exact separation of the actual permanent coefficients into Wick pairings and the remaining graphs. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The genuine nonpairing terms of the two-partition expansion; all Möbius signs are retained. -/
noncomputable def nonPairingCoordinateSum (B : Matrix ι ι ℝ) (k : ℕ) : ℝ :=
  ∑ P : Setoid (Fin k), ∑ Q : Setoid (Fin k),
    if IsPairingPartition P ∧ IsPairingPartition Q then 0 else
      IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ Q * partitionContraction B P Q

omit [DecidableEq ι] in
theorem gaussianBilinearMoment_weighted_pairings (B : Matrix ι ι ℝ) (k : ℕ) :
    gaussianBilinearMoment B k =
      ∑ P : Setoid (Fin k), ∑ Q : Setoid (Fin k),
        if IsPairingPartition P ∧ IsPairingPartition Q then
          IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ Q * partitionContraction B P Q
        else 0 := by
  rw [gaussianBilinearMoment_pairing_expansion]
  simp only [rectangularPartitionContraction_square, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P _
  by_cases hp : IsPairingPartition P
  · simp only [hp, ite_true, true_and]
    apply Finset.sum_congr rfl
    intro Q _
    by_cases hq : IsPairingPartition Q
    · simp only [hq, ite_true]
      rw [pair_partition_mu_product P Q hp hq, one_mul]
    · simp [hq]
  · simp [hp]

theorem distinctCoordinateSum_eq_gaussian_add_nonpairing (B : Matrix ι ι ℝ) (k : ℕ) :
    distinctCoordinateSum B k = gaussianBilinearMoment B k + nonPairingCoordinateSum B k := by
  rw [distinctCoordinateSum_partition_expansion, gaussianBilinearMoment_weighted_pairings,
    nonPairingCoordinateSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Q _
  split_ifs <;> simp

/-- The Wick Gaussian coefficient is attached to the actual normalized permanent polynomial. -/
theorem normalized_coeff_eq_gaussian_add_nonpairing (E : Matrix ι ι ℝ) (k : ℕ) :
    (((Fintype.card ι).descFactorial k : ℝ) / (Fintype.card ι : ℝ) ^ k) *
        (normalizedPermanentPolynomial E).coeff k =
      bilinearGaussianCoefficient (fun i j => E i j / (Fintype.card ι : ℝ)) k +
        nonPairingCoordinateSum (fun i j => E i j / (Fintype.card ι : ℝ)) k / (k.factorial : ℝ) := by
  rw [normalized_coeff_distinct_coordinates, distinctCoordinateSum_eq_gaussian_add_nonpairing,
    add_div]
  rfl

/-- Above the number of available labels, the nonpairing terms cancel the entire Gaussian moment. -/
theorem nonPairingCoordinateSum_above_dimension (B : Matrix ι ι ℝ) (k : ℕ)
    (hk : Fintype.card ι < k) :
    nonPairingCoordinateSum B k = -gaussianBilinearMoment B k := by
  have h := distinctCoordinateSum_eq_gaussian_add_nonpairing B k
  rw [distinctCoordinateSum_eq_zero_of_lt B k hk] at h
  linarith

omit [DecidableEq ι] in
theorem gaussianBilinearMoment_zero (B : Matrix ι ι ℝ) : gaussianBilinearMoment B 0 = 1 := by
  simp [gaussianBilinearMoment]

theorem nonPairingCoordinateSum_zero (B : Matrix ι ι ℝ) : nonPairingCoordinateSum B 0 = 0 := by
  have h := distinctCoordinateSum_eq_gaussian_add_nonpairing B 0
  rw [distinctCoordinateSum_zero, gaussianBilinearMoment_zero] at h
  linarith

end TournamentHamiltonian
