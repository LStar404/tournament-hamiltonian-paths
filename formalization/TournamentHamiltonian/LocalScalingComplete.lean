import TournamentHamiltonian.LocalScalingNormalization

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- All quantitative conclusions for the same finite balancing potentials. -/
structure LocalScalingWitness (X : Matrix ι ι ℝ) (K C q eps : ℝ)
    (z : (ι ⊕ ι) → ℝ) : Prop where
  infinity : ‖z‖ ≤ 4 * localScalingInverseBudget C q * eps
  gauge : (∑ i, z (Sum.inl i)) = (∑ i, z (Sum.inr i))
  row_sum : ∀ i, ∑ j, localScaledMatrix X z i j = 1
  column_sum : ∀ j, ∑ i, localScaledMatrix X z i j = 1
  density : ∀ i j, |localScaledMatrix X z i j| ≤ 2 * K / Fintype.card ι
  gap : ‖localScaledMatrix X z - averagingMatrix ι‖ ≤ (1 + q) / 2
  euclidean : localEuclideanNorm z ≤
    2 * localScalingInverseBudget C q * localEuclideanNorm (localMarginalVector X)
  frobenius : realFrobeniusNorm (localScaledMatrix X z - X) ≤
    8 * K * localScalingInverseBudget C q / Real.sqrt (Fintype.card ι) *
      localEuclideanNorm (localMarginalVector X)
  capacity_nonneg : 0 ≤ localScalingCapacity z
  capacity_upper : localScalingCapacity z ≤ 32 * localScalingInverseBudget C q ^ 2 *
    localEuclideanNorm (localMarginalVector X) ^ 2
  nonnegative : ∀ i j, 0 ≤ localScaledMatrix X z i j
  zero_support : ∀ i j, localScaledMatrix X z i j = 0 ↔ X i j = 0

/-- The complete two local-scaling lemmas: every field concerns the actual
matrix obtained from one Banach fixed point. -/
theorem exists_local_scaling_witness (X : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (hX : ∀ i j, 0 ≤ X i j)
    (hmass : matrixEntryMass X = Fintype.card ι)
    (K C q eps : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (heps : 0 ≤ eps)
    (hXentry : ∀ i j, |X i j| ≤ K / Fintype.card ι)
    (hentry : ∀ i j, |localCenteredKernel X i j| ≤ C / Fintype.card ι)
    (hEq : ‖localCenteredKernel X‖ ≤ q)
    (ha : ∀ i, |matrixRowError X i| ≤ eps) (hb : ∀ j, |matrixColumnError X j| ≤ eps)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (hsmall : eps ≤ 1 / (256 * localScalingInverseBudget C q ^ 2))
    (hgap : eps ≤ (1 - q) / (2 * (32 * localScalingInverseBudget C q + 2))) :
    ∃ z : (ι ⊕ ι) → ℝ, LocalScalingWitness X K C q eps z := by
  obtain ⟨z, hz, hgauge, hr, hc, hdisp, hfrob, hcap0, hcap⟩ :=
    exists_local_scaling_displacement_capacity X hp hX hmass K C q eps hK hC hq0 hq1
      heps hXentry hentry hEq ha hb hrow hcol hsmall
  have hR1 := local_scaling_radius_le_quarter C q eps hC hq1 heps hsmall
  have hL := localScalingInverseBudget_nonneg C q hC hq1
  have hR0 : 0 ≤ 4 * localScalingInverseBudget C q * eps := by positivity
  have hcenter := localScaledMatrix_centered_gap_bound X hp z q eps
    (4 * localScalingInverseBudget C q * eps) heps hEq ha hb hrow hcol hR0 hR1 hz
  have hgap' := (le_div_iff₀
    (show 0 < 2 * (32 * localScalingInverseBudget C q + 2) by positivity)).mp hgap
  refine ⟨z, ⟨hz, hgauge, hr, hc,
    localScaledMatrix_dense_entry X z K hK hXentry (hz.trans hR1), ?_, hdisp, hfrob,
    hcap0, hcap, localScaledMatrix_nonnegative X hX z, localScaledMatrix_zero_support X z⟩⟩
  nlinarith

/-- Actual positive-mass normalization followed by local scaling, with both
the exact permanent restoration and the mass-defect upper bound. -/
theorem exists_normalized_local_scaling_witness (X : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (hX : ∀ i j, 0 ≤ X i j) (hM : 0 < matrixEntryMass X)
    (K C q eps : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (heps : 0 ≤ eps)
    (hXentry : ∀ i j, |massNormalizedMatrix X i j| ≤ K / Fintype.card ι)
    (hentry : ∀ i j, |localCenteredKernel (massNormalizedMatrix X) i j| ≤ C / Fintype.card ι)
    (hEq : ‖localCenteredKernel (massNormalizedMatrix X)‖ ≤ q)
    (ha : ∀ i, |matrixRowError (massNormalizedMatrix X) i| ≤ eps)
    (hb : ∀ j, |matrixColumnError (massNormalizedMatrix X) j| ≤ eps)
    (hrow : ∀ i, ∑ j, |massNormalizedMatrix X i j| ≤ 2)
    (hcol : ∀ j, ∑ i, |massNormalizedMatrix X i j| ≤ 2)
    (hsmall : eps ≤ 1 / (256 * localScalingInverseBudget C q ^ 2))
    (hgap : eps ≤ (1 - q) / (2 * (32 * localScalingInverseBudget C q + 2))) :
    ∃ z : (ι ⊕ ι) → ℝ, LocalScalingWitness (massNormalizedMatrix X) K C q eps z ∧
      X.permanent = Real.exp (-localScalingCapacity (massRestoredLocalPotentials X z)) *
        (localScaledMatrix (massNormalizedMatrix X) z).permanent ∧
      X.permanent ≤ Real.exp (matrixEntryMass X - Fintype.card ι) *
        (localScaledMatrix (massNormalizedMatrix X) z).permanent := by
  obtain ⟨z, hz⟩ := exists_local_scaling_witness (massNormalizedMatrix X) hp
    (massNormalizedMatrix_nonnegative X hX hM) (massNormalizedMatrix_mass X hM.ne')
    K C q eps hK hC hq0 hq1 heps hXentry hentry hEq ha hb hrow hcol hsmall hgap
  refine ⟨z, hz, ?_, normalized_local_scaling_permanent_upper X hp hX hM z hz.row_sum hz.column_sum⟩
  rw [← massRestoredLocalPotentials_scaledMatrix X hp hM]
  exact localScaledMatrix_permanent_restoration X (massRestoredLocalPotentials X z)

end TournamentHamiltonian
