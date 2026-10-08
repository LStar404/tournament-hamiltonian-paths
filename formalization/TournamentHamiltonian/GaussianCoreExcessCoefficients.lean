import TournamentHamiltonian.GaussianCoreCoefficientConvolution
import TournamentHamiltonian.GaussianCoreExcess

/-! Actual signed core coefficients split by positive excess in finite degree. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable (κ : Type*) [Fintype κ]

abbrev CenteredCorePartitionPair :=
  {c : CorePartitionPair κ // ¬ HasSingletonClass c.val.1 ∧ ¬ HasSingletonClass c.val.2}

variable {κ} {ι : Type*} [Fintype ι]

theorem coreCoordinateSum_centered (B : Matrix ι ι ℝ)
    (hrow : ∀ i, (∑ j : ι, B i j) = 0) (hcol : ∀ j, (∑ i : ι, B i j) = 0) :
    coreCoordinateSum (κ := κ) B =
      ∑ c : CenteredCorePartitionPair κ,
        IncidenceAlgebra.mu ℝ ⊥ c.val.val.1 * IncidenceAlgebra.mu ℝ ⊥ c.val.val.2 *
          partitionContraction B c.val.val.1 c.val.val.2 := by
  unfold coreCoordinateSum
  let w : CorePartitionPair κ → ℝ := fun c =>
    IncidenceAlgebra.mu ℝ ⊥ c.val.1 * IncidenceAlgebra.mu ℝ ⊥ c.val.2 * partitionContraction B c.val.1 c.val.2
  change (∑ c : CorePartitionPair κ, w c) = ∑ c : CenteredCorePartitionPair κ, w c.val
  rw [← Finset.sum_subtype (Finset.univ.filter (fun c : CorePartitionPair κ =>
      ¬ HasSingletonClass c.val.1 ∧ ¬ HasSingletonClass c.val.2)) (by simp) w]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c _ hc
  have hs : HasSingletonClass c.val.1 ∨ HasSingletonClass c.val.2 := by
    by_cases hp : HasSingletonClass c.val.1
    · exact Or.inl hp
    · exact Or.inr ((by simpa [hp] using hc))
  rcases hs with hs | hs
  · exact by simp only [w, partitionContraction_eq_zero_of_row_singleton B _ _ hcol hs, mul_zero]
  · exact by simp only [w, partitionContraction_eq_zero_of_column_singleton B _ _ hrow hs, mul_zero]

variable [DecidableEq κ]

theorem centeredCorePair_positive_excess (c : CenteredCorePartitionPair κ) (e : κ) :
    1 ≤ partitionGraphExcess c.val.val.1 c.val.val.2 := by
  have hn : ¬ (IsPairingPartition c.val.val.1 ∧ IsPairingPartition c.val.val.2) := by
    rintro ⟨hp, hq⟩
    exact c.val.property e (pairingPartitionPair_all_pure _ _ hp hq e)
  have h := nonPairing_graph_positive_excess _ _ c.property.1 c.property.2 hn
  simp only [partitionGraphExcess, Fintype.card_sum]
  omega

omit [DecidableEq κ] in
theorem centeredCorePair_excess_lt (c : CenteredCorePartitionPair κ) (e : κ) :
    partitionGraphExcess c.val.val.1 c.val.val.2 < Fintype.card κ := by
  have : Nonempty (Quotient c.val.val.1) := ⟨Quotient.mk _ e⟩
  have hq : 0 < Fintype.card (Quotient c.val.val.1) := Fintype.card_pos
  have : Nonempty κ := ⟨e⟩
  have hn : 0 < Fintype.card κ := Fintype.card_pos
  simp only [partitionGraphExcess, Fintype.card_sum]
  omega

noncomputable def coreExcessCoordinateSum (B : Matrix ι ι ℝ) (j : ℕ) : ℝ :=
  ∑ c : CenteredCorePartitionPair κ,
    if partitionGraphExcess c.val.val.1 c.val.val.2 = j then
      IncidenceAlgebra.mu ℝ ⊥ c.val.val.1 * IncidenceAlgebra.mu ℝ ⊥ c.val.val.2 *
        partitionContraction B c.val.val.1 c.val.val.2 else 0

theorem coreCoordinateSum_excess_sum (B : Matrix ι ι ℝ)
    (hrow : ∀ i, (∑ j : ι, B i j) = 0) (hcol : ∀ j, (∑ i : ι, B i j) = 0) (e : κ) :
    coreCoordinateSum (κ := κ) B =
      ∑ j ∈ Finset.Ico 1 (Fintype.card κ), coreExcessCoordinateSum (κ := κ) B j := by
  rw [coreCoordinateSum_centered B hrow hcol]
  unfold coreExcessCoordinateSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  have hp := centeredCorePair_positive_excess c e
  have hl := centeredCorePair_excess_lt c e
  have hm : partitionGraphExcess c.val.val.1 c.val.val.2 ∈ Finset.Ico 1 (Fintype.card κ) :=
    Finset.mem_Ico.mpr ⟨hp, hl⟩
  simp [hm]

noncomputable def actualCoreExcessCoefficient (B : Matrix ι ι ℝ) (j k : ℕ) : ℝ :=
  coreExcessCoordinateSum (κ := Fin k) B j / (k.factorial : ℝ)

omit [DecidableEq κ] in
theorem actualCoreCoefficient_excess_sum (B : Matrix ι ι ℝ)
    (hrow : ∀ i, (∑ j : ι, B i j) = 0) (hcol : ∀ j, (∑ i : ι, B i j) = 0)
    {k : ℕ} (hk : 0 < k) :
    actualCoreCoefficient B k = ∑ j ∈ Finset.Ico 1 k, actualCoreExcessCoefficient B j k := by
  unfold actualCoreCoefficient actualCoreExcessCoefficient
  rw [coreCoordinateSum_excess_sum B hrow hcol ⟨0, hk⟩]
  simp only [Fintype.card_fin, Finset.sum_div]

omit [DecidableEq κ] in
theorem actualCoreExcessCoefficient_eq_zero (B : Matrix ι ι ℝ) (j k : ℕ)
    (hj : j = 0 ∨ k ≤ j) (hk : 0 < k) :
    actualCoreExcessCoefficient B j k = 0 := by
  unfold actualCoreExcessCoefficient coreExcessCoordinateSum
  apply div_eq_zero_iff.mpr
  left
  apply Finset.sum_eq_zero
  intro c _
  have hp := centeredCorePair_positive_excess c ⟨0, hk⟩
  have hl := centeredCorePair_excess_lt c ⟨0, hk⟩
  simp only [Fintype.card_fin] at hl
  have hn : partitionGraphExcess c.val.val.1 c.val.val.2 ≠ j := by
    rcases hj with rfl | hj <;> omega
  simp [hn]

omit [DecidableEq κ] in
theorem actualCoreCoefficient_eq_constant_add_excess (B : Matrix ι ι ℝ)
    (hrow : ∀ i, (∑ j : ι, B i j) = 0) (hcol : ∀ j, (∑ i : ι, B i j) = 0) (k : ℕ) :
    actualCoreCoefficient B k = (if k = 0 then 1 else 0) +
      ∑ j ∈ Finset.Ico 1 k, actualCoreExcessCoefficient B j k := by
  by_cases hk : k = 0
  · subst k
    simp [actualCoreCoefficient_zero]
  · simpa [hk] using actualCoreCoefficient_excess_sum B hrow hcol (Nat.pos_of_ne_zero hk)

omit [DecidableEq κ] in
/-- The genuine centered distinct-coordinate coefficient is the Gaussian term plus
the finite convolution of its positive-excess core terms. -/
theorem distinctCoordinateSum_div_gaussian_excess_convolution (B : Matrix ι ι ℝ)
    (hrow : ∀ i, (∑ j : ι, B i j) = 0) (hcol : ∀ j, (∑ i : ι, B i j) = 0) (k : ℕ) :
    distinctCoordinateSum B k / (k.factorial : ℝ) = bilinearGaussianCoefficient B k +
      ∑ l ∈ Finset.range (k + 1), bilinearGaussianCoefficient B l *
        ∑ j ∈ Finset.Ico 1 (k - l), actualCoreExcessCoefficient B j (k - l) := by
  rw [distinctCoordinateSum_div_gaussian_core_convolution]
  simp_rw [actualCoreCoefficient_eq_constant_add_excess B hrow hcol, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    _ = bilinearGaussianCoefficient B k * (if k - k = 0 then 1 else 0) := by
      apply Finset.sum_eq_single k
      · intro l hl hne
        have hlk : l < k + 1 := Finset.mem_range.mp hl
        have hkl : k - l ≠ 0 := by omega
        simp [hkl]
      · simp
    _ = _ := by simp

end TournamentHamiltonian
