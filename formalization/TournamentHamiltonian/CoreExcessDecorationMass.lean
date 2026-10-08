import TournamentHamiltonian.CompressedCoreTensorBounds

/-! The actual signed excess coefficient is bounded by genuine decorated graph fibers. -/

namespace TournamentHamiltonian

open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable (κ : Type*) [Fintype κ]

abbrev CenteredCoreOfExcessAndHigh (j b : ℕ) :=
  {c : CenteredCorePartitionPair κ //
    partitionGraphExcess c.val.val.1 c.val.val.2 = j ∧
      Fintype.card (HighGraphVertices c.val.val.1 c.val.val.2) = b}

abbrev DecoratedCoreOfExcessAndHigh (j b : ℕ) :=
  Σ c : CenteredCoreOfExcessAndHigh κ j b, HighVertexDecorations c.val.val.val.1 c.val.val.val.2

variable {κ} [DecidableEq κ]

theorem centeredCore_high_card_pos (c : CenteredCorePartitionPair κ)
    (hj : 0 < partitionGraphExcess c.val.val.1 c.val.val.2) :
    0 < Fintype.card (HighGraphVertices c.val.val.1 c.val.val.2) := by
  have hcard : 0 < Fintype.card κ := by
    have hle : partitionGraphExcess c.val.val.1 c.val.val.2 ≤ Fintype.card κ := Nat.sub_le _ _
    omega
  obtain ⟨e⟩ := Fintype.card_pos_iff.mp hcard
  have hpair : ¬ (IsPairingPartition c.val.val.1 ∧ IsPairingPartition c.val.val.2) := by
    rintro ⟨hP, hQ⟩
    exact c.val.property e (pairingPartitionPair_all_pure _ _ hP hQ e)
  rw [highGraphVertices_card]
  exact highDegreeVertices_card_pos _ _ c.property.1 c.property.2 hpair

theorem centeredCore_excess_high_sum (j : ℕ) (hj : 0 < j)
    (f : CenteredCorePartitionPair κ → ℝ) :
    (∑ c : CenteredCorePartitionPair κ,
      if partitionGraphExcess c.val.val.1 c.val.val.2 = j then f c else 0) =
      ∑ b ∈ Finset.Icc 1 (2 * j), ∑ c : CenteredCoreOfExcessAndHigh κ j b, f c.val := by
  have hsub : ∀ b, (∑ c : CenteredCoreOfExcessAndHigh κ j b, f c.val) =
      ∑ c : CenteredCorePartitionPair κ,
        if partitionGraphExcess c.val.val.1 c.val.val.2 = j ∧
          Fintype.card (HighGraphVertices c.val.val.1 c.val.val.2) = b then f c else 0 := by
    intro b
    rw [← Finset.sum_subtype (Finset.univ.filter (fun c : CenteredCorePartitionPair κ =>
      partitionGraphExcess c.val.val.1 c.val.val.2 = j ∧
        Fintype.card (HighGraphVertices c.val.val.1 c.val.val.2) = b)) (by simp) f,
      Finset.sum_filter]
  simp_rw [hsub]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hex : partitionGraphExcess c.val.val.1 c.val.val.2 = j
  · have hbpos := centeredCore_high_card_pos c (by omega)
    have hble := highDegreeVertices_card_le _ _ c.property.1 c.property.2
    rw [← highGraphVertices_card, hex] at hble
    have hbmem : Fintype.card (HighGraphVertices c.val.val.1 c.val.val.2) ∈ Finset.Icc 1 (2 * j) :=
      Finset.mem_Icc.mpr ⟨hbpos, hble⟩
    simp [hex, hbmem]
  · simp [hex]

/-- A finite sum over the actual decorated core graphs, before encoding and counting. -/
noncomputable def decoratedCorePathMass (n : ℕ) (C q R : ℝ) (j b : ℕ) : ℝ :=
  ∑ cd : DecoratedCoreOfExcessAndHigh κ j b,
    (∏ p : ActualCompressedPaths cd.1.val.val.val.1 cd.1.val.val.val.2,
      positiveChainWeight C q R (compressedPathLength cd.1.val.val.val.1 cd.1.val.val.val.2 p - 1)) /
        ((b.factorial : ℝ) *
          (∏ v : HighGraphVertices cd.1.val.val.val.1 cd.1.val.val.val.2,
            (partitionGraphDegree cd.1.val.val.val.1 cd.1.val.val.val.2 v.val : ℝ)) *
          (n : ℝ) ^ j)

theorem decoratedCorePathMass_nonneg (n : ℕ) (C q R : ℝ) (j b : ℕ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hR : 0 ≤ R) :
    0 ≤ decoratedCorePathMass (κ := κ) n C q R j b := by
  apply Finset.sum_nonneg
  intro cd _
  apply div_nonneg
  · exact Finset.prod_nonneg (fun p _ => positiveChainWeight_nonneg C q R hC hq hR _)
  · positivity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coreExcessCoordinateSum_abs_weighted_le_decorated_mass (B : Matrix ι ι ℝ)
    (j : ℕ) (hj : 0 < j) (C q R : ℝ) (hC : 0 ≤ C)
    (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i l, |B i l| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q) :
    |coreExcessCoordinateSum (κ := κ) B j| * R ^ Fintype.card κ ≤
      ∑ b ∈ Finset.Icc 1 (2 * j), decoratedCorePathMass (κ := κ) (Fintype.card ι) C q R j b := by
  let t : CenteredCorePartitionPair κ → ℝ := fun c =>
    IncidenceAlgebra.mu ℝ ⊥ c.val.val.1 * IncidenceAlgebra.mu ℝ ⊥ c.val.val.2 *
      partitionContraction B c.val.val.1 c.val.val.2
  calc
    _ ≤ (∑ c : CenteredCorePartitionPair κ,
        |if partitionGraphExcess c.val.val.1 c.val.val.2 = j then t c else 0|) * R ^ Fintype.card κ :=
      mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hR _)
    _ = ∑ c : CenteredCorePartitionPair κ,
        if partitionGraphExcess c.val.val.1 c.val.val.2 = j then |t c| * R ^ Fintype.card κ else 0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp
    _ = ∑ b ∈ Finset.Icc 1 (2 * j),
        ∑ c : CenteredCoreOfExcessAndHigh κ j b, |t c.val| * R ^ Fintype.card κ :=
      centeredCore_excess_high_sum j hj _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro b _
      rw [decoratedCorePathMass, Fintype.sum_sigma]
      apply Finset.sum_le_sum
      intro c _
      have hdec : (Fintype.card (HighVertexDecorations c.val.val.val.1 c.val.val.val.2) : ℝ) ≠ 0 := by
        exact_mod_cast (highVertexDecorations_card_pos _ _).ne'
      calc
        _ = ∑ _d : HighVertexDecorations c.val.val.val.1 c.val.val.val.2,
            |t c.val| * R ^ Fintype.card κ /
              (Fintype.card (HighVertexDecorations c.val.val.val.1 c.val.val.val.2) : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro d _
          have h := partitionContraction_decoration_weighted_path_le B c.val.val.val.1 c.val.val.val.2
            c.val.property.1 c.val.property.2 c.val.val.property C q R hC hn hR hB hq
          simpa only [c.property.1, c.property.2, t] using h

theorem actualCoreExcessCoefficient_abs_weighted_le_decorated_mass (B : Matrix ι ι ℝ)
    (j k : ℕ) (hj : 0 < j) (C q R : ℝ) (hC : 0 ≤ C)
    (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i l, |B i l| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q) :
    |actualCoreExcessCoefficient B j k| * R ^ k ≤
      (∑ b ∈ Finset.Icc 1 (2 * j), decoratedCorePathMass (κ := Fin k) (Fintype.card ι) C q R j b) /
        (k.factorial : ℝ) := by
  have habsf : |(k.factorial : ℝ)| = (k.factorial : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  rw [actualCoreExcessCoefficient, abs_div, habsf]
  have h := coreExcessCoordinateSum_abs_weighted_le_decorated_mass (κ := Fin k) B j hj C q R hC hn hR hB hq
  simp only [Fintype.card_fin] at h
  exact (by simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right h (Nat.cast_nonneg k.factorial))

end TournamentHamiltonian
