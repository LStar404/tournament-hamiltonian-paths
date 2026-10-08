import TournamentHamiltonian.GaussianCoreCoefficients

/-! Actual surviving graphs have positive excess unless all their blocks are Wick pairs. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem pairingPartition_no_singleton (P : Setoid κ) (hP : IsPairingPartition P) :
    ¬ HasSingletonClass P := by
  rintro ⟨e, he⟩
  have hc := (isPairingPartition_iff_class_card P).mp hP e
  have hs : partitionClass P e = {e} := by
    ext i
    simp only [partitionClass, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact ⟨fun hi => he i (P.symm hi), fun hi => hi ▸ P.refl e⟩
  rw [hs, Finset.card_singleton] at hc
  omega

omit [DecidableEq κ] in
theorem coordinatePartitionDegree_sum (P : Setoid κ) :
    (∑ v : Quotient P, coordinatePartitionDegree P v) = Fintype.card κ := by
  simpa only [← partitionBlock_card_eq_degree] using partition_block_card_sum P

theorem singletonFree_partition_vertex_bound (P : Setoid κ) (hP : ¬ HasSingletonClass P) :
    2 * Fintype.card (Quotient P) ≤ Fintype.card κ := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun v _ => singletonFree_coordinateDegree_ge_two P hP v)
  simpa [coordinatePartitionDegree_sum, mul_comm] using h

theorem singletonFree_partition_vertex_strict (P : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hpair : ¬ IsPairingPartition P) :
    2 * Fintype.card (Quotient P) < Fintype.card κ := by
  have hex : ∃ v : Quotient P, 2 < coordinatePartitionDegree P v := by
    by_contra h
    apply hpair
    intro v
    rw [partitionBlock_card_eq_degree]
    have hd := singletonFree_coordinateDegree_ge_two P hP v
    have hn : ¬ 2 < coordinatePartitionDegree P v := fun hv => h ⟨v, hv⟩
    omega
  obtain ⟨v, hv⟩ := hex
  have h := Finset.sum_lt_sum
    (fun w (_ : w ∈ (Finset.univ : Finset (Quotient P))) =>
      singletonFree_coordinateDegree_ge_two P hP w)
    ⟨v, Finset.mem_univ v, hv⟩
  simpa [coordinatePartitionDegree_sum, mul_comm] using h

/-- A surviving graph which is not a union of degree-two components has positive excess. -/
theorem nonPairing_graph_positive_excess (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hpair : ¬ (IsPairingPartition P ∧ IsPairingPartition Q)) :
    Fintype.card (Quotient P) + Fintype.card (Quotient Q) < Fintype.card κ := by
  have hp := singletonFree_partition_vertex_bound P hP
  have hq := singletonFree_partition_vertex_bound Q hQ
  by_cases hpp : IsPairingPartition P
  · have hqq : ¬ IsPairingPartition Q := fun hh => hpair ⟨hpp, hh⟩
    have hqs := singletonFree_partition_vertex_strict Q hQ hqq
    omega
  · have hps := singletonFree_partition_vertex_strict P hP hpp
    omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem nonPairingCoordinateSum_centered (B : Matrix ι ι ℝ) (k : ℕ)
    (hrow : ∀ i, (∑ j : ι, B i j) = 0) (hcol : ∀ j, (∑ i : ι, B i j) = 0) :
    nonPairingCoordinateSum B k =
      ∑ P ∈ Finset.univ.filter (fun P : Setoid (Fin k) => ¬ HasSingletonClass P),
        ∑ Q ∈ Finset.univ.filter (fun Q : Setoid (Fin k) => ¬ HasSingletonClass Q),
          if IsPairingPartition P ∧ IsPairingPartition Q then 0 else
            IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ Q *
              partitionContraction B P Q := by
  unfold nonPairingCoordinateSum
  symm
  calc
    _ = ∑ P ∈ Finset.univ.filter (fun P : Setoid (Fin k) => ¬ HasSingletonClass P),
        ∑ Q : Setoid (Fin k),
          if IsPairingPartition P ∧ IsPairingPartition Q then 0 else
            IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ Q *
              partitionContraction B P Q := by
      apply Finset.sum_congr rfl
      intro P _
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro Q _ hQ
      have hsingle : HasSingletonClass Q := by simpa using hQ
      split_ifs
      · rfl
      · rw [partitionContraction_eq_zero_of_column_singleton B P Q hrow hsingle, mul_zero]
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro P _ hP
      have hsingle : HasSingletonClass P := by simpa using hP
      apply Finset.sum_eq_zero
      intro Q _
      split_ifs
      · rfl
      · rw [partitionContraction_eq_zero_of_row_singleton B P Q hcol hsingle, mul_zero]

omit [DecidableEq κ] [DecidableEq ι] in
theorem partitionContraction_abs_le (B : Matrix ι ι ℝ) (P Q : Setoid κ)
    (M : ℝ) (hB : ∀ i j, |B i j| ≤ M) :
    |partitionContraction B P Q| ≤
      (Fintype.card ι : ℝ) ^ (Fintype.card (Quotient P) + Fintype.card (Quotient Q)) *
        M ^ Fintype.card κ := by
  unfold partitionContraction
  calc
    _ ≤ ∑ r : Quotient P → ι, |∑ c : Quotient Q → ι,
        ∏ e : κ, B (r (Quotient.mk P e)) (c (Quotient.mk Q e))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Quotient P → ι, ∑ _c : Quotient Q → ι, M ^ Fintype.card κ := by
      apply Finset.sum_le_sum
      intro r _
      calc
        _ ≤ ∑ c : Quotient Q → ι,
            |∏ e : κ, B (r (Quotient.mk P e)) (c (Quotient.mk Q e))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro c _
          rw [Finset.abs_prod]
          calc
            _ ≤ ∏ _e : κ, M :=
              Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
                (fun e _ => hB (r (Quotient.mk P e)) (c (Quotient.mk Q e)))
            _ = M ^ Fintype.card κ := by simp
    _ = _ := by simp [Nat.cast_pow, pow_add]; ring

private theorem vertex_scaling_identity (n C : ℝ) (hn : n ≠ 0) (k v : ℕ) (hv : v ≤ k) :
    n ^ v * (C / n) ^ k = C ^ k / n ^ (k - v) := by
  rw [div_pow, show n ^ k = n ^ (k - v) * n ^ v by
    rw [← pow_add, Nat.sub_add_cancel hv]]
  field_simp

omit [DecidableEq ι] in
/-- An actual nonpairing graph with centered entries bounded by `C/n` loses at least one label. -/
theorem nonPairing_partitionContraction_abs_le (B : Matrix ι ι ℝ) (P Q : Setoid κ)
    (C : ℝ) (hC : 0 ≤ C) (hn : 0 < Fintype.card ι)
    (hB : ∀ i j, |B i j| ≤ C / (Fintype.card ι : ℝ))
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hpair : ¬ (IsPairingPartition P ∧ IsPairingPartition Q)) :
    |partitionContraction B P Q| ≤ C ^ Fintype.card κ / (Fintype.card ι : ℝ) := by
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hv := nonPairing_graph_positive_excess P Q hP hQ hpair
  have hj : 1 ≤ Fintype.card κ -
      (Fintype.card (Quotient P) + Fintype.card (Quotient Q)) := by omega
  calc
    _ ≤ (Fintype.card ι : ℝ) ^
        (Fintype.card (Quotient P) + Fintype.card (Quotient Q)) *
        (C / (Fintype.card ι : ℝ)) ^ Fintype.card κ := partitionContraction_abs_le B P Q _ hB
    _ = C ^ Fintype.card κ / (Fintype.card ι : ℝ) ^
        (Fintype.card κ - (Fintype.card (Quotient P) + Fintype.card (Quotient Q))) :=
      vertex_scaling_identity _ _ hnpos.ne' _ _ hv.le
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (pow_nonneg hC _) hnpos
      simpa using pow_le_pow_right₀ hn1 hj

/-- A dimension-independent finite partition weight mass in a fixed edge degree. -/
noncomputable def nonPairingWeightMass (k : ℕ) : ℝ :=
  ∑ P ∈ Finset.univ.filter (fun P : Setoid (Fin k) => ¬ HasSingletonClass P),
    ∑ Q ∈ Finset.univ.filter (fun Q : Setoid (Fin k) => ¬ HasSingletonClass Q),
      if IsPairingPartition P ∧ IsPairingPartition Q then 0 else
        |IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ Q|

theorem nonPairingWeightMass_nonneg (k : ℕ) : 0 ≤ nonPairingWeightMass k := by
  apply Finset.sum_nonneg
  intro P _
  apply Finset.sum_nonneg
  intro Q _
  split_ifs
  · rfl
  · exact abs_nonneg _

omit [DecidableEq ι] in
/-- The genuine coefficient remainder has an explicit fixed-degree bound.
The weight mass depends on the degree; this does not assert a bound in a linear degree window. -/
theorem nonPairingCoordinateSum_abs_le (B : Matrix ι ι ℝ) (k : ℕ)
    (C : ℝ) (hC : 0 ≤ C) (hn : 0 < Fintype.card ι)
    (hB : ∀ i j, |B i j| ≤ C / (Fintype.card ι : ℝ))
    (hrow : ∀ i, (∑ j : ι, B i j) = 0) (hcol : ∀ j, (∑ i : ι, B i j) = 0) :
    |nonPairingCoordinateSum B k| ≤ nonPairingWeightMass k *
      (C ^ k / (Fintype.card ι : ℝ)) := by
  rw [nonPairingCoordinateSum_centered B k hrow hcol]
  calc
    _ ≤ ∑ P ∈ Finset.univ.filter (fun P : Setoid (Fin k) => ¬ HasSingletonClass P),
        |∑ Q ∈ Finset.univ.filter (fun Q : Setoid (Fin k) => ¬ HasSingletonClass Q),
          if IsPairingPartition P ∧ IsPairingPartition Q then 0 else
            IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ Q *
              partitionContraction B P Q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ P ∈ Finset.univ.filter (fun P : Setoid (Fin k) => ¬ HasSingletonClass P),
        ∑ Q ∈ Finset.univ.filter (fun Q : Setoid (Fin k) => ¬ HasSingletonClass Q),
          (if IsPairingPartition P ∧ IsPairingPartition Q then 0 else
            |IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ Q|) *
            (C ^ k / (Fintype.card ι : ℝ)) := by
      apply Finset.sum_le_sum
      intro P hP
      calc
        _ ≤ ∑ Q ∈ Finset.univ.filter (fun Q : Setoid (Fin k) => ¬ HasSingletonClass Q),
            |if IsPairingPartition P ∧ IsPairingPartition Q then 0 else
              IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ Q *
                partitionContraction B P Q| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro Q hQ
          split_ifs with hpair
          · simp
          · rw [abs_mul]
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            simpa only [Fintype.card_fin] using
              nonPairing_partitionContraction_abs_le B P Q C hC hn hB
                (Finset.mem_filter.mp hP).2 (Finset.mem_filter.mp hQ).2 hpair
    _ = _ := by simp only [nonPairingWeightMass, Finset.sum_mul]

end TournamentHamiltonian
