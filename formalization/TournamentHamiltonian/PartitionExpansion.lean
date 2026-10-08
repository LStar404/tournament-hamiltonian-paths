import TournamentHamiltonian.PermanentExpansion
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Setoid.Partition

/-! The finite partition-lattice expansion and singleton cancellation in §3.2. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

noncomputable instance coordinatePartitionFintype {κ : Type*} [Fintype κ] :
    Fintype (Setoid κ) := by
  classical
  exact Fintype.ofInjective (fun P : Setoid κ => P.r)
    (fun P Q h => Setoid.ext (fun i j => by
      have hr := congrArg (fun r : κ → κ → Prop => r i j) h
      exact iff_of_eq hr))

noncomputable instance coordinatePartitionLocallyFinite {κ : Type*} [Fintype κ] :
    LocallyFiniteOrder (Setoid κ) := by
  classical
  exact Fintype.toLocallyFiniteOrder

/-- General finite-fiber form of Möbius inversion, specialized at the bottom. -/
theorem moebius_fiber_bottom {X Λ R : Type*} [Fintype X] [Fintype Λ]
    [PartialOrder Λ] [BoundedOrder Λ] [LocallyFiniteOrder Λ] [CommRing R]
    (g : X → Λ) (w : X → R) :
    (∑ x ∈ Finset.univ.filter (fun x => g x = ⊥), w x) =
      ∑ P : Λ, IncidenceAlgebra.mu R ⊥ P *
        ∑ x ∈ Finset.univ.filter (fun x => P ≤ g x), w x := by
  classical
  let f (P : Λ) := ∑ x ∈ Finset.univ.filter (fun x => g x = P), w x
  let h (P : Λ) := ∑ x ∈ Finset.univ.filter (fun x => P ≤ g x), w x
  have hh (P : Λ) : h P = ∑ Q ∈ Finset.Ici P, f Q := by
    simpa [h, f, Finset.mem_Ici] using
      (Finset.sum_fiberwise_eq_sum_filter Finset.univ (Finset.Ici P) g w).symm
  simpa [f, h] using IncidenceAlgebra.moebius_inversion_top f h hh ⊥

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommRing R]

/-- Assign independent numerical labels to each row and column partition block.
No distinctness condition is imposed on labels of different blocks. -/
noncomputable def partitionContraction (B : Matrix ι ι R) (P Q : Setoid κ) : R := by
  classical
  exact ∑ r : Quotient P → ι, ∑ c : Quotient Q → ι,
    ∏ i : κ, B (r (Quotient.mk P i)) (c (Quotient.mk Q i))

omit [DecidableEq ι] in
private theorem sum_block_labels (P : Setoid κ) (w : (κ → ι) → R) :
    (∑ r : Quotient P → ι, w (r ∘ Quotient.mk P)) =
      ∑ r ∈ Finset.univ.filter (fun r : κ → ι => P ≤ Setoid.ker r), w r := by
  classical
  calc
    _ = ∑ r : {r : κ → ι // P ≤ Setoid.ker r}, w r := by
      apply (Fintype.sum_equiv (Setoid.liftEquiv P) _ _ ?_).symm
      intro r
      congr 1
    _ = _ := (Finset.sum_subtype _ (by simp) w).symm

omit [DecidableEq ι] in
theorem partitionContraction_eq_constrained_sum (B : Matrix ι ι R) (P Q : Setoid κ) :
    partitionContraction B P Q =
      ∑ r ∈ Finset.univ.filter (fun r : κ → ι => P ≤ Setoid.ker r),
        ∑ c ∈ Finset.univ.filter (fun c : κ → ι => Q ≤ Setoid.ker c),
          ∏ i : κ, B (r i) (c i) := by
  classical
  unfold partitionContraction
  calc
    _ = ∑ r : Quotient P → ι,
        ∑ c ∈ Finset.univ.filter (fun c : κ → ι => Q ≤ Setoid.ker c),
          ∏ i : κ, B (r (Quotient.mk P i)) (c i) := by
      apply Finset.sum_congr rfl
      intro r _
      exact sum_block_labels Q (fun c : κ → ι => ∏ i : κ, B (r (Quotient.mk P i)) (c i))
    _ = _ := sum_block_labels P (fun r : κ → ι =>
      ∑ c ∈ Finset.univ.filter (fun c : κ → ι => Q ≤ Setoid.ker c),
        ∏ i : κ, B (r i) (c i))

private theorem sum_embeddings_eq_injective_sum (w : (κ → ι) → R) :
    (∑ r : κ ↪ ι, w r) =
      ∑ r ∈ Finset.univ.filter (fun r : κ → ι => Function.Injective r), w r := by
  classical
  calc
    _ = ∑ r : {r : κ → ι // Function.Injective r}, w r := by
      apply (Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding κ ι)
        _ _ (fun _ => rfl)).symm
    _ = _ := (Finset.sum_subtype _ (by simp) w).symm

private theorem injective_sum_moebius (w : (κ → ι) → R) :
    (∑ r ∈ Finset.univ.filter (fun r : κ → ι => Function.Injective r), w r) =
      ∑ P : Setoid κ, IncidenceAlgebra.mu R ⊥ P *
        ∑ r ∈ Finset.univ.filter (fun r : κ → ι => P ≤ Setoid.ker r), w r := by
  classical
  simpa only [Setoid.ker_eq_bot_iff] using
    moebius_fiber_bottom (fun r : κ → ι => Setoid.ker r) w

private theorem injective_sum_partition_moebius
    (w : (κ → ι) → (κ → ι) → R) :
    (∑ r ∈ Finset.univ.filter (fun r : κ → ι => Function.Injective r),
      ∑ c ∈ Finset.univ.filter (fun c : κ → ι => Function.Injective c), w r c) =
      ∑ P : Setoid κ, ∑ Q : Setoid κ,
        IncidenceAlgebra.mu R ⊥ P * IncidenceAlgebra.mu R ⊥ Q *
          ∑ r ∈ Finset.univ.filter (fun r : κ → ι => P ≤ Setoid.ker r),
            ∑ c ∈ Finset.univ.filter (fun c : κ → ι => Q ≤ Setoid.ker c), w r c := by
  classical
  simp_rw [injective_sum_moebius]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q _
  rw [← Finset.mul_sum]
  ring

/-- The genuine partition-lattice Möbius expansion of the distinct-coordinate sum. -/
theorem distinctCoordinateSum_partition_expansion (B : Matrix ι ι R) (k : ℕ) :
    distinctCoordinateSum B k =
      ∑ P : Setoid (Fin k), ∑ Q : Setoid (Fin k),
        IncidenceAlgebra.mu R ⊥ P * IncidenceAlgebra.mu R ⊥ Q *
          partitionContraction B P Q := by
  classical
  have hinj : distinctCoordinateSum B k =
      ∑ r ∈ Finset.univ.filter (fun r : Fin k → ι => Function.Injective r),
        ∑ c ∈ Finset.univ.filter (fun c : Fin k → ι => Function.Injective c),
          ∏ i : Fin k, B (r i) (c i) := by
    unfold distinctCoordinateSum
    rw [Finset.sum_comm]
    calc
      _ = ∑ r : Fin k ↪ ι,
          ∑ c ∈ Finset.univ.filter (fun c : Fin k → ι => Function.Injective c),
            ∏ i : Fin k, B (r i) (c i) := by
        apply Finset.sum_congr rfl
        intro r _
        exact sum_embeddings_eq_injective_sum (fun c : Fin k → ι => ∏ i : Fin k, B (r i) (c i))
      _ = _ := sum_embeddings_eq_injective_sum (fun r : Fin k → ι =>
        ∑ c ∈ Finset.univ.filter (fun c : Fin k → ι => Function.Injective c),
          ∏ i : Fin k, B (r i) (c i))
  rw [hinj]
  rw [injective_sum_partition_moebius (fun r c : Fin k → ι => ∏ i : Fin k, B (r i) (c i))]
  apply Finset.sum_congr rfl
  intro P _
  apply Finset.sum_congr rfl
  intro Q _
  exact congrArg (fun v => IncidenceAlgebra.mu R ⊥ P * IncidenceAlgebra.mu R ⊥ Q * v)
    (partitionContraction_eq_constrained_sum B P Q).symm

omit [DecidableEq ι] in
private theorem sum_labels_singleton_factor {V : Type*} [Fintype V] [DecidableEq V]
    (u : κ → V) (e : κ) (hu : ∀ i, u i = u e → i = e)
    (f : κ → ι → R) (hf : (∑ a : ι, f e a) = 0) :
    (∑ r : V → ι, ∏ i : κ, f i (r (u i))) = 0 := by
  classical
  let split := Equiv.funSplitAt (u e) ι
  let rest (t : {v : V // v ≠ u e} → ι) : R :=
    ∏ i : {i : κ // i ≠ e},
      f i (t ⟨u i, fun h => i.property (hu i h)⟩)
  have hp (a : ι) (t : {v : V // v ≠ u e} → ι) :
      (∏ i : κ, f i (split.symm (a, t) (u i))) = f e a * rest t := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ e]
    have he : split.symm (a, t) (u e) = a := by
      simp [split, Equiv.funSplitAt, Equiv.piSplitAt]
    rw [he]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    have hi : u i ≠ u e := fun h => i.property (hu i h)
    simp [split, Equiv.funSplitAt, Equiv.piSplitAt, hi]
  calc
    _ = ∑ x : ι × ({v : V // v ≠ u e} → ι),
        ∏ i : κ, f i (split.symm x (u i)) := by
      exact (Fintype.sum_equiv split.symm _ _ (fun _ => rfl)).symm
    _ = ∑ a : ι, ∑ t : {v : V // v ≠ u e} → ι, f e a * rest t := by
      rw [Fintype.sum_prod_type]
      simp_rw [hp]
    _ = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro t _
      rw [← Finset.sum_mul, hf, zero_mul]

/-- A singleton block in the partition of edge labels is a graph vertex of degree one. -/
def HasSingletonClass (P : Setoid κ) : Prop :=
  ∃ e : κ, ∀ i : κ, P i e → i = e

omit [DecidableEq ι] in
/-- Summing the independent label of a singleton row block gives a column sum of `B`. -/
theorem partitionContraction_eq_zero_of_row_singleton (B : Matrix ι ι R)
    (P Q : Setoid κ) (hB : ∀ j, (∑ i : ι, B i j) = 0)
    (hP : HasSingletonClass P) : partitionContraction B P Q = 0 := by
  classical
  obtain ⟨e, he⟩ := hP
  unfold partitionContraction
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  apply sum_labels_singleton_factor (fun i => Quotient.mk P i) e
    (fun i h => he i (Quotient.exact h))
    (fun i a => B a (c (Quotient.mk Q i)))
  exact hB _

omit [DecidableEq ι] in
/-- Summing the independent label of a singleton column block gives a row sum of `B`. -/
theorem partitionContraction_eq_zero_of_column_singleton (B : Matrix ι ι R)
    (P Q : Setoid κ) (hB : ∀ i, (∑ j : ι, B i j) = 0)
    (hQ : HasSingletonClass Q) : partitionContraction B P Q = 0 := by
  classical
  obtain ⟨e, he⟩ := hQ
  unfold partitionContraction
  apply Finset.sum_eq_zero
  intro r _
  apply sum_labels_singleton_factor (fun i => Quotient.mk Q i) e
    (fun i h => he i (Quotient.exact h))
    (fun i a => B (r (Quotient.mk P i)) a)
  exact hB _

/-- In a singleton-free partition, every graph vertex has degree at least two. -/
theorem singletonFree_block_card_ge_two (P : Setoid κ) (hP : ¬ HasSingletonClass P) (e : κ) :
    2 ≤ (Finset.univ.filter (fun i : κ => P i e)).card := by
  classical
  have hex : ∃ i : κ, P i e ∧ i ≠ e := by
    by_contra h
    apply hP
    refine ⟨e, fun i hi => ?_⟩
    by_contra hne
    exact h ⟨i, hi, hne⟩
  obtain ⟨i, hi, hne⟩ := hex
  apply Finset.Nontrivial.two_le_card
  exact ⟨i, by simp [hi], e, by simp, hne⟩

/-- Centering removes every graph with a vertex of degree one, exactly and in each finite degree. -/
theorem distinctCoordinateSum_centered_partition_expansion (B : Matrix ι ι R) (k : ℕ)
    (hrow : ∀ i, (∑ j : ι, B i j) = 0) (hcol : ∀ j, (∑ i : ι, B i j) = 0) :
    distinctCoordinateSum B k =
      ∑ P ∈ Finset.univ.filter (fun P : Setoid (Fin k) => ¬ HasSingletonClass P),
        ∑ Q ∈ Finset.univ.filter (fun Q : Setoid (Fin k) => ¬ HasSingletonClass Q),
          IncidenceAlgebra.mu R ⊥ P * IncidenceAlgebra.mu R ⊥ Q *
            partitionContraction B P Q := by
  classical
  rw [distinctCoordinateSum_partition_expansion]
  symm
  calc
    _ = ∑ P ∈ Finset.univ.filter (fun P : Setoid (Fin k) => ¬ HasSingletonClass P),
        ∑ Q : Setoid (Fin k),
          IncidenceAlgebra.mu R ⊥ P * IncidenceAlgebra.mu R ⊥ Q *
            partitionContraction B P Q := by
      apply Finset.sum_congr rfl
      intro P _
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro Q _ hQ
      have hsingle : HasSingletonClass Q := by simpa using hQ
      rw [partitionContraction_eq_zero_of_column_singleton B P Q hrow hsingle, mul_zero]
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro P _ hP
      have hsingle : HasSingletonClass P := by simpa using hP
      apply Finset.sum_eq_zero
      intro Q _
      rw [partitionContraction_eq_zero_of_row_singleton B P Q hcol hsingle, mul_zero]

theorem permanentMinorSum_partition_expansion {K : Type*} [Field K] [CharZero K]
    (B : Matrix ι ι K) (k : ℕ) :
    permanentMinorSum B k =
      (∑ P : Setoid (Fin k), ∑ Q : Setoid (Fin k),
        IncidenceAlgebra.mu K ⊥ P * IncidenceAlgebra.mu K ⊥ Q *
          partitionContraction B P Q) / (k.factorial : K) := by
  rw [permanentMinorSum_eq_distinctCoordinateSum_div_factorial,
    distinctCoordinateSum_partition_expansion]

theorem normalized_coeff_partition_expansion {K : Type*} [Field K] [CharZero K]
    (E : Matrix ι ι K) (k : ℕ) :
    (((Fintype.card ι).descFactorial k : K) / (Fintype.card ι : K) ^ k) *
        (normalizedPermanentPolynomial E).coeff k =
      (∑ P : Setoid (Fin k), ∑ Q : Setoid (Fin k),
        IncidenceAlgebra.mu K ⊥ P * IncidenceAlgebra.mu K ⊥ Q *
          partitionContraction (fun i j => E i j / (Fintype.card ι : K)) P Q) /
        (k.factorial : K) := by
  rw [normalized_coeff_rescaling]
  exact permanentMinorSum_partition_expansion _ _

/-- The number of edge labels incident to a particular partition block. -/
noncomputable def coordinatePartitionDegree (P : Setoid κ) (v : Quotient P) : ℕ :=
  (Finset.univ.filter (fun i : κ => Quotient.mk P i = v)).card

theorem singletonFree_coordinateDegree_ge_two (P : Setoid κ) (hP : ¬ HasSingletonClass P)
    (v : Quotient P) : 2 ≤ coordinatePartitionDegree P v := by
  classical
  induction v using Quotient.inductionOn with
  | h e =>
    simpa only [coordinatePartitionDegree, Quotient.eq] using
      singletonFree_block_card_ge_two P hP e

/-- The partition sum cancels exactly above the number of available numerical labels. -/
theorem partition_expansion_eq_zero_of_lt (B : Matrix ι ι R) (k : ℕ)
    (hk : Fintype.card ι < k) :
    (∑ P : Setoid (Fin k), ∑ Q : Setoid (Fin k),
      IncidenceAlgebra.mu R ⊥ P * IncidenceAlgebra.mu R ⊥ Q *
        partitionContraction B P Q) = 0 := by
  rw [← distinctCoordinateSum_partition_expansion, distinctCoordinateSum_eq_zero_of_lt B k hk]

theorem partition_expansion_degree_zero (B : Matrix ι ι R) :
    (∑ P : Setoid (Fin 0), ∑ Q : Setoid (Fin 0),
      IncidenceAlgebra.mu R ⊥ P * IncidenceAlgebra.mu R ⊥ Q *
        partitionContraction B P Q) = 1 := by
  rw [← distinctCoordinateSum_partition_expansion, distinctCoordinateSum_zero]

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem partitionContraction_isEmpty [IsEmpty κ]
    (B : Matrix ι ι R) (P Q : Setoid κ) : partitionContraction B P Q = 1 := by
  classical
  simp [partitionContraction]

end TournamentHamiltonian
