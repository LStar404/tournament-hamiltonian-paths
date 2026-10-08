import TournamentHamiltonian.PartitionComponentAssembly

/-! A finite bijection between actual partition graphs and their Wick/core decomposition. -/

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable (κ : Type*) [Fintype κ] [DecidableEq κ]

abbrev PairingPartitionPair :=
  {PQ : Setoid κ × Setoid κ // IsPairingPartition PQ.1 ∧ IsPairingPartition PQ.2}

abbrev CorePartitionPair :=
  {PQ : Setoid κ × Setoid κ // ∀ e, ¬ IsPureDegreeTwoComponent PQ.1 PQ.2 e}

abbrev PureCoreDecomposition :=
  Σ s : Set κ, PairingPartitionPair {e // s e} × CorePartitionPair {e // ¬s e}

variable {κ}

noncomputable def assemblePureCore (d : PureCoreDecomposition κ) : Setoid κ × Setoid κ :=
  (assembleSubsetPartition d.1 d.2.1.val.1 d.2.2.val.1,
    assembleSubsetPartition d.1 d.2.1.val.2 d.2.2.val.2)

noncomputable def extractPureCore (PQ : Setoid κ × Setoid κ) : PureCoreDecomposition κ :=
  ⟨{e | IsPureDegreeTwoComponent PQ.1 PQ.2 e},
    ⟨⟨(pureRowPartition PQ.1 PQ.2, pureColumnPartition PQ.1 PQ.2),
      pureRowPartition_isPairing PQ.1 PQ.2, pureColumnPartition_isPairing PQ.1 PQ.2⟩,
    ⟨(coreRowPartition PQ.1 PQ.2, coreColumnPartition PQ.1 PQ.2),
      coreComponent_no_pure_component PQ.1 PQ.2⟩⟩⟩

omit [DecidableEq κ] in
theorem assemble_extractPureCore (PQ : Setoid κ × Setoid κ) :
    assemblePureCore (extractPureCore PQ) = PQ := by
  apply Prod.ext
  · exact coreComponent_row_reassembly PQ.1 PQ.2
  · exact coreComponent_column_reassembly PQ.1 PQ.2

omit [DecidableEq κ] in
theorem assemblePureCore_pure_iff (d : PureCoreDecomposition κ) (e : κ) :
    IsPureDegreeTwoComponent (assemblePureCore d).1 (assemblePureCore d).2 e ↔ d.1 e :=
  assembleSubsetPair_pure_iff d.1 d.2.1.val.1 d.2.1.val.2 d.2.2.val.1 d.2.2.val.2
    d.2.1.property.1 d.2.1.property.2 d.2.2.property e

omit [DecidableEq κ] in
theorem assemblePureCore_injective : Function.Injective (assemblePureCore (κ := κ)) := by
  intro a b hab
  have hs : a.1 = b.1 := by
    apply Set.ext
    intro e
    have ha := assemblePureCore_pure_iff a e
    rw [hab] at ha
    exact ha.symm.trans (assemblePureCore_pure_iff b e)
  rcases a with ⟨s, ⟨⟨⟨P, R⟩, hPR⟩, ⟨⟨Q, S⟩, hQS⟩⟩⟩
  rcases b with ⟨t, ⟨⟨⟨P', R'⟩, hPR'⟩, ⟨⟨Q', S'⟩, hQS'⟩⟩⟩
  change s = t at hs
  cases hs
  have hrow := congrArg Prod.fst hab
  have hcol := congrArg Prod.snd hab
  change assembleSubsetPartition s P Q = assembleSubsetPartition s P' Q' at hrow
  change assembleSubsetPartition s R S = assembleSubsetPartition s R' S' at hcol
  have hp : P = P' := by
    have h := congrArg (Setoid.comap (Subtype.val : {e // s e} → κ)) hrow
    simpa only [assembleSubsetPartition_comap_pos] using h
  have hq : Q = Q' := by
    have h := congrArg (Setoid.comap (Subtype.val : {e // ¬s e} → κ)) hrow
    simpa only [assembleSubsetPartition_comap_neg] using h
  have hr : R = R' := by
    have h := congrArg (Setoid.comap (Subtype.val : {e // s e} → κ)) hcol
    simpa only [assembleSubsetPartition_comap_pos] using h
  have ht : S = S' := by
    have h := congrArg (Setoid.comap (Subtype.val : {e // ¬s e} → κ)) hcol
    simpa only [assembleSubsetPartition_comap_neg] using h
  subst P'; subst Q'; subst R'; subst S'
  rfl

omit [DecidableEq κ] in
theorem assemblePureCore_surjective : Function.Surjective (assemblePureCore (κ := κ)) :=
  fun PQ => ⟨extractPureCore PQ, assemble_extractPureCore PQ⟩

noncomputable def pureCoreDecompositionEquiv : PureCoreDecomposition κ ≃ (Setoid κ × Setoid κ) :=
  Equiv.ofBijective assemblePureCore ⟨assemblePureCore_injective, assemblePureCore_surjective⟩

variable {ι : Type*} [Fintype ι]
open scoped BigOperators

theorem assemblePureCore_weight (B : Matrix ι ι ℝ) (d : PureCoreDecomposition κ) :
    IncidenceAlgebra.mu ℝ ⊥ (assemblePureCore d).1 *
      IncidenceAlgebra.mu ℝ ⊥ (assemblePureCore d).2 *
        partitionContraction B (assemblePureCore d).1 (assemblePureCore d).2 =
      partitionContraction B d.2.1.val.1 d.2.1.val.2 *
        (IncidenceAlgebra.mu ℝ ⊥ d.2.2.val.1 * IncidenceAlgebra.mu ℝ ⊥ d.2.2.val.2 *
          partitionContraction B d.2.2.val.1 d.2.2.val.2) := by
  rcases d with ⟨s, ⟨⟨⟨P, R⟩, hPR⟩, ⟨⟨Q, S⟩, hQS⟩⟩⟩
  change IncidenceAlgebra.mu ℝ ⊥ (assembleSubsetPartition s P Q) *
    IncidenceAlgebra.mu ℝ ⊥ (assembleSubsetPartition s R S) *
    partitionContraction B (assembleSubsetPartition s P Q) (assembleSubsetPartition s R S) = _
  have hp := partition_mu_invariant_subset (R := ℝ) (assembleSubsetPartition s P Q) s
    (assembleSubsetPartition_invariant s P Q)
  have hr := partition_mu_invariant_subset (R := ℝ) (assembleSubsetPartition s R S) s
    (assembleSubsetPartition_invariant s R S)
  have ht := partitionContraction_invariant_subset B (assembleSubsetPartition s P Q)
    (assembleSubsetPartition s R S) s (assembleSubsetPartition_invariant s P Q)
      (assembleSubsetPartition_invariant s R S)
  simp only [assembleSubsetPartition_comap_pos, assembleSubsetPartition_comap_neg] at hp hr ht
  rw [hp, hr, ht]
  calc
    _ = (IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ R) *
      (partitionContraction B P R *
        (IncidenceAlgebra.mu ℝ ⊥ Q * IncidenceAlgebra.mu ℝ ⊥ S * partitionContraction B Q S)) := by ring
    _ = _ := by rw [pair_partition_mu_product P R hPR.1 hPR.2, one_mul]

/-- An exact finite component identity. The Wick and signed core sums are indexed by actual complementary edge subsets. -/
theorem partitionGraphSum_pure_core_decomposition (B : Matrix ι ι ℝ) :
    (∑ P : Setoid κ, ∑ Q : Setoid κ,
      IncidenceAlgebra.mu ℝ ⊥ P * IncidenceAlgebra.mu ℝ ⊥ Q * partitionContraction B P Q) =
      ∑ s : Set κ,
        (∑ p : PairingPartitionPair {e // s e}, partitionContraction B p.val.1 p.val.2) *
        (∑ c : CorePartitionPair {e // ¬s e},
          IncidenceAlgebra.mu ℝ ⊥ c.val.1 * IncidenceAlgebra.mu ℝ ⊥ c.val.2 *
            partitionContraction B c.val.1 c.val.2) := by
  calc
    _ = ∑ PQ : Setoid κ × Setoid κ,
        IncidenceAlgebra.mu ℝ ⊥ PQ.1 * IncidenceAlgebra.mu ℝ ⊥ PQ.2 *
          partitionContraction B PQ.1 PQ.2 :=
      (Fintype.sum_prod_type (fun PQ : Setoid κ × Setoid κ =>
        IncidenceAlgebra.mu ℝ ⊥ PQ.1 * IncidenceAlgebra.mu ℝ ⊥ PQ.2 *
          partitionContraction B PQ.1 PQ.2)).symm
    _ = ∑ d : PureCoreDecomposition κ,
        IncidenceAlgebra.mu ℝ ⊥ (assemblePureCore d).1 *
          IncidenceAlgebra.mu ℝ ⊥ (assemblePureCore d).2 *
            partitionContraction B (assemblePureCore d).1 (assemblePureCore d).2 :=
      (Fintype.sum_equiv pureCoreDecompositionEquiv _ _ (fun _ => rfl)).symm
    _ = ∑ d : PureCoreDecomposition κ,
        partitionContraction B d.2.1.val.1 d.2.1.val.2 *
          (IncidenceAlgebra.mu ℝ ⊥ d.2.2.val.1 * IncidenceAlgebra.mu ℝ ⊥ d.2.2.val.2 *
            partitionContraction B d.2.2.val.1 d.2.2.val.2) := by
      apply Finset.sum_congr rfl
      intro d _
      exact assemblePureCore_weight B d
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

end TournamentHamiltonian
