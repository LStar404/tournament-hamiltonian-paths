import TournamentHamiltonian.RectangularScaling

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
theorem rectangularPermanent_nonneg (X : Matrix ι κ ℝ) (hX : ∀ i j, 0 ≤ X i j) (e : ι ≃ κ) :
    0 ≤ rectangularPermanent X e :=
  matrix_permanent_nonneg_of_nonneg (X.submatrix id e) (fun i j => hX i (e j))

omit [DecidableEq κ] in
theorem rectangularPermanent_massNormalized_restoration (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (hM : 0 < matrixEntryMass X) (x : ι → ℝ) (y : κ → ℝ) :
    rectangularPermanent X e =
      Real.exp (-((∑ i, x i) + (∑ j, y j) +
        Fintype.card ι * Real.log (Fintype.card ι / matrixEntryMass X))) *
      rectangularPermanent (rectangularExpScaling (massNormalizedMatrix X) x y) e := by
  have hmass : matrixEntryMass (X.submatrix id e) = matrixEntryMass X :=
    matrixEntryMass_submatrix_equiv X (Equiv.refl ι) e
  have h := normalized_local_scaling_permanent_restoration (X.submatrix id e) hp
    (by rwa [hmass]) (Sum.elim x (y ∘ e))
  have hn : massNormalizedMatrix (X.submatrix id e) = (massNormalizedMatrix X).submatrix id e :=
    massNormalizedMatrix_submatrix_equiv X (Equiv.refl ι) e
  have hy : (∑ j, (y ∘ e) j) = ∑ j, y j := e.sum_comp y
  rw [hmass, hn] at h
  simp only [localScalingCapacity, Sum.elim_inl, Sum.elim_inr, hy] at h
  have hs : localScaledMatrix ((massNormalizedMatrix X).submatrix id e) (Sum.elim x (y ∘ e)) =
      (rectangularExpScaling (massNormalizedMatrix X) x y).submatrix id e := by
    ext i j
    simp only [localScaledMatrix, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
      rectangularExpScaling, Matrix.submatrix_apply, id_eq, Real.exp_add]
    ring
  rw [hs] at h
  exact h

omit [DecidableEq κ] in
theorem rectangularPermanent_massNormalized_upper (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (hX : ∀ i j, 0 ≤ X i j) (hM : 0 < matrixEntryMass X)
    (x : ι → ℝ) (y : κ → ℝ) (hcap : 0 ≤ (∑ i, x i) + ∑ j, y j) :
    rectangularPermanent X e ≤ Real.exp (matrixEntryMass X - Fintype.card ι) *
      rectangularPermanent (rectangularExpScaling (massNormalizedMatrix X) x y) e := by
  have hpR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hM hpR)) hpR.le
  have hl : Real.log (Fintype.card ι / matrixEntryMass X) =
      -Real.log (matrixEntryMass X / Fintype.card ι) := by
    rw [Real.log_div hpR.ne' hM.ne', Real.log_div hM.ne' hpR.ne']
    ring
  have hc : (Fintype.card ι : ℝ) * (matrixEntryMass X / Fintype.card ι - 1) =
      matrixEntryMass X - Fintype.card ι := by field_simp [hpR.ne']
  rw [hc] at hlog
  have ht : -((∑ i, x i) + (∑ j, y j) +
      Fintype.card ι * Real.log (Fintype.card ι / matrixEntryMass X)) ≤
      matrixEntryMass X - Fintype.card ι := by rw [hl]; linarith
  have hB (i j) : 0 ≤ rectangularExpScaling (massNormalizedMatrix X) x y i j :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hM.le) (hX i j))) (Real.exp_pos _).le
  rw [rectangularPermanent_massNormalized_restoration X e hp hM x y]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht) (rectangularPermanent_nonneg _ hB e)

theorem exists_normalized_rectangular_scaling_witness (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (hX : ∀ i j, 0 ≤ X i j) (hM : 0 < matrixEntryMass X)
    (K C q eps : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (heps : 0 ≤ eps)
    (hXentry : ∀ i j, |massNormalizedMatrix X i j| ≤ K / Fintype.card ι)
    (hentry : ∀ i j, |rectangularCenteredKernel (massNormalizedMatrix X) i j| ≤ C / Fintype.card ι)
    (hEq : ‖rectangularCenteredKernel (massNormalizedMatrix X)‖ ≤ q)
    (ha : ∀ i, |matrixRowError (massNormalizedMatrix X) i| ≤ eps)
    (hb : ∀ j, |matrixColumnError (massNormalizedMatrix X) j| ≤ eps)
    (hrow : ∀ i, ∑ j, |massNormalizedMatrix X i j| ≤ 2)
    (hcol : ∀ j, ∑ i, |massNormalizedMatrix X i j| ≤ 2)
    (hsmall : eps ≤ 1 / (256 * localScalingInverseBudget C q ^ 2))
    (hgap : eps ≤ (1 - q) / (2 * (32 * localScalingInverseBudget C q + 2))) :
    ∃ x : ι → ℝ, ∃ y : κ → ℝ,
      RectangularScalingWitness (massNormalizedMatrix X) e K C q eps x y ∧
      rectangularPermanent X e =
        Real.exp (-((∑ i, x i) + (∑ j, y j) +
          Fintype.card ι * Real.log (Fintype.card ι / matrixEntryMass X))) *
          rectangularPermanent (rectangularExpScaling (massNormalizedMatrix X) x y) e ∧
      rectangularPermanent X e ≤ Real.exp (matrixEntryMass X - Fintype.card ι) *
        rectangularPermanent (rectangularExpScaling (massNormalizedMatrix X) x y) e := by
  have hnormX (i j) : 0 ≤ massNormalizedMatrix X i j :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) hM.le) (hX i j)
  obtain ⟨x, y, hxy⟩ := exists_rectangular_scaling_witness (massNormalizedMatrix X) e hp hnormX
    (massNormalizedMatrix_mass X hM.ne') K C q eps hK hC hq0 hq1 heps hXentry hentry hEq
    ha hb hrow hcol hsmall hgap
  exact ⟨x, y, hxy, rectangularPermanent_massNormalized_restoration X e hp hM x y,
    rectangularPermanent_massNormalized_upper X e hp hX hM x y hxy.capacity_nonneg⟩

section DeletedSets

variable {η : Type*} [Fintype η] [DecidableEq η]

noncomputable def deletedComplementEquiv (I J : Finset η) (hIJ : I.card = J.card) :
    ↥Iᶜ ≃ ↥Jᶜ := Finset.equivOfCardEq (by rw [Finset.card_compl, Finset.card_compl, hIJ])

noncomputable def nonprincipalSubmatrix (X : Matrix η η ℝ) (I J : Finset η) :
    Matrix ↥Iᶜ ↥Jᶜ ℝ := X.submatrix Subtype.val Subtype.val

/-- Arbitrary distinct deleted row and column sets are square after an explicit
column equivalence. No equality between the selectors is required. -/
theorem exists_nonprincipal_scaling_witness (X : Matrix η η ℝ) (I J : Finset η)
    (hIJ : I.card = J.card) (hp : 0 < Fintype.card ↥Iᶜ)
    (hX : ∀ i : ↥Iᶜ, ∀ j : ↥Jᶜ, 0 ≤ X i j)
    (hmass : matrixEntryMass (nonprincipalSubmatrix X I J) = Fintype.card ↥Iᶜ)
    (K C q eps : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (heps : 0 ≤ eps)
    (hXentry : ∀ i : ↥Iᶜ, ∀ j : ↥Jᶜ, |X i j| ≤ K / Fintype.card ↥Iᶜ)
    (hentry : ∀ i j, |rectangularCenteredKernel (nonprincipalSubmatrix X I J) i j| ≤
      C / Fintype.card ↥Iᶜ)
    (hEq : ‖rectangularCenteredKernel (nonprincipalSubmatrix X I J)‖ ≤ q)
    (ha : ∀ i, |matrixRowError (nonprincipalSubmatrix X I J) i| ≤ eps)
    (hb : ∀ j, |matrixColumnError (nonprincipalSubmatrix X I J) j| ≤ eps)
    (hrow : ∀ i : ↥Iᶜ, ∑ j : ↥Jᶜ, |X i j| ≤ 2)
    (hcol : ∀ j : ↥Jᶜ, ∑ i : ↥Iᶜ, |X i j| ≤ 2)
    (hsmall : eps ≤ 1 / (256 * localScalingInverseBudget C q ^ 2))
    (hgap : eps ≤ (1 - q) / (2 * (32 * localScalingInverseBudget C q + 2))) :
    ∃ x : ↥Iᶜ → ℝ, ∃ y : ↥Jᶜ → ℝ,
      RectangularScalingWitness (nonprincipalSubmatrix X I J)
        (deletedComplementEquiv I J hIJ) K C q eps x y :=
  exists_rectangular_scaling_witness (nonprincipalSubmatrix X I J) (deletedComplementEquiv I J hIJ)
    hp hX hmass K C q eps hK hC hq0 hq1 heps hXentry hentry hEq ha hb hrow hcol hsmall hgap

end DeletedSets

end TournamentHamiltonian
