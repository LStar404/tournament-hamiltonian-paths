import TournamentHamiltonian.RectangularReindexing

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def rectangularAverageMatrix (ι κ : Type*) [Fintype ι] : Matrix ι κ ℝ :=
  fun _ _ => (Fintype.card ι : ℝ)⁻¹

noncomputable def rectangularCenteredKernel (X : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  fun i j => X i j - (matrixRowError X i + matrixColumnError X j) / Fintype.card ι -
    (Fintype.card ι : ℝ)⁻¹

noncomputable def rectangularMarginalVector (X : Matrix ι κ ℝ) : (ι ⊕ κ) → ℝ :=
  Sum.elim (matrixRowError X) (matrixColumnError X)

noncomputable def rectangularExpScaling (X : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) : Matrix ι κ ℝ :=
  fun i j => Real.exp (x i) * X i j * Real.exp (y j)

noncomputable def rectangularPermanent (X : Matrix ι κ ℝ) (e : ι ≃ κ) : ℝ :=
  (X.submatrix id e).permanent

omit [Fintype κ] [DecidableEq κ] in
theorem rectangularPermanent_independent (X : Matrix ι κ ℝ) (e f : ι ≃ κ) :
    rectangularPermanent X e = rectangularPermanent X f := by
  have hid : (X.submatrix id e).submatrix id (f.trans e.symm) = X.submatrix id f := by
    ext i j
    simp
  have h := Matrix.permanent_permute_rows (f.trans e.symm) (X.submatrix id e)
  rw [hid] at h
  exact h.symm

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixRowError_square_reindex (X : Matrix ι κ ℝ) (e : ι ≃ κ) (i : ι) :
    matrixRowError (X.submatrix id e) i = matrixRowError X i :=
  matrixRowError_submatrix_equiv X (Equiv.refl ι) e i

omit [DecidableEq ι] [DecidableEq κ] [Fintype κ] in
theorem matrixColumnError_square_reindex (X : Matrix ι κ ℝ) (e : ι ≃ κ) (j : ι) :
    matrixColumnError (X.submatrix id e) j = matrixColumnError X (e j) :=
  matrixColumnError_submatrix_equiv X (Equiv.refl ι) e j

omit [DecidableEq ι] [DecidableEq κ] in
theorem rectangularCenteredKernel_square_reindex (X : Matrix ι κ ℝ) (e : ι ≃ κ) :
    localCenteredKernel (X.submatrix id e) = (rectangularCenteredKernel X).submatrix id e := by
  ext i j
  simp only [localCenteredKernel, marginalBalancedMatrix, averagingMatrix, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, mul_one, rectangularCenteredKernel,
    Matrix.submatrix_apply, matrixRowError_square_reindex,
    matrixColumnError_square_reindex, id_eq]

omit [DecidableEq ι] [DecidableEq κ] [Fintype κ] in
theorem rectangularAverageMatrix_square_reindex (e : ι ≃ κ) :
    (rectangularAverageMatrix ι κ).submatrix id e = averagingMatrix ι := by
  ext i j
  simp [rectangularAverageMatrix, averagingMatrix]

omit [DecidableEq ι] [DecidableEq κ] in
theorem rectangularMarginalVector_square_reindex (X : Matrix ι κ ℝ) (e : ι ≃ κ) :
    localMarginalVector (X.submatrix id e) =
      rectangularMarginalVector X ∘ Equiv.sumCongr (Equiv.refl ι) e := by
  ext k
  rcases k with i | j
  · simp [localMarginalVector, rectangularMarginalVector, matrixRowError_square_reindex]
  · simp [localMarginalVector, rectangularMarginalVector, matrixColumnError_square_reindex]

omit [DecidableEq ι] [DecidableEq κ] in
theorem pi_norm_comp_equiv (e : ι ≃ κ) (v : κ → ℝ) : ‖v ∘ e‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2
    intro i
    exact norm_le_pi_norm v (e i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (v ∘ e))).2
    intro j
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using norm_le_pi_norm (v ∘ e) (e.symm j)

omit [DecidableEq ι] [DecidableEq κ] [Fintype ι] [Fintype κ] in
theorem rectangularExpScaling_square_reindex (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (z : (ι ⊕ ι) → ℝ) :
    (rectangularExpScaling X (fun i => z (Sum.inl i))
      (fun j => z (Sum.inr (e.symm j)))).submatrix id e = localScaledMatrix (X.submatrix id e) z := by
  ext i j
  simp only [rectangularExpScaling, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    localScaledMatrix, id_eq, Real.exp_add]
  ring

omit [DecidableEq ι] [DecidableEq κ] [Fintype ι] [Fintype κ] in
theorem rectangular_potentials_square_reindex (e : ι ≃ κ) (z : (ι ⊕ ι) → ℝ) :
    (Sum.elim (fun i => z (Sum.inl i)) (fun j => z (Sum.inr (e.symm j)))) ∘
      Equiv.sumCongr (Equiv.refl ι) e = z := by
  ext k
  rcases k with i | j <;> simp

omit [DecidableEq κ] in
theorem rectangularPermanent_exp_restoration (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (x : ι → ℝ) (y : κ → ℝ) :
    rectangularPermanent X e = Real.exp (-((∑ i, x i) + ∑ j, y j)) *
      rectangularPermanent (rectangularExpScaling X x y) e := by
  have h := permanent_exp_restoration (X.submatrix id e) x (y ∘ e)
  have hy : (∑ j, (y ∘ e) j) = ∑ j, y j := e.sum_comp y
  rw [hy] at h
  exact h

structure RectangularScalingWitness (X : Matrix ι κ ℝ) (e : ι ≃ κ) (K C q eps : ℝ)
    (x : ι → ℝ) (y : κ → ℝ) : Prop where
  infinity : ‖Sum.elim x y‖ ≤ 4 * localScalingInverseBudget C q * eps
  gauge : (∑ i, x i) = ∑ j, y j
  row_sum : ∀ i, ∑ j, rectangularExpScaling X x y i j = 1
  column_sum : ∀ j, ∑ i, rectangularExpScaling X x y i j = 1
  density : ∀ i j, |rectangularExpScaling X x y i j| ≤ 2 * K / Fintype.card ι
  gap : ‖rectangularExpScaling X x y - rectangularAverageMatrix ι κ‖ ≤ (1 + q) / 2
  euclidean : localEuclideanNorm (Sum.elim x y) ≤
    2 * localScalingInverseBudget C q * localEuclideanNorm (rectangularMarginalVector X)
  frobenius : realFrobeniusNorm (rectangularExpScaling X x y - X) ≤
    8 * K * localScalingInverseBudget C q / Real.sqrt (Fintype.card ι) *
      localEuclideanNorm (rectangularMarginalVector X)
  capacity_nonneg : 0 ≤ (∑ i, x i) + ∑ j, y j
  capacity_upper : (∑ i, x i) + ∑ j, y j ≤ 32 * localScalingInverseBudget C q ^ 2 *
    localEuclideanNorm (rectangularMarginalVector X) ^ 2
  nonnegative : ∀ i j, 0 ≤ rectangularExpScaling X x y i j
  zero_support : ∀ i j, rectangularExpScaling X x y i j = 0 ↔ X i j = 0
  permanent_restoration : rectangularPermanent X e = Real.exp (-((∑ i, x i) + ∑ j, y j)) *
    rectangularPermanent (rectangularExpScaling X x y) e

theorem localScalingWitness_to_rectangular (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (K C q eps : ℝ) (z : (ι ⊕ ι) → ℝ)
    (hz : LocalScalingWitness (X.submatrix id e) K C q eps z) :
    RectangularScalingWitness X e K C q eps
      (fun i => z (Sum.inl i)) (fun j => z (Sum.inr (e.symm j))) := by
  let x : ι → ℝ := fun i => z (Sum.inl i)
  let y : κ → ℝ := fun j => z (Sum.inr (e.symm j))
  let B := rectangularExpScaling X x y
  let A := localScaledMatrix (X.submatrix id e) z
  have hB : B.submatrix id e = A := rectangularExpScaling_square_reindex X e z
  have hpoint (i : ι) (j : κ) : B i j = A i (e.symm j) := by
    have h := congrFun (congrFun hB i) (e.symm j)
    simpa only [Matrix.submatrix_apply, id_eq, Equiv.apply_symm_apply] using h
  have hpoint' (i j : ι) : B i (e j) = A i j := congrFun (congrFun hB i) j
  have hxy : (Sum.elim x y) ∘ Equiv.sumCongr (Equiv.refl ι) e = z :=
    rectangular_potentials_square_reindex e z
  have hnorm : ‖Sum.elim x y‖ = ‖z‖ := by
    have h := pi_norm_comp_equiv (Equiv.sumCongr (Equiv.refl ι) e) (Sum.elim x y)
    rw [hxy] at h
    exact h.symm
  have heuc : localEuclideanNorm (Sum.elim x y) = localEuclideanNorm z := by
    have h := localEuclideanNorm_comp_equiv (Equiv.sumCongr (Equiv.refl ι) e) (Sum.elim x y)
    rw [hxy] at h
    exact h.symm
  have hg : localEuclideanNorm (localMarginalVector (X.submatrix id e)) =
      localEuclideanNorm (rectangularMarginalVector X) := by
    rw [rectangularMarginalVector_square_reindex, localEuclideanNorm_comp_equiv]
  have hy : (∑ j, y j) = ∑ j, z (Sum.inr j) := e.symm.sum_comp (fun j => z (Sum.inr j))
  have hgap : ‖B - rectangularAverageMatrix ι κ‖ = ‖A - averagingMatrix ι‖ := by
    have h := matrix_l2_opNorm_submatrix_equiv (B - rectangularAverageMatrix ι κ) (Equiv.refl ι) e
    have hd : (B - rectangularAverageMatrix ι κ).submatrix id e = A - averagingMatrix ι := by
      change B.submatrix id e - (rectangularAverageMatrix ι κ).submatrix id e = _
      rw [hB, rectangularAverageMatrix_square_reindex]
    change ‖(B - rectangularAverageMatrix ι κ).submatrix id e‖ = ‖B - rectangularAverageMatrix ι κ‖ at h
    rw [hd] at h
    exact h.symm
  have hfrob : realFrobeniusNorm (B - X) = realFrobeniusNorm (A - X.submatrix id e) := by
    have h := realFrobeniusNorm_submatrix_equiv (B - X) (Equiv.refl ι) e
    have hd : (B - X).submatrix id e = A - X.submatrix id e := by
      change B.submatrix id e - X.submatrix id e = _
      rw [hB]
    change realFrobeniusNorm ((B - X).submatrix id e) = realFrobeniusNorm (B - X) at h
    rw [hd] at h
    exact h.symm
  change RectangularScalingWitness X e K C q eps x y
  refine ⟨by rw [hnorm]; exact hz.infinity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rectangularPermanent_exp_restoration X e x y⟩
  · rw [hy]
    exact hz.gauge
  · intro i
    change (∑ j, B i j) = 1
    rw [← e.sum_comp (fun j => B i j)]
    simp_rw [hpoint']
    exact hz.row_sum i
  · intro j
    change (∑ i, B i j) = 1
    simp_rw [hpoint]
    exact hz.column_sum (e.symm j)
  · intro i j
    change |B i j| ≤ _
    rw [hpoint]
    exact hz.density i (e.symm j)
  · change ‖B - rectangularAverageMatrix ι κ‖ ≤ _
    rw [hgap]
    exact hz.gap
  · rw [heuc, ← hg]
    exact hz.euclidean
  · change realFrobeniusNorm (B - X) ≤ _
    rw [hfrob, ← hg]
    exact hz.frobenius
  · rw [hy]
    exact hz.capacity_nonneg
  · rw [hy, ← hg]
    exact hz.capacity_upper
  · intro i j
    change 0 ≤ B i j
    rw [hpoint]
    exact hz.nonnegative i (e.symm j)
  · intro i j
    change B i j = 0 ↔ X i j = 0
    rw [hpoint]
    simpa using hz.zero_support i (e.symm j)

theorem exists_rectangular_scaling_witness (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (hX : ∀ i j, 0 ≤ X i j)
    (hmass : matrixEntryMass X = Fintype.card ι)
    (K C q eps : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (heps : 0 ≤ eps)
    (hXentry : ∀ i j, |X i j| ≤ K / Fintype.card ι)
    (hentry : ∀ i j, |rectangularCenteredKernel X i j| ≤ C / Fintype.card ι)
    (hEq : ‖rectangularCenteredKernel X‖ ≤ q)
    (ha : ∀ i, |matrixRowError X i| ≤ eps) (hb : ∀ j, |matrixColumnError X j| ≤ eps)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (hsmall : eps ≤ 1 / (256 * localScalingInverseBudget C q ^ 2))
    (hgap : eps ≤ (1 - q) / (2 * (32 * localScalingInverseBudget C q + 2))) :
    ∃ x : ι → ℝ, ∃ y : κ → ℝ, RectangularScalingWitness X e K C q eps x y := by
  have hm : matrixEntryMass (X.submatrix id e) = Fintype.card ι := by
    have h := matrixEntryMass_submatrix_equiv X (Equiv.refl ι) e
    change matrixEntryMass (X.submatrix id e) = matrixEntryMass X at h
    rwa [hmass] at h
  have he : ‖localCenteredKernel (X.submatrix id e)‖ ≤ q := by
    rw [rectangularCenteredKernel_square_reindex]
    have h := matrix_l2_opNorm_submatrix_equiv (rectangularCenteredKernel X) (Equiv.refl ι) e
    change ‖(rectangularCenteredKernel X).submatrix id e‖ = ‖rectangularCenteredKernel X‖ at h
    rwa [h]
  obtain ⟨z, hz⟩ := exists_local_scaling_witness (X.submatrix id e) hp
    (fun i j => hX i (e j)) hm K C q eps hK hC hq0 hq1 heps
    (fun i j => hXentry i (e j))
    (by intro i j; rw [rectangularCenteredKernel_square_reindex]; exact hentry i (e j))
    he (by intro i; rw [matrixRowError_square_reindex]; exact ha i)
    (by intro j; rw [matrixColumnError_square_reindex]; exact hb (e j))
    (by
      intro i
      have h := matrix_absolute_row_sum_submatrix_equiv X (Equiv.refl ι) e i
      change (∑ j, |X.submatrix id e i j|) = ∑ j, |X i j| at h
      rw [h]
      exact hrow i)
    (by intro j; exact hcol (e j)) hsmall hgap
  exact ⟨(fun i => z (Sum.inl i)), (fun j => z (Sum.inr (e.symm j))),
    localScalingWitness_to_rectangular X e K C q eps z hz⟩

end TournamentHamiltonian
