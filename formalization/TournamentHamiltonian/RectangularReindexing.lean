import TournamentHamiltonian.LocalScalingComplete
import TournamentHamiltonian.ScalingKernelBridge

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ']

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ'] in
theorem localEuclideanNorm_comp_equiv (e : ι ≃ κ) (v : κ → ℝ) :
    localEuclideanNorm (v ∘ e) = localEuclideanNorm v := by
  have h : localEuclideanNorm (v ∘ e) ^ 2 = localEuclideanNorm v ^ 2 := by
    rw [localEuclideanNorm_sq, localEuclideanNorm_sq]
    exact e.sum_comp (fun i => v i ^ 2)
  nlinarith [localEuclideanNorm_nonneg (v ∘ e), localEuclideanNorm_nonneg v]

omit [DecidableEq ι] [DecidableEq ι'] in
theorem matrix_l2_opNorm_submatrix_equiv_le (X : Matrix ι κ ℝ) (er : ι' ≃ ι) (ec : κ' ≃ κ) :
    ‖X.submatrix er ec‖ ≤ ‖X‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg X)
  intro z
  change localEuclideanNorm ((X.submatrix er ec) *ᵥ (fun i => z i)) ≤ ‖X‖ * localEuclideanNorm (fun i => z i)
  rw [Matrix.submatrix_mulVec_equiv, localEuclideanNorm_comp_equiv]
  have h := Matrix.l2_opNorm_mulVec X (WithLp.toLp 2 ((fun i => z i) ∘ ec.symm))
  change localEuclideanNorm (X *ᵥ ((fun i => z i) ∘ ec.symm)) ≤
    ‖X‖ * localEuclideanNorm ((fun i => z i) ∘ ec.symm) at h
  rwa [localEuclideanNorm_comp_equiv] at h

omit [DecidableEq ι] [DecidableEq ι'] in
theorem matrix_l2_opNorm_submatrix_equiv (X : Matrix ι κ ℝ) (er : ι' ≃ ι) (ec : κ' ≃ κ) :
    ‖X.submatrix er ec‖ = ‖X‖ := by
  apply le_antisymm (matrix_l2_opNorm_submatrix_equiv_le X er ec)
  have h := matrix_l2_opNorm_submatrix_equiv_le (X.submatrix er ec) er.symm ec.symm
  have hid : (X.submatrix er ec).submatrix er.symm ec.symm = X := by
    ext i j
    simp
  rwa [hid] at h

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ'] in
theorem realFrobeniusNorm_submatrix_equiv (X : Matrix ι κ ℝ) (er : ι' ≃ ι) (ec : κ' ≃ κ) :
    realFrobeniusNorm (X.submatrix er ec) = realFrobeniusNorm X := by
  unfold realFrobeniusNorm
  simp only [Matrix.submatrix_apply]
  have hsum (i : ι) : (∑ j : κ', X i (ec j) ^ 2) = ∑ j : κ, X i j ^ 2 :=
    ec.sum_comp (fun j : κ => (X i j : ℝ) ^ 2)
  simp_rw [hsum]
  rw [er.sum_comp (fun i => ∑ j, X i j ^ 2)]

omit [DecidableEq ι] [DecidableEq ι'] in
theorem gramGaussian_submatrix_equiv (X : Matrix ι κ ℝ) (er : ι' ≃ ι) (ec : κ' ≃ κ) :
    gramGaussian (X.submatrix er ec) = gramGaussian X := by
  have hgram : (X.submatrix er ec).transpose * X.submatrix er ec =
      (X.transpose * X).submatrix ec ec := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
  have hmat : (1 : Matrix κ' κ' ℝ) - (X.submatrix er ec).transpose * X.submatrix er ec =
      ((1 : Matrix κ κ ℝ) - X.transpose * X).submatrix ec ec := by
    rw [hgram]
    change 1 - (X.transpose * X).submatrix ec ec =
      (1 : Matrix κ κ ℝ).submatrix ec ec - (X.transpose * X).submatrix ec ec
    rw [Matrix.submatrix_one_equiv]
  unfold gramGaussian
  rw [hmat, Matrix.det_submatrix_equiv_self]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ'] in
theorem matrixEntryMass_submatrix_equiv (X : Matrix ι κ ℝ) (er : ι' ≃ ι) (ec : κ' ≃ κ) :
    matrixEntryMass (X.submatrix er ec) = matrixEntryMass X := by
  unfold matrixEntryMass
  simp only [Matrix.submatrix_apply]
  have hsum (i : ι) : (∑ j : κ', X i (ec j)) = ∑ j : κ, X i j := ec.sum_comp (fun j : κ => X i j)
  simp_rw [hsum]
  exact er.sum_comp (fun i => ∑ j, X i j)

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ'] [Fintype ι] [Fintype ι'] in
theorem matrixRowError_submatrix_equiv (X : Matrix ι κ ℝ) (er : ι' ≃ ι) (ec : κ' ≃ κ) (i : ι') :
    matrixRowError (X.submatrix er ec) i = matrixRowError X (er i) := by
  unfold matrixRowError
  simp only [Matrix.submatrix_apply]
  rw [ec.sum_comp (fun j => X (er i) j)]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ'] [Fintype κ] [Fintype κ'] in
theorem matrixColumnError_submatrix_equiv (X : Matrix ι κ ℝ) (er : ι' ≃ ι) (ec : κ' ≃ κ) (j : κ') :
    matrixColumnError (X.submatrix er ec) j = matrixColumnError X (ec j) := by
  unfold matrixColumnError
  simp only [Matrix.submatrix_apply]
  rw [er.sum_comp (fun i => X i (ec j))]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ'] [Fintype ι] [Fintype ι'] in
theorem matrix_absolute_row_sum_submatrix_equiv (X : Matrix ι κ ℝ) (er : ι' ≃ ι) (ec : κ' ≃ κ) (i : ι') :
    (∑ j, |X.submatrix er ec i j|) = ∑ j, |X (er i) j| :=
  ec.sum_comp (fun j => |X (er i) j|)

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ'] [Fintype κ] [Fintype κ'] in
theorem matrix_absolute_column_sum_submatrix_equiv (X : Matrix ι κ ℝ) (er : ι' ≃ ι) (ec : κ' ≃ κ) (j : κ') :
    (∑ i, |X.submatrix er ec i j|) = ∑ i, |X i (ec j)| :=
  er.sum_comp (fun i => |X i (ec j)|)

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ'] in
theorem massNormalizedMatrix_submatrix_equiv (X : Matrix ι κ ℝ) (er : ι' ≃ ι) (ec : κ' ≃ κ) :
    massNormalizedMatrix (X.submatrix er ec) = (massNormalizedMatrix X).submatrix er ec := by
  ext i j
  simp only [massNormalizedMatrix, matrixEntryMass_submatrix_equiv, Fintype.card_congr er,
    Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply]

end TournamentHamiltonian
