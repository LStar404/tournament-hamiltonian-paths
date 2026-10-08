import TournamentHamiltonian.GramLipschitz
import TournamentHamiltonian.DeletionMass
import Mathlib.Data.Matrix.Block

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def averagingMatrix (ι : Type*) [Fintype ι] : Matrix ι ι ℝ :=
  (Fintype.card ι : ℝ)⁻¹ • Matrix.of (fun _ _ => 1)

noncomputable def marginalBalancedMatrix (X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => X i j - (matrixRowError X i + matrixColumnError X j) / Fintype.card ι

noncomputable def localCenteredKernel (X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  marginalBalancedMatrix X - averagingMatrix ι

def DoublyCentered (E : Matrix ι ι ℝ) : Prop :=
  (∀ i, ∑ j, E i j = 0) ∧ (∀ j, ∑ i, E i j = 0)

omit [DecidableEq ι] in
theorem marginalBalancedMatrix_row_sum (X : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (hmass : matrixEntryMass X = Fintype.card ι) (i : ι) :
    (∑ j, marginalBalancedMatrix X i j) = 1 := by
  have hpR : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hbeta : ∑ j, matrixColumnError X j = 0 := by
    rw [matrixColumnError_sum, hmass, sub_self]
  simp only [marginalBalancedMatrix, Finset.sum_sub_distrib, ← Finset.sum_div,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hbeta, add_zero]
  rw [matrixRowError]
  field_simp [hpR]
  ring

omit [DecidableEq ι] in
theorem marginalBalancedMatrix_column_sum (X : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (hmass : matrixEntryMass X = Fintype.card ι) (j : ι) :
    (∑ i, marginalBalancedMatrix X i j) = 1 := by
  have hpR : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have halpha : ∑ i, matrixRowError X i = 0 := by
    rw [matrixRowError_sum, hmass, sub_self]
  simp only [marginalBalancedMatrix, Finset.sum_sub_distrib, ← Finset.sum_div,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, halpha, zero_add]
  rw [matrixColumnError]
  field_simp [hpR]
  ring

omit [DecidableEq ι] in
theorem averagingMatrix_row_sum (hp : 0 < Fintype.card ι) (i : ι) :
    (∑ j, averagingMatrix ι i j) = 1 := by
  have hpR : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp [averagingMatrix, mul_inv_cancel₀ hpR]

omit [DecidableEq ι] in
theorem averagingMatrix_column_sum (hp : 0 < Fintype.card ι) (j : ι) :
    (∑ i, averagingMatrix ι i j) = 1 := by
  have hpR : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp [averagingMatrix, mul_inv_cancel₀ hpR]

omit [DecidableEq ι] in
theorem localCenteredKernel_doublyCentered (X : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (hmass : matrixEntryMass X = Fintype.card ι) :
    DoublyCentered (localCenteredKernel X) := by
  constructor
  · intro i
    simp only [localCenteredKernel, Matrix.sub_apply, Finset.sum_sub_distrib,
      marginalBalancedMatrix_row_sum X hp hmass, averagingMatrix_row_sum hp, sub_self]
  · intro j
    simp only [localCenteredKernel, Matrix.sub_apply, Finset.sum_sub_distrib,
      marginalBalancedMatrix_column_sum X hp hmass, averagingMatrix_column_sum hp, sub_self]

omit [DecidableEq ι] in
theorem averagingMatrix_transpose : (averagingMatrix ι).transpose = averagingMatrix ι := by
  ext i j
  rfl

omit [DecidableEq ι] in
theorem averagingMatrix_idempotent (hp : 0 < Fintype.card ι) :
    averagingMatrix ι * averagingMatrix ι = averagingMatrix ι := by
  ext i j
  have hpR : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp [averagingMatrix, Matrix.mul_apply, hpR]

omit [DecidableEq ι] in
theorem DoublyCentered.transpose {E : Matrix ι ι ℝ} (hE : DoublyCentered E) :
    DoublyCentered E.transpose := ⟨hE.2, hE.1⟩

omit [DecidableEq ι] in
theorem DoublyCentered.mul_averaging {E : Matrix ι ι ℝ} (hE : DoublyCentered E) :
    E * averagingMatrix ι = 0 := by
  ext i j
  simp only [Matrix.mul_apply, averagingMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, mul_one, ← Finset.sum_mul, hE.1, zero_mul, Matrix.zero_apply]

omit [DecidableEq ι] in
theorem DoublyCentered.averaging_mul {E : Matrix ι ι ℝ} (hE : DoublyCentered E) :
    averagingMatrix ι * E = 0 := by
  ext i j
  simp only [Matrix.mul_apply, averagingMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, mul_one, ← Finset.mul_sum, hE.2, mul_zero, Matrix.zero_apply]

noncomputable def localGramLeft (E : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (1 - E * E.transpose)⁻¹

noncomputable def localGramRight (E : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (1 - E.transpose * E)⁻¹

noncomputable def localBalancedHessian (E : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 1 (averagingMatrix ι + E) (averagingMatrix ι + E.transpose) 1

noncomputable def localGaugeCorrection (ι : Type*) [Fintype ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks ((1 / 2 : ℝ) • averagingMatrix ι) ((-1 / 2 : ℝ) • averagingMatrix ι)
    ((-1 / 2 : ℝ) • averagingMatrix ι) ((1 / 2 : ℝ) • averagingMatrix ι)

noncomputable def localBalancedInverse (E : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks (localGramLeft E - (1 / 4 : ℝ) • averagingMatrix ι)
    (-(E * localGramRight E) - (1 / 4 : ℝ) • averagingMatrix ι)
    (-(E * localGramRight E).transpose - (1 / 4 : ℝ) • averagingMatrix ι)
    (localGramRight E - (1 / 4 : ℝ) • averagingMatrix ι)

theorem localGramRight_gram_posDef (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    (1 - E.transpose * E).PosDef := gram_complement_posDef E q hq0 hq1 hEq

theorem localGramLeft_gram_posDef (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    (1 - E * E.transpose).PosDef := by
  have ht : ‖E.transpose‖ ≤ q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.l2_opNorm_conjTranspose E).le.trans hEq
  simpa only [Matrix.transpose_transpose] using gram_complement_posDef E.transpose q hq0 hq1 ht

theorem localGramRight_mul_gram (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    localGramRight E * (1 - E.transpose * E) = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
    (localGramRight_gram_posDef E q hq0 hq1 hEq).det_pos.ne')

theorem gram_mul_localGramRight (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    (1 - E.transpose * E) * localGramRight E = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
    (localGramRight_gram_posDef E q hq0 hq1 hEq).det_pos.ne')

theorem localGramLeft_mul_gram (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    localGramLeft E * (1 - E * E.transpose) = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
    (localGramLeft_gram_posDef E q hq0 hq1 hEq).det_pos.ne')

theorem gram_mul_localGramLeft (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    (1 - E * E.transpose) * localGramLeft E = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
    (localGramLeft_gram_posDef E q hq0 hq1 hEq).det_pos.ne')

theorem localGramRight_transpose (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    (localGramRight E).transpose = localGramRight E := by
  simpa only [localGramRight, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (localGramRight_gram_posDef E q hq0 hq1 hEq).inv.isHermitian.eq

theorem localGramLeft_transpose (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    (localGramLeft E).transpose = localGramLeft E := by
  simpa only [localGramLeft, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (localGramLeft_gram_posDef E q hq0 hq1 hEq).inv.isHermitian.eq

theorem localGramLeft_mul_E (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    localGramLeft E * E = E * localGramRight E := by
  have hl := localGramLeft_mul_gram E q hq0 hq1 hEq
  have hr := gram_mul_localGramRight E q hq0 hq1 hEq
  have hi : (1 - E * E.transpose) * E = E * (1 - E.transpose * E) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  calc
    _ = localGramLeft E * E * ((1 - E.transpose * E) * localGramRight E) := by rw [hr, Matrix.mul_one]
    _ = localGramLeft E * ((1 - E * E.transpose) * E) * localGramRight E := by
      rw [hi]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [← Matrix.mul_assoc, hl, Matrix.one_mul]

theorem localGramLeft_sub_one (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    localGramLeft E - 1 = E * localGramRight E * E.transpose := by
  have hl := localGramLeft_mul_gram E q hq0 hq1 hEq
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, localGramLeft_mul_E E q hq0 hq1 hEq] at hl
  rw [← hl]
  abel

theorem localGramRight_sub_one (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    localGramRight E - 1 = E.transpose * localGramLeft E * E := by
  have ht : ‖E.transpose‖ ≤ q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.l2_opNorm_conjTranspose E).le.trans hEq
  simpa only [localGramLeft, localGramRight, Matrix.transpose_transpose] using
    localGramLeft_sub_one E.transpose q hq0 hq1 ht

theorem localGramRight_mul_averaging (E : Matrix ι ι ℝ) (hE : DoublyCentered E)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    localGramRight E * averagingMatrix ι = averagingMatrix ι := by
  have ha : (1 - E.transpose * E) * averagingMatrix ι = averagingMatrix ι := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hE.mul_averaging, Matrix.mul_zero, sub_zero]
  calc
    _ = localGramRight E * ((1 - E.transpose * E) * averagingMatrix ι) := by rw [ha]
    _ = _ := by rw [← Matrix.mul_assoc, localGramRight_mul_gram E q hq0 hq1 hEq, Matrix.one_mul]

theorem localGramLeft_mul_averaging (E : Matrix ι ι ℝ) (hE : DoublyCentered E)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    localGramLeft E * averagingMatrix ι = averagingMatrix ι := by
  have ht : ‖E.transpose‖ ≤ q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.l2_opNorm_conjTranspose E).le.trans hEq
  simpa only [localGramLeft, localGramRight, Matrix.transpose_transpose] using
    localGramRight_mul_averaging E.transpose hE.transpose q hq0 hq1 ht

theorem localGramRight_opNorm_le (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    ‖localGramRight E‖ ≤ (1 - q ^ 2)⁻¹ := by
  apply inverse_opNorm_le_of_quadratic_lower _ (localGramRight_gram_posDef E q hq0 hq1 hEq)
    _ (by nlinarith)
  exact gram_complement_quadratic_lower E q hq0 hEq

theorem localGramLeft_opNorm_le (E : Matrix ι ι ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    ‖localGramLeft E‖ ≤ (1 - q ^ 2)⁻¹ := by
  have ht : ‖E.transpose‖ ≤ q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.l2_opNorm_conjTranspose E).le.trans hEq
  simpa only [localGramLeft, localGramRight, Matrix.transpose_transpose] using
    localGramRight_opNorm_le E.transpose q hq0 hq1 ht

theorem localBalancedHessian_add_gauge (E : Matrix ι ι ℝ) :
    localBalancedHessian E + localGaugeCorrection ι =
      Matrix.fromBlocks (1 + (1 / 2 : ℝ) • averagingMatrix ι)
        (E + (1 / 2 : ℝ) • averagingMatrix ι)
        (E.transpose + (1 / 2 : ℝ) • averagingMatrix ι)
        (1 + (1 / 2 : ℝ) • averagingMatrix ι) := by
  unfold localBalancedHessian localGaugeCorrection
  rw [Matrix.fromBlocks_add]
  congr 1 <;> module

theorem localBalancedInverse_mul_hessian (E : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (hE : DoublyCentered E)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    localBalancedInverse E * (localBalancedHessian E + localGaugeCorrection ι) = 1 := by
  have hRR := localGramRight_transpose E q hq0 hq1 hEq
  have hRP := localGramRight_mul_averaging E hE q hq0 hq1 hEq
  have hLP := localGramLeft_mul_averaging E hE q hq0 hq1 hEq
  have hRLE := localGramLeft_mul_E E q hq0 hq1 hEq
  have hOET : E * (localGramRight E * E.transpose) = localGramLeft E - 1 := by
    simpa only [Matrix.mul_assoc] using (localGramLeft_sub_one E q hq0 hq1 hEq).symm
  have hRETE : localGramRight E * (E.transpose * E) = localGramRight E - 1 := by
    have h := localGramRight_mul_gram E q hq0 hq1 hEq
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    rw [← h]
    abel
  have hPP := averagingMatrix_idempotent (ι := ι) hp
  rw [localBalancedHessian_add_gauge]
  unfold localBalancedInverse
  simp only [Matrix.transpose_mul, hRR]
  rw [Matrix.fromBlocks_multiply]
  rw [← Matrix.fromBlocks_one (l := ι) (m := ι)]
  congr 1 <;>
    simp only [Matrix.mul_add, Matrix.sub_mul,
      Matrix.neg_mul, Matrix.mul_one,
      smul_mul_assoc, Matrix.mul_smul, Matrix.mul_assoc,
      hE.mul_averaging, hE.averaging_mul, hE.transpose.mul_averaging,
      hE.transpose.averaging_mul, hRP, hLP, hPP, hRLE, hOET, hRETE,
      Matrix.mul_zero, smul_zero]
    <;> module

theorem localBalancedHessian_inverse (E : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (hE : DoublyCentered E)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    (localBalancedHessian E + localGaugeCorrection ι)⁻¹ = localBalancedInverse E :=
  Matrix.inv_eq_left_inv (localBalancedInverse_mul_hessian E hp hE q hq0 hq1 hEq)

theorem local_sandwich_entry_le (U A V : Matrix ι ι ℝ) (i j : ι) :
    |(U * A * V.transpose) i j| ≤
      Real.sqrt (∑ k, U i k ^ 2) * Real.sqrt (∑ k, V j k ^ 2) * ‖A‖ := by
  let u : EuclideanSpace ℝ ι := WithLp.toLp 2 (U i)
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (V j)
  have hu : ‖u‖ = Real.sqrt (∑ k, U i k ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg u), EuclideanSpace.norm_sq_eq]
    simp [u, Real.norm_eq_abs, sq_abs]
  have hv : ‖v‖ = Real.sqrt (∑ k, V j k ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg v), EuclideanSpace.norm_sq_eq]
    simp [v, Real.norm_eq_abs, sq_abs]
  have he : inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) = (U * A * V.transpose) i j := by
    rw [Matrix.inner_toEuclideanCLM, Matrix.mul_assoc]
    simp [u, v, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct]
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖ ≤ ‖A‖ * ‖v‖ := by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
      ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) A) v
  rw [← he, ← hu, ← hv]
  calc
    _ ≤ ‖u‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖A‖ * ‖v‖) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg u)
    _ = _ := by ring

omit [DecidableEq ι] in
theorem dense_row_euclidean_bound (E : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (C : ℝ) (hC : 0 ≤ C)
    (hentry : ∀ i j, |E i j| ≤ C / Fintype.card ι) (i : ι) :
    Real.sqrt (∑ j, E i j ^ 2) ≤ C / Real.sqrt (Fintype.card ι : ℝ) := by
  have hpR : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hp
  have hs : (∑ j, E i j ^ 2) ≤ C ^ 2 / Fintype.card ι := by
    calc
      _ ≤ ∑ _j : ι, (C / Fintype.card ι) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have h := pow_le_pow_left₀ (abs_nonneg (E i j)) (hentry i j) 2
        simpa only [sq_abs] using h
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [hpR.ne']
  have h := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_div (sq_nonneg C), Real.sqrt_sq hC] at h
  exact h

theorem dense_sandwich_entry_bound (U A V : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (C K : ℝ) (hC : 0 ≤ C) (_hK : 0 ≤ K)
    (hU : ∀ i j, |U i j| ≤ C / Fintype.card ι)
    (hV : ∀ i j, |V i j| ≤ C / Fintype.card ι) (hA : ‖A‖ ≤ K) (i j : ι) :
    |(U * A * V.transpose) i j| ≤ C ^ 2 * K / Fintype.card ι := by
  have hu := dense_row_euclidean_bound U hp C hC hU i
  have hv := dense_row_euclidean_bound V hp C hC hV j
  have hprod := mul_le_mul hu hv (Real.sqrt_nonneg _) (div_nonneg hC (Real.sqrt_nonneg _))
  have h := (local_sandwich_entry_le U A V i j).trans
    (mul_le_mul hprod hA (norm_nonneg _) (mul_nonneg
      (div_nonneg hC (Real.sqrt_nonneg _)) (div_nonneg hC (Real.sqrt_nonneg _))))
  have he : (C / Real.sqrt (Fintype.card ι : ℝ)) *
      (C / Real.sqrt (Fintype.card ι : ℝ)) * K = C ^ 2 * K / Fintype.card ι := by
    rw [← pow_two, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  rw [he] at h
  exact h

theorem localGramLeft_entry_bound (E : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (C q : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hentry : ∀ i j, |E i j| ≤ C / Fintype.card ι) (hEq : ‖E‖ ≤ q) (i j : ι) :
    |(localGramLeft E - 1) i j| ≤ C ^ 2 / (Fintype.card ι * (1 - q ^ 2)) := by
  rw [localGramLeft_sub_one E q hq0 hq1 hEq]
  have hg : 0 ≤ (1 - q ^ 2)⁻¹ := by apply inv_nonneg.mpr; nlinarith
  have h := dense_sandwich_entry_bound E (localGramRight E) E hp C (1 - q ^ 2)⁻¹
    hC hg hentry hentry (localGramRight_opNorm_le E q hq0 hq1 hEq) i j
  convert h using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem localGramRight_entry_bound (E : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (C q : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hentry : ∀ i j, |E i j| ≤ C / Fintype.card ι) (hEq : ‖E‖ ≤ q) (i j : ι) :
    |(localGramRight E - 1) i j| ≤ C ^ 2 / (Fintype.card ι * (1 - q ^ 2)) := by
  have ht : ‖E.transpose‖ ≤ q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.l2_opNorm_conjTranspose E).le.trans hEq
  simpa only [localGramLeft, localGramRight, Matrix.transpose_transpose] using
    localGramLeft_entry_bound E.transpose hp C q hC hq0 hq1 (fun i j => hentry j i) ht i j

theorem localOffDiagonal_entry_bound (E : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (C q : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hentry : ∀ i j, |E i j| ≤ C / Fintype.card ι) (hEq : ‖E‖ ≤ q) (i j : ι) :
    |(E * localGramRight E) i j| ≤ C / Fintype.card ι +
      C ^ 2 * q / (Fintype.card ι * (1 - q ^ 2)) := by
  have ht : ‖E.transpose‖ ≤ q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.l2_opNorm_conjTranspose E).le.trans hEq
  have hn : ‖localGramRight E * E.transpose‖ ≤ q / (1 - q ^ 2) := by
    have hg : 0 ≤ (1 - q ^ 2)⁻¹ := by apply inv_nonneg.mpr; nlinarith
    have h := (norm_mul_le _ _).trans (mul_le_mul
      (localGramRight_opNorm_le E q hq0 hq1 hEq) ht (norm_nonneg _) hg)
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hg : 0 ≤ q / (1 - q ^ 2) := div_nonneg hq0 (by nlinarith)
  have hb := dense_sandwich_entry_bound E (localGramRight E * E.transpose) E.transpose
    hp C (q / (1 - q ^ 2)) hC hg hentry (fun i j => hentry j i) hn i j
  have he : E * localGramRight E = E + E * (localGramRight E * E.transpose) * E := by
    rw [← localGramLeft_mul_E E q hq0 hq1 hEq]
    have h := localGramLeft_sub_one E q hq0 hq1 hEq
    rw [← Matrix.mul_assoc, ← h, Matrix.sub_mul, Matrix.one_mul]
    abel
  rw [he, Matrix.add_apply]
  apply (abs_add_le _ _).trans
  have hb' : |(E * (localGramRight E * E.transpose) * E) i j| ≤
      C ^ 2 * q / (Fintype.card ι * (1 - q ^ 2)) := by
    simpa only [Matrix.transpose_transpose, div_div, mul_div_assoc, mul_comm (1 - q ^ 2)] using hb
  exact add_le_add (hentry i j) hb'

theorem diagonal_block_absolute_row_bound (R : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (d : ℝ)
    (hR : ∀ i j, |(R - 1) i j| ≤ d / Fintype.card ι) (i : ι) :
    (∑ j, |(R - (1 / 4 : ℝ) • averagingMatrix ι) i j|) ≤ 1 + d + 1 / 4 := by
  have hpR : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hp
  have ha (j : ι) : |(1 / 4 : ℝ) * averagingMatrix ι i j| = (1 / 4 : ℝ) / Fintype.card ι := by
    simp [averagingMatrix, abs_mul, abs_of_pos hpR, div_eq_mul_inv]
  have hpoint (j : ι) : |(R - (1 / 4 : ℝ) • averagingMatrix ι) i j| ≤
      |(1 : Matrix ι ι ℝ) i j| + d / Fintype.card ι + (1 / 4 : ℝ) / Fintype.card ι := by
    have he : (R - (1 / 4 : ℝ) • averagingMatrix ι) i j =
        (1 : Matrix ι ι ℝ) i j + (R - 1) i j - (1 / 4 : ℝ) * averagingMatrix ι i j := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [he]
    have hab : |(1 : Matrix ι ι ℝ) i j + (R - 1) i j -
        (1 / 4 : ℝ) * averagingMatrix ι i j| ≤
        |(1 : Matrix ι ι ℝ) i j + (R - 1) i j| + |(1 / 4 : ℝ) * averagingMatrix ι i j| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        ((1 : Matrix ι ι ℝ) i j + (R - 1) i j) ((1 / 4 : ℝ) * averagingMatrix ι i j)
    have h := hab.trans (add_le_add (abs_add_le _ _) le_rfl)
    exact h.trans (by rw [ha]; linarith [hR i j])
  calc
    _ ≤ ∑ j, (|(1 : Matrix ι ι ℝ) i j| + d / Fintype.card ι +
        (1 / 4 : ℝ) / Fintype.card ι) := Finset.sum_le_sum (fun j _ => hpoint j)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp [Matrix.one_apply, apply_ite, mul_div_cancel₀ _ hpR.ne']

omit [DecidableEq ι] in
theorem offdiagonal_block_absolute_row_bound (O : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (d : ℝ)
    (hO : ∀ i j, |O i j| ≤ d / Fintype.card ι) (i : ι) :
    (∑ j, |(-O - (1 / 4 : ℝ) • averagingMatrix ι) i j|) ≤ d + 1 / 4 := by
  have hpR : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hp
  have ha (j : ι) : |(1 / 4 : ℝ) * averagingMatrix ι i j| = (1 / 4 : ℝ) / Fintype.card ι := by
    simp [averagingMatrix, abs_mul, abs_of_pos hpR, div_eq_mul_inv]
  have hpoint (j : ι) : |(-O - (1 / 4 : ℝ) • averagingMatrix ι) i j| ≤
      d / Fintype.card ι + (1 / 4 : ℝ) / Fintype.card ι := by
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    have h : |-O i j - (1 / 4 : ℝ) * averagingMatrix ι i j| ≤
        |-O i j| + |(1 / 4 : ℝ) * averagingMatrix ι i j| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (-O i j) ((1 / 4 : ℝ) * averagingMatrix ι i j)
    rw [abs_neg, ha] at h
    exact h.trans (add_le_add (hO i j) le_rfl)
  calc
    _ ≤ ∑ j : ι, (d / Fintype.card ι + (1 / 4 : ℝ) / Fintype.card ι) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp [mul_div_cancel₀ _ hpR.ne']

noncomputable def localScalingInverseBudget (C q : ℝ) : ℝ :=
  3 / 2 + C + C ^ 2 / (1 - q)

theorem localBalancedInverse_absolute_row_bound (E : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (C q : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hentry : ∀ i j, |E i j| ≤ C / Fintype.card ι) (hEq : ‖E‖ ≤ q) (i : ι ⊕ ι) :
    (∑ j, |localBalancedInverse E i j|) ≤ localScalingInverseBudget C q := by
  have hg : 1 - q ^ 2 ≠ 0 := by nlinarith
  have hm : 1 - q ≠ 0 := by linarith
  have hdL := diagonal_block_absolute_row_bound (localGramLeft E) hp (C ^ 2 / (1 - q ^ 2))
    (fun i j => by
      simpa only [div_div, mul_comm (1 - q ^ 2)] using localGramLeft_entry_bound E hp C q hC hq0 hq1 hentry hEq i j)
  have hdR := diagonal_block_absolute_row_bound (localGramRight E) hp (C ^ 2 / (1 - q ^ 2))
    (fun i j => by
      simpa only [div_div, mul_comm (1 - q ^ 2)] using localGramRight_entry_bound E hp C q hC hq0 hq1 hentry hEq i j)
  have hO : ∀ i j, |(E * localGramRight E) i j| ≤
      (C + C ^ 2 * q / (1 - q ^ 2)) / Fintype.card ι := by
    intro i j
    have h := localOffDiagonal_entry_bound E hp C q hC hq0 hq1 hentry hEq i j
    convert h using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hoL := offdiagonal_block_absolute_row_bound (E * localGramRight E) hp
    (C + C ^ 2 * q / (1 - q ^ 2)) hO
  have hoR := offdiagonal_block_absolute_row_bound (E * localGramRight E).transpose hp
    (C + C ^ 2 * q / (1 - q ^ 2)) (fun i j => hO j i)
  have he : (1 + C ^ 2 / (1 - q ^ 2) + 1 / 4) +
      (C + C ^ 2 * q / (1 - q ^ 2) + 1 / 4) = localScalingInverseBudget C q := by
    unfold localScalingInverseBudget
    field_simp [hg, hm]; ring
  rcases i with i | i
  · simp only [Fintype.sum_sum_type]
    change (∑ j, |(localGramLeft E - (1 / 4 : ℝ) • averagingMatrix ι) i j|) +
      (∑ j, |(-(E * localGramRight E) - (1 / 4 : ℝ) • averagingMatrix ι) i j|) ≤ _
    rw [← he]
    exact add_le_add (hdL i) (hoL i)
  · simp only [Fintype.sum_sum_type]
    change (∑ j, |(-(E * localGramRight E).transpose - (1 / 4 : ℝ) • averagingMatrix ι) i j|) +
      (∑ j, |(localGramRight E - (1 / 4 : ℝ) • averagingMatrix ι) i j|) ≤ _
    rw [← he]
    exact (add_le_add (hoR i) (hdR i)).trans_eq (add_comm _ _)

theorem localBalancedInverse_transpose (E : Matrix ι ι ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hEq : ‖E‖ ≤ q) :
    (localBalancedInverse E).transpose = localBalancedInverse E := by
  unfold localBalancedInverse
  rw [Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_neg,
    averagingMatrix_transpose, Matrix.transpose_transpose,
    localGramLeft_transpose E q hq0 hq1 hEq, localGramRight_transpose E q hq0 hq1 hEq]

theorem localBalancedInverse_absolute_column_bound (E : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (C q : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hentry : ∀ i j, |E i j| ≤ C / Fintype.card ι) (hEq : ‖E‖ ≤ q) (j : ι ⊕ ι) :
    (∑ i, |localBalancedInverse E i j|) ≤ localScalingInverseBudget C q := by
  have h := localBalancedInverse_absolute_row_bound E hp C q hC hq0 hq1 hentry hEq j
  have hs (i : ι ⊕ ι) : localBalancedInverse E i j = localBalancedInverse E j i := by
    exact congrFun (congrFun (localBalancedInverse_transpose E q hq0 hq1 hEq) j) i
  simpa only [hs] using h

theorem localScalingInverseBudget_nonneg (C q : ℝ) (hC : 0 ≤ C) (hq1 : q < 1) :
    0 ≤ localScalingInverseBudget C q := by
  unfold localScalingInverseBudget
  have h : 0 ≤ C ^ 2 / (1 - q) := div_nonneg (sq_nonneg _) (by linarith)
  linarith

section MatrixNormBounds

variable {ρ σ : Type*} [Fintype ρ] [Fintype σ]

theorem absolute_row_bound_mulVec (A : Matrix ρ σ ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hrow : ∀ i, ∑ j, |A i j| ≤ L) (z : σ → ℝ) :
    ‖A *ᵥ z‖ ≤ L * ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL (norm_nonneg _))).mpr
  intro i
  calc
    _ ≤ ∑ j, ‖A i j * z j‖ := norm_sum_le _ _
    _ ≤ ∑ j, |A i j| * ‖z‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z j) (abs_nonneg _)
    _ = (∑ j, |A i j|) * ‖z‖ := (Finset.sum_mul ..).symm
    _ ≤ L * ‖z‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)

theorem absolute_row_column_bound_mulVec_sq (A : Matrix ρ σ ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hrow : ∀ i, ∑ j, |A i j| ≤ L) (hcol : ∀ j, ∑ i, |A i j| ≤ L) (z : σ → ℝ) :
    (∑ i, (A *ᵥ z) i ^ 2) ≤ L ^ 2 * ∑ j, z j ^ 2 := by
  have hpoint (i : ρ) : (A *ᵥ z) i ^ 2 ≤ L * ∑ j, |A i j| * z j ^ 2 := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun j => A i j * z j) (f := fun j => |A i j|)
      (g := fun j => |A i j| * z j ^ 2) (fun _ _ => abs_nonneg _)
      (fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) (by
        intro j _
        simp only [mul_pow, ← mul_assoc, ← pow_two, sq_abs]
        exact le_rfl)
    exact h.trans (mul_le_mul_of_nonneg_right (hrow i)
      (Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))))
  calc
    _ ≤ ∑ i, L * ∑ j, |A i j| * z j ^ 2 := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = L * ∑ j, (∑ i, |A i j|) * z j ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ L * ∑ j, L * z j ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hL
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

end MatrixNormBounds

theorem localBalancedInverse_infinity_control (E : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (C q : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hentry : ∀ i j, |E i j| ≤ C / Fintype.card ι) (hEq : ‖E‖ ≤ q) (z : (ι ⊕ ι) → ℝ) :
    ‖localBalancedInverse E *ᵥ z‖ ≤ localScalingInverseBudget C q * ‖z‖ :=
  absolute_row_bound_mulVec _ _ (localScalingInverseBudget_nonneg C q hC hq1)
    (localBalancedInverse_absolute_row_bound E hp C q hC hq0 hq1 hentry hEq) z

theorem localBalancedInverse_euclidean_control_sq (E : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (C q : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hentry : ∀ i j, |E i j| ≤ C / Fintype.card ι) (hEq : ‖E‖ ≤ q) (z : (ι ⊕ ι) → ℝ) :
    (∑ i, (localBalancedInverse E *ᵥ z) i ^ 2) ≤ localScalingInverseBudget C q ^ 2 * ∑ i, z i ^ 2 :=
  absolute_row_column_bound_mulVec_sq _ _ (localScalingInverseBudget_nonneg C q hC hq1)
    (localBalancedInverse_absolute_row_bound E hp C q hC hq0 hq1 hentry hEq)
    (localBalancedInverse_absolute_column_bound E hp C q hC hq0 hq1 hentry hEq) z

end TournamentHamiltonian
