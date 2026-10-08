import TournamentHamiltonian.LocalScalingEstimates

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def localEuclideanNorm (v : ι → ℝ) : ℝ := ‖WithLp.toLp 2 v‖

omit [DecidableEq ι] in
theorem localEuclideanNorm_nonneg (v : ι → ℝ) : 0 ≤ localEuclideanNorm v := norm_nonneg _

omit [DecidableEq ι] in
theorem localEuclideanNorm_sq (v : ι → ℝ) : localEuclideanNorm v ^ 2 = ∑ i, v i ^ 2 := by
  simp [localEuclideanNorm, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

omit [DecidableEq ι] in
theorem localEuclideanNorm_add_le (v w : ι → ℝ) :
    localEuclideanNorm (v + w) ≤ localEuclideanNorm v + localEuclideanNorm w :=
  norm_add_le (WithLp.toLp 2 v) (WithLp.toLp 2 w)

omit [DecidableEq ι] in
theorem localEuclideanNorm_neg (v : ι → ℝ) : localEuclideanNorm (-v) = localEuclideanNorm v :=
  norm_neg (WithLp.toLp 2 v)

omit [DecidableEq ι] in
theorem localEuclideanNorm_mulVec_le (A : Matrix ι ι ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hrow : ∀ i, ∑ j, |A i j| ≤ L) (hcol : ∀ j, ∑ i, |A i j| ≤ L) (v : ι → ℝ) :
    localEuclideanNorm (A *ᵥ v) ≤ L * localEuclideanNorm v := by
  apply (sq_le_sq₀ (localEuclideanNorm_nonneg _) (mul_nonneg hL (localEuclideanNorm_nonneg _))).mp
  rw [localEuclideanNorm_sq, mul_pow, localEuclideanNorm_sq]
  exact absolute_row_column_bound_mulVec_sq A L hL hrow hcol v

theorem localHessian_transpose (X : Matrix ι ι ℝ) : (localHessian X).transpose = localHessian X := by
  simp only [localHessian, Matrix.fromBlocks_transpose, Matrix.diagonal_transpose, Matrix.transpose_transpose]

theorem localBalancedHessian_transpose (E : Matrix ι ι ℝ) :
    (localBalancedHessian E).transpose = localBalancedHessian E := by
  simp only [localBalancedHessian, Matrix.fromBlocks_transpose, Matrix.transpose_one,
    Matrix.transpose_add, averagingMatrix_transpose, Matrix.transpose_transpose]

theorem localHessian_difference_column_bound (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (eps : ℝ) (heps : 0 ≤ eps) (ha : ∀ i, |matrixRowError X i| ≤ eps)
    (hb : ∀ j, |matrixColumnError X j| ≤ eps) (j : ι ⊕ ι) :
    (∑ i, |(localHessian X - localBalancedHessian (localCenteredKernel X)) i j|) ≤ 3 * eps := by
  have hs : (localHessian X - localBalancedHessian (localCenteredKernel X)).transpose =
      localHessian X - localBalancedHessian (localCenteredKernel X) := by
    rw [Matrix.transpose_sub, localHessian_transpose, localBalancedHessian_transpose]
  have hpoint (i : ι ⊕ ι) : (localHessian X - localBalancedHessian (localCenteredKernel X)) i j =
      (localHessian X - localBalancedHessian (localCenteredKernel X)) j i :=
    congrFun (congrFun hs j) i
  simpa only [hpoint] using localHessian_difference_row_bound X hp eps heps ha hb j

omit [DecidableEq ι] in
theorem weighted_marginal_remainder_sq_bound (X : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (f : ι → ι → ℝ) (x y : ι → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hf : ∀ i j, f i j ^ 2 ≤ D * (x i ^ 2 + y j ^ 2)) :
    (∑ i, (∑ j, X i j * f i j) ^ 2) ≤ 4 * D * ((∑ i, x i ^ 2) + ∑ j, y j ^ 2) := by
  have hpoint (i : ι) : (∑ j, X i j * f i j) ^ 2 ≤ 2 * D *
      ∑ j, |X i j| * (x i ^ 2 + y j ^ 2) := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun j => X i j * f i j) (f := fun j => |X i j|)
      (g := fun j => |X i j| * f i j ^ 2) (fun _ _ => abs_nonneg _)
      (fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) (by
        intro j _
        simp only [mul_pow, ← mul_assoc, ← pow_two, sq_abs]
        exact le_rfl)
    have h' := h.trans (mul_le_mul_of_nonneg_right (hrow i)
      (Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))))
    have hh : (∑ j, |X i j| * f i j ^ 2) ≤ D * ∑ j, |X i j| * (x i ^ 2 + y j ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_left (hf i j) (abs_nonneg (X i j))
      convert h using 1; ring
    exact h'.trans (by nlinarith [mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)])
  have hweight : (∑ i, ∑ j, |X i j| * (x i ^ 2 + y j ^ 2)) ≤
      2 * ((∑ i, x i ^ 2) + ∑ j, y j ^ 2) := by
    simp only [mul_add, Finset.sum_add_distrib]
    have hx : (∑ i, ∑ j, |X i j| * x i ^ 2) ≤ 2 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
    have hy : (∑ i, ∑ j, |X i j| * y j ^ 2) ≤ 2 * ∑ j, y j ^ 2 := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
    nlinarith
  calc
    _ ≤ ∑ i, 2 * D * ∑ j, |X i j| * (x i ^ 2 + y j ^ 2) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = 2 * D * ∑ i, ∑ j, |X i j| * (x i ^ 2 + y j ^ 2) := (Finset.mul_sum ..).symm
    _ ≤ 2 * D * (2 * ((∑ i, x i ^ 2) + ∑ j, y j ^ 2)) :=
      mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = _ := by ring

omit [DecidableEq ι] in
theorem localNonlinearRemainder_euclidean_bound (X : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (R : ℝ) (hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 4) (z : (ι ⊕ ι) → ℝ) (hz : ‖z‖ ≤ R) :
    localEuclideanNorm (localNonlinearRemainder X z) ≤ 8 * R * localEuclideanNorm z := by
  have hf (i j : ι) : localExpRemainder (z (Sum.inl i) + z (Sum.inr j)) ^ 2 ≤
      8 * R ^ 2 * (z (Sum.inl i) ^ 2 + z (Sum.inr j) ^ 2) := by
    let a := z (Sum.inl i) + z (Sum.inr j)
    have h1 := norm_le_pi_norm z (Sum.inl i)
    have h2 := norm_le_pi_norm z (Sum.inr j)
    rw [Real.norm_eq_abs] at h1 h2
    have ha : |a| ≤ 2 * R := (abs_add_le _ _).trans (by linarith)
    have hr : |localExpRemainder a| ≤ a ^ 2 := by
      simpa only [localExpRemainder, Real.norm_eq_abs, sq_abs] using
        Real.norm_exp_sub_one_sub_id_le (x := a) (by rw [Real.norm_eq_abs]; linarith)
    have hrem : |localExpRemainder a| ≤ 2 * R * |a| := hr.trans (by
      have h := mul_le_mul_of_nonneg_right ha (abs_nonneg a)
      nlinarith [sq_abs a])
    have hs := pow_le_pow_left₀ (abs_nonneg (localExpRemainder a)) hrem 2
    rw [sq_abs, mul_pow, sq_abs] at hs
    have hasq : a ^ 2 ≤ 2 * (z (Sum.inl i) ^ 2 + z (Sum.inr j) ^ 2) := by
      dsimp [a]
      nlinarith [sq_nonneg (z (Sum.inl i) - z (Sum.inr j))]
    have h := mul_le_mul_of_nonneg_left hasq (sq_nonneg (2 * R))
    nlinarith
  have hleft := weighted_marginal_remainder_sq_bound X hrow hcol
    (fun i j => localExpRemainder (z (Sum.inl i) + z (Sum.inr j)))
    (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) (8 * R ^ 2) (by positivity) hf
  have hright := weighted_marginal_remainder_sq_bound X.transpose hcol hrow
    (fun j i => localExpRemainder (z (Sum.inl i) + z (Sum.inr j)))
    (fun j => z (Sum.inr j)) (fun i => z (Sum.inl i)) (8 * R ^ 2) (by positivity)
    (fun j i => by simpa only [add_comm] using hf i j)
  apply (sq_le_sq₀ (localEuclideanNorm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hR0) (localEuclideanNorm_nonneg _))).mp
  rw [localEuclideanNorm_sq, mul_pow, localEuclideanNorm_sq]
  simp only [Fintype.sum_sum_type, localNonlinearRemainder, Sum.elim_inl, Sum.elim_inr]
  simp only [Matrix.transpose_apply] at hright
  nlinarith

theorem local_scaling_fixedPoint_euclidean_control (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (C q eps : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1) (heps : 0 ≤ eps)
    (hentry : ∀ i j, |localCenteredKernel X i j| ≤ C / Fintype.card ι)
    (hEq : ‖localCenteredKernel X‖ ≤ q)
    (ha : ∀ i, |matrixRowError X i| ≤ eps) (hb : ∀ j, |matrixColumnError X j| ≤ eps)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (hsmall : eps ≤ 1 / (256 * localScalingInverseBudget C q ^ 2))
    (z : (ι ⊕ ι) → ℝ) (hz : ‖z‖ ≤ 4 * localScalingInverseBudget C q * eps)
    (hfix : Function.IsFixedPt (localScalingMap X) z) :
    localEuclideanNorm z ≤ 2 * localScalingInverseBudget C q * localEuclideanNorm (localMarginalVector X) := by
  let L := localScalingInverseBudget C q
  let R := 4 * L * eps
  let A := localHessian X - localBalancedHessian (localCenteredKernel X)
  let M := localBalancedInverse (localCenteredKernel X)
  have hL : 3 / 2 ≤ L := by
    dsimp [L, localScalingInverseBudget]
    have h := div_nonneg (sq_nonneg C) (show 0 ≤ 1 - q by linarith)
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 / 4 := local_scaling_radius_le_quarter C q eps hC hq1 heps hsmall
  have hsmall' : eps * (256 * L ^ 2) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 256 * L ^ 2)).mp hsmall
  have hcoeff : L * (3 * eps + 8 * R) ≤ 1 / 2 := by
    have h := mul_nonneg (show 0 ≤ L - 3 / 2 by linarith) (mul_nonneg hL0 heps)
    dsimp [R]
    nlinarith
  have hA := localEuclideanNorm_mulVec_le A (3 * eps) (by positivity)
    (localHessian_difference_row_bound X hp eps heps ha hb)
    (localHessian_difference_column_bound X hp eps heps ha hb) z
  have hN := localNonlinearRemainder_euclidean_bound X hrow hcol R hR0 hR1 z hz
  have hM (v : (ι ⊕ ι) → ℝ) : localEuclideanNorm (M *ᵥ v) ≤ L * localEuclideanNorm v :=
    localEuclideanNorm_mulVec_le M L hL0
      (localBalancedInverse_absolute_row_bound _ hp C q hC hq0 hq1 hentry hEq)
      (localBalancedInverse_absolute_column_bound _ hp C q hC hq0 hq1 hentry hEq) v
  have hnorm : localEuclideanNorm z ≤ L * (localEuclideanNorm (localMarginalVector X) +
      (3 * eps + 8 * R) * localEuclideanNorm z) := by
    have h := congrArg localEuclideanNorm hfix.eq
    change localEuclideanNorm (-(M *ᵥ (localMarginalVector X + A *ᵥ z + localNonlinearRemainder X z))) =
      localEuclideanNorm z at h
    rw [localEuclideanNorm_neg] at h
    rw [← h]
    apply (hM _).trans
    apply mul_le_mul_of_nonneg_left _ hL0
    have hh := (localEuclideanNorm_add_le (localMarginalVector X + A *ᵥ z) (localNonlinearRemainder X z)).trans
      (add_le_add (localEuclideanNorm_add_le (localMarginalVector X) (A *ᵥ z)) le_rfl)
    nlinarith
  have h := mul_le_mul_of_nonneg_right hcoeff (localEuclideanNorm_nonneg z)
  change localEuclideanNorm z ≤ 2 * L * _
  nlinarith

omit [DecidableEq ι] in
theorem localScaledMatrix_frobenius_change_sq (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (C : ℝ) (hentry : ∀ i j, |X i j| ≤ C / Fintype.card ι)
    (z : (ι ⊕ ι) → ℝ) (hz : ‖z‖ ≤ 1 / 4) :
    realFrobeniusNorm (localScaledMatrix X z - X) ^ 2 ≤
      8 * C ^ 2 / Fintype.card ι * localEuclideanNorm z ^ 2 := by
  have hpR : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpoint (i j : ι) : (localScaledMatrix X z - X) i j ^ 2 ≤
      8 * (C / Fintype.card ι) ^ 2 * (z (Sum.inl i) ^ 2 + z (Sum.inr j) ^ 2) := by
    let a := z (Sum.inl i) + z (Sum.inr j)
    have h1 := norm_le_pi_norm z (Sum.inl i)
    have h2 := norm_le_pi_norm z (Sum.inr j)
    rw [Real.norm_eq_abs] at h1 h2
    have ha : |a| ≤ 1 / 2 := (abs_add_le _ _).trans (by linarith)
    have h := local_exp_sub_one_bound a (by linarith)
    have hs := pow_le_pow_left₀ (abs_nonneg (Real.exp a - 1)) h 2
    simp only [sq_abs, mul_pow] at hs
    have hasq : a ^ 2 ≤ 2 * (z (Sum.inl i) ^ 2 + z (Sum.inr j) ^ 2) := by
      dsimp [a]
      nlinarith [sq_nonneg (z (Sum.inl i) - z (Sum.inr j))]
    have he : (Real.exp a - 1) ^ 2 ≤ 8 * (z (Sum.inl i) ^ 2 + z (Sum.inr j) ^ 2) := by nlinarith
    have hx := pow_le_pow_left₀ (abs_nonneg (X i j)) (hentry i j) 2
    rw [sq_abs] at hx
    have hd : (localScaledMatrix X z - X) i j = X i j * (Real.exp a - 1) := by
      simp only [localScaledMatrix, Matrix.sub_apply]
      dsimp [a]
      ring
    rw [hd, mul_pow]
    have hh := mul_le_mul hx he (sq_nonneg _) (sq_nonneg _)
    nlinarith
  rw [realFrobeniusNorm_sq, localEuclideanNorm_sq]
  calc
    _ ≤ ∑ i, ∑ j, 8 * (C / Fintype.card ι) ^ 2 *
        (z (Sum.inl i) ^ 2 + z (Sum.inr j) ^ 2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpoint i j))
    _ = 8 * (C / Fintype.card ι) ^ 2 * ∑ i, ∑ j,
        (z (Sum.inl i) ^ 2 + z (Sum.inr j) ^ 2) := by simp only [Finset.mul_sum]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.mul_sum, Fintype.sum_sum_type]
      field_simp [hpR]

end TournamentHamiltonian
