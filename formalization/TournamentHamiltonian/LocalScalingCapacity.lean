import TournamentHamiltonian.LocalScalingDisplacement

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def localScalingCapacity (z : (ι ⊕ ι) → ℝ) : ℝ :=
  (∑ i, z (Sum.inl i)) + ∑ j, z (Sum.inr j)

noncomputable def localCapacityIntegrand (a : ℝ) : ℝ :=
  Real.exp a * a - Real.exp a + 1

theorem localCapacityIntegrand_nonneg (a : ℝ) : 0 ≤ localCapacityIntegrand a := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-a)) (Real.exp_pos a).le
  rw [← Real.exp_add] at h
  simp only [add_neg_cancel, Real.exp_zero] at h
  dsimp [localCapacityIntegrand]
  nlinarith

theorem localCapacityIntegrand_upper (a : ℝ) (ha : |a| ≤ 1 / 2) :
    localCapacityIntegrand a ≤ 2 * a ^ 2 := by
  have hr : 0 ≤ Real.exp a - 1 - a := by linarith [Real.add_one_le_exp a]
  have he := local_exp_sub_one_bound a (by linarith)
  have hm := mul_le_mul_of_nonneg_left he (abs_nonneg a)
  have hab : a * (Real.exp a - 1) ≤ |a| * |Real.exp a - 1| := le_abs_self _ |>.trans (by rw [abs_mul])
  dsimp [localCapacityIntegrand]
  nlinarith [sq_abs a]

omit [DecidableEq ι] in
theorem localMarginalVector_euclidean_sq (X : Matrix ι ι ℝ) :
    localEuclideanNorm (localMarginalVector X) ^ 2 =
      (∑ i, matrixRowError X i ^ 2) + ∑ j, matrixColumnError X j ^ 2 := by
  simp only [localEuclideanNorm_sq, Fintype.sum_sum_type, localMarginalVector,
    Sum.elim_inl, Sum.elim_inr]

omit [DecidableEq ι] in
theorem localScalingCapacity_eq_integrand (X : Matrix ι ι ℝ)
    (hmass : matrixEntryMass X = Fintype.card ι) (z : (ι ⊕ ι) → ℝ)
    (hrow : ∀ i, ∑ j, localScaledMatrix X z i j = 1)
    (hcol : ∀ j, ∑ i, localScaledMatrix X z i j = 1) :
    localScalingCapacity z = ∑ i, ∑ j, X i j *
      localCapacityIntegrand (z (Sum.inl i) + z (Sum.inr j)) := by
  have hmassB : (∑ i, ∑ j, localScaledMatrix X z i j) = Fintype.card ι := by simp [hrow]
  have hleft : (∑ i, ∑ j, localScaledMatrix X z i j * z (Sum.inl i)) = ∑ i, z (Sum.inl i) := by
    simp only [← Finset.sum_mul, hrow, one_mul]
  have hright : (∑ i, ∑ j, localScaledMatrix X z i j * z (Sum.inr j)) = ∑ j, z (Sum.inr j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, one_mul]
  have hmassX : (∑ i, ∑ j, X i j) = Fintype.card ι := hmass
  simp only [localCapacityIntegrand, mul_add, mul_sub, mul_one, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← mul_assoc]
  change localScalingCapacity z =
    (∑ i, ∑ j, localScaledMatrix X z i j * z (Sum.inl i)) +
      (∑ i, ∑ j, localScaledMatrix X z i j * z (Sum.inr j)) -
        (∑ i, ∑ j, localScaledMatrix X z i j) + (∑ i, ∑ j, X i j)
  rw [hleft, hright, hmassB, hmassX]
  dsimp [localScalingCapacity]
  ring

omit [DecidableEq ι] in
theorem localScalingCapacity_nonnegative (X : Matrix ι ι ℝ)
    (hX : ∀ i j, 0 ≤ X i j) (hmass : matrixEntryMass X = Fintype.card ι)
    (z : (ι ⊕ ι) → ℝ) (hrow : ∀ i, ∑ j, localScaledMatrix X z i j = 1)
    (hcol : ∀ j, ∑ i, localScaledMatrix X z i j = 1) :
    0 ≤ localScalingCapacity z := by
  rw [localScalingCapacity_eq_integrand X hmass z hrow hcol]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (hX i j) (localCapacityIntegrand_nonneg _)))

omit [DecidableEq ι] in
theorem localScalingCapacity_euclidean_bound (X : Matrix ι ι ℝ)
    (hX : ∀ i j, 0 ≤ X i j) (hmass : matrixEntryMass X = Fintype.card ι)
    (hrowX : ∀ i, ∑ j, |X i j| ≤ 2) (hcolX : ∀ j, ∑ i, |X i j| ≤ 2)
    (z : (ι ⊕ ι) → ℝ) (hz : ‖z‖ ≤ 1 / 4)
    (hrow : ∀ i, ∑ j, localScaledMatrix X z i j = 1)
    (hcol : ∀ j, ∑ i, localScaledMatrix X z i j = 1) :
    localScalingCapacity z ≤ 8 * localEuclideanNorm z ^ 2 := by
  have hpoint (i j : ι) : X i j * localCapacityIntegrand (z (Sum.inl i) + z (Sum.inr j)) ≤
      4 * X i j * (z (Sum.inl i) ^ 2 + z (Sum.inr j) ^ 2) := by
    have hi := norm_le_pi_norm z (Sum.inl i)
    have hj := norm_le_pi_norm z (Sum.inr j)
    rw [Real.norm_eq_abs] at hi hj
    have ha : |z (Sum.inl i) + z (Sum.inr j)| ≤ 1 / 2 := (abs_add_le _ _).trans (by linarith)
    have h := mul_le_mul_of_nonneg_left (localCapacityIntegrand_upper _ ha) (hX i j)
    have hh := mul_le_mul_of_nonneg_left (show
      (z (Sum.inl i) + z (Sum.inr j)) ^ 2 ≤
        2 * (z (Sum.inl i) ^ 2 + z (Sum.inr j) ^ 2) by
          nlinarith [sq_nonneg (z (Sum.inl i) - z (Sum.inr j))]) (hX i j)
    nlinarith
  have hr (i : ι) : (∑ j, X i j) ≤ 2 := by simpa only [abs_of_nonneg (hX i _)] using hrowX i
  have hc (j : ι) : (∑ i, X i j) ≤ 2 := by simpa only [abs_of_nonneg (hX _ j)] using hcolX j
  have hl : (∑ i, ∑ j, X i j * z (Sum.inl i) ^ 2) ≤ 2 * ∑ i, z (Sum.inl i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hr i) (sq_nonneg _)
  have hh : (∑ i, ∑ j, X i j * z (Sum.inr j) ^ 2) ≤ 2 * ∑ j, z (Sum.inr j) ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hc j) (sq_nonneg _)
  rw [localScalingCapacity_eq_integrand X hmass z hrow hcol, localEuclideanNorm_sq,
    Fintype.sum_sum_type]
  calc
    _ ≤ ∑ i, ∑ j, 4 * X i j * (z (Sum.inl i) ^ 2 + z (Sum.inr j) ^ 2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpoint i j))
    _ = 4 * ((∑ i, ∑ j, X i j * z (Sum.inl i) ^ 2) +
        ∑ i, ∑ j, X i j * z (Sum.inr j) ^ 2) := by
      simp only [mul_add, ← Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
    _ ≤ _ := by linarith

omit [DecidableEq ι] in
theorem localScaledMatrix_frobenius_change (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (C : ℝ) (hC : 0 ≤ C) (hentry : ∀ i j, |X i j| ≤ C / Fintype.card ι)
    (z : (ι ⊕ ι) → ℝ) (hz : ‖z‖ ≤ 1 / 4) :
    realFrobeniusNorm (localScaledMatrix X z - X) ≤
      4 * C / Real.sqrt (Fintype.card ι) * localEuclideanNorm z := by
  have hpR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  have hcoef : (4 * C / Real.sqrt (Fintype.card ι)) ^ 2 = 16 * C ^ 2 / Fintype.card ι := by
    rw [div_pow, Real.sq_sqrt hpR.le]
    ring
  have h := localScaledMatrix_frobenius_change_sq X hp C hentry z hz
  apply (sq_le_sq₀ (realFrobeniusNorm_nonneg _)
    (mul_nonneg (div_nonneg (by positivity) (Real.sqrt_nonneg _)) (localEuclideanNorm_nonneg _))).mp
  rw [mul_pow, hcoef]
  have hn : 0 ≤ C ^ 2 / Fintype.card ι * localEuclideanNorm z ^ 2 := by positivity
  ring_nf at h hn ⊢
  linarith

/-- The genuine balancing point constructed by contraction has dimension-uniform
Euclidean displacement, Frobenius displacement, and nonnegative capacity. -/
theorem exists_local_scaling_displacement_capacity (X : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (hX : ∀ i j, 0 ≤ X i j)
    (hmass : matrixEntryMass X = Fintype.card ι)
    (K C q eps : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (heps : 0 ≤ eps)
    (hXentry : ∀ i j, |X i j| ≤ K / Fintype.card ι)
    (hentry : ∀ i j, |localCenteredKernel X i j| ≤ C / Fintype.card ι)
    (hEq : ‖localCenteredKernel X‖ ≤ q)
    (ha : ∀ i, |matrixRowError X i| ≤ eps) (hb : ∀ j, |matrixColumnError X j| ≤ eps)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (hsmall : eps ≤ 1 / (256 * localScalingInverseBudget C q ^ 2)) :
    ∃ z : (ι ⊕ ι) → ℝ,
      ‖z‖ ≤ 4 * localScalingInverseBudget C q * eps ∧
      (∑ i, z (Sum.inl i)) = (∑ i, z (Sum.inr i)) ∧
      (∀ i, ∑ j, localScaledMatrix X z i j = 1) ∧
      (∀ j, ∑ i, localScaledMatrix X z i j = 1) ∧
      localEuclideanNorm z ≤ 2 * localScalingInverseBudget C q * localEuclideanNorm (localMarginalVector X) ∧
      realFrobeniusNorm (localScaledMatrix X z - X) ≤
        8 * K * localScalingInverseBudget C q / Real.sqrt (Fintype.card ι) *
          localEuclideanNorm (localMarginalVector X) ∧
      0 ≤ localScalingCapacity z ∧
      localScalingCapacity z ≤ 32 * localScalingInverseBudget C q ^ 2 *
        localEuclideanNorm (localMarginalVector X) ^ 2 := by
  obtain ⟨z, hz, hfix⟩ := exists_local_scaling_fixedPoint X hp C q eps hC hq0 hq1 heps
    hentry hEq ha hb hrow hcol hsmall
  have hbal := localScaling_fixedPoint_balances X hp hmass q hq0 hq1 hEq z hfix
  have hr (i : ι) : ∑ j, localScaledMatrix X z i j = 1 := by
    have h := congrFun hbal.2 (Sum.inl i)
    change (∑ j, localScaledMatrix X z i j) - 1 = 0 at h
    linarith
  have hc (j : ι) : ∑ i, localScaledMatrix X z i j = 1 := by
    have h := congrFun hbal.2 (Sum.inr j)
    change (∑ i, localScaledMatrix X z i j) - 1 = 0 at h
    linarith
  have hzsmall : ‖z‖ ≤ 1 / 4 := hz.trans (local_scaling_radius_le_quarter C q eps hC hq1 heps hsmall)
  have hL : 0 ≤ localScalingInverseBudget C q := by
    dsimp [localScalingInverseBudget]
    have h := div_nonneg (sq_nonneg C) (show 0 ≤ 1 - q by linarith)
    linarith
  have hdisp := local_scaling_fixedPoint_euclidean_control X hp C q eps hC hq0 hq1 heps
    hentry hEq ha hb hrow hcol hsmall z hz hfix
  refine ⟨z, hz, sub_eq_zero.mp hbal.1, hr, hc, hdisp, ?_,
    localScalingCapacity_nonnegative X hX hmass z hr hc, ?_⟩
  · have hf := localScaledMatrix_frobenius_change X hp K hK hXentry z hzsmall
    have h := mul_le_mul_of_nonneg_left hdisp
      (show 0 ≤ 4 * K / Real.sqrt (Fintype.card ι) by positivity)
    apply hf.trans
    convert h using 1
    ring
  · have hcap := localScalingCapacity_euclidean_bound X hX hmass hrow hcol z hzsmall hr hc
    have hsq := pow_le_pow_left₀ (localEuclideanNorm_nonneg z) hdisp 2
    simp only [mul_pow] at hsq
    nlinarith

end TournamentHamiltonian
