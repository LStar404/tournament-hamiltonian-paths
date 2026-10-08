import TournamentHamiltonian.LocalScalingExistence

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

theorem local_exp_upper_two (a : ℝ) (ha : |a| ≤ 1 / 2) : Real.exp a ≤ 2 := by
  have hr := Real.norm_exp_sub_one_sub_id_le (x := a) (by
    rw [Real.norm_eq_abs]
    linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs] at hr
  have hs : a ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  nlinarith [le_abs_self a, le_abs_self (Real.exp a - 1 - a)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem absolute_row_column_bound_opNorm (A : Matrix ι ι ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hrow : ∀ i, ∑ j, |A i j| ≤ L) (hcol : ∀ j, ∑ i, |A i j| ≤ L) : ‖A‖ ≤ L := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hL
  intro z
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  have hs := absolute_row_column_bound_mulVec_sq A L hL hrow hcol (fun i => z i)
  have hy : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A z‖ ^ 2 = ∑ i, (A *ᵥ (fun i => z i)) i ^ 2 := by
    change ‖WithLp.toLp 2 (A *ᵥ (fun i => z i))‖ ^ 2 = _
    simp [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [hy, mul_pow, EuclideanSpace.norm_sq_eq]
  simpa only [Real.norm_eq_abs, sq_abs] using hs

omit [DecidableEq ι] in
theorem localScaledMatrix_change_entry (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ)
    (R : ℝ) (_hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 4) (hz : ‖z‖ ≤ R) (i j : ι) :
    |(localScaledMatrix X z - X) i j| ≤ 4 * R * |X i j| := by
  have h1 := norm_le_pi_norm z (Sum.inl i)
  have h2 := norm_le_pi_norm z (Sum.inr j)
  rw [Real.norm_eq_abs] at h1 h2
  have ha : |z (Sum.inl i) + z (Sum.inr j)| ≤ 2 * R :=
    (abs_add_le _ _).trans (by linarith)
  have h := local_exp_sub_one_bound _ (show |z (Sum.inl i) + z (Sum.inr j)| ≤ 1 by linarith)
  have he : (localScaledMatrix X z - X) i j =
      X i j * (Real.exp (z (Sum.inl i) + z (Sum.inr j)) - 1) := by
    simp only [Matrix.sub_apply, localScaledMatrix]
    ring
  rw [he, abs_mul]
  have hb : |Real.exp (z (Sum.inl i) + z (Sum.inr j)) - 1| ≤ 4 * R := h.trans (by linarith)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (abs_nonneg (X i j))

omit [DecidableEq ι] in
theorem localScaledMatrix_change_row_bound (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (R : ℝ) (hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 4)
    (hz : ‖z‖ ≤ R) (i : ι) : (∑ j, |(localScaledMatrix X z - X) i j|) ≤ 8 * R := by
  calc
    _ ≤ ∑ j, 4 * R * |X i j| := Finset.sum_le_sum (fun j _ =>
      localScaledMatrix_change_entry X z R hR0 hR1 hz i j)
    _ = 4 * R * ∑ j, |X i j| := (Finset.mul_sum ..).symm
    _ ≤ 4 * R * 2 := mul_le_mul_of_nonneg_left (hrow i) (by positivity)
    _ = _ := by ring

omit [DecidableEq ι] in
theorem localScaledMatrix_change_column_bound (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ)
    (hcol : ∀ j, ∑ i, |X i j| ≤ 2) (R : ℝ) (hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 4)
    (hz : ‖z‖ ≤ R) (j : ι) : (∑ i, |(localScaledMatrix X z - X) i j|) ≤ 8 * R := by
  calc
    _ ≤ ∑ i, 4 * R * |X i j| := Finset.sum_le_sum (fun i _ =>
      localScaledMatrix_change_entry X z R hR0 hR1 hz i j)
    _ = 4 * R * ∑ i, |X i j| := (Finset.mul_sum ..).symm
    _ ≤ 4 * R * 2 := mul_le_mul_of_nonneg_left (hcol j) (by positivity)
    _ = _ := by ring

theorem localScaledMatrix_change_opNorm (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (R : ℝ) (hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 4) (hz : ‖z‖ ≤ R) :
    ‖localScaledMatrix X z - X‖ ≤ 8 * R :=
  absolute_row_column_bound_opNorm _ _ (by positivity)
    (localScaledMatrix_change_row_bound X z hrow R hR0 hR1 hz)
    (localScaledMatrix_change_column_bound X z hcol R hR0 hR1 hz)

omit [DecidableEq ι] in
theorem localScaledMatrix_dense_entry (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hentry : ∀ i j, |X i j| ≤ C / Fintype.card ι)
    (hz : ‖z‖ ≤ 1 / 4) (i j : ι) :
    |localScaledMatrix X z i j| ≤ 2 * C / Fintype.card ι := by
  have h1 := norm_le_pi_norm z (Sum.inl i)
  have h2 := norm_le_pi_norm z (Sum.inr j)
  rw [Real.norm_eq_abs] at h1 h2
  have ha : |z (Sum.inl i) + z (Sum.inr j)| ≤ 1 / 2 :=
    (abs_add_le _ _).trans (by linarith)
  rw [localScaledMatrix, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h := mul_le_mul (hentry i j) (local_exp_upper_two _ ha) (Real.exp_pos _).le
    (div_nonneg hC (Nat.cast_nonneg _))
  convert h using 1; ring

theorem marginalBalancedMatrix_change_opNorm (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (eps : ℝ) (heps : 0 ≤ eps) (ha : ∀ i, |matrixRowError X i| ≤ eps)
    (hb : ∀ j, |matrixColumnError X j| ≤ eps) : ‖X - marginalBalancedMatrix X‖ ≤ 2 * eps := by
  have hpR : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hp
  have hentry (i j : ι) : |(X - marginalBalancedMatrix X) i j| ≤ 2 * eps / Fintype.card ι := by
    simp only [Matrix.sub_apply, marginalBalancedMatrix, sub_sub_cancel]
    rw [abs_div, abs_of_pos hpR]
    apply div_le_div_of_nonneg_right _ hpR.le
    linarith [abs_add_le (matrixRowError X i) (matrixColumnError X j), ha i, hb j]
  apply absolute_row_column_bound_opNorm _ _ (by positivity)
  · intro i
    calc
      _ ≤ ∑ _j : ι, 2 * eps / Fintype.card ι := Finset.sum_le_sum (fun j _ => hentry i j)
      _ = _ := by simp [mul_div_cancel₀ _ hpR.ne']
  · intro j
    calc
      _ ≤ ∑ _i : ι, 2 * eps / Fintype.card ι := Finset.sum_le_sum (fun i _ => hentry i j)
      _ = _ := by simp [mul_div_cancel₀ _ hpR.ne']

theorem localScaledMatrix_centered_gap_bound (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (z : (ι ⊕ ι) → ℝ) (q eps R : ℝ) (heps : 0 ≤ eps)
    (hEq : ‖localCenteredKernel X‖ ≤ q)
    (ha : ∀ i, |matrixRowError X i| ≤ eps) (hb : ∀ j, |matrixColumnError X j| ≤ eps)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 4) (hz : ‖z‖ ≤ R) :
    ‖localScaledMatrix X z - averagingMatrix ι‖ ≤ q + 2 * eps + 8 * R := by
  have he : localScaledMatrix X z - averagingMatrix ι =
      (localScaledMatrix X z - X) + (X - marginalBalancedMatrix X) + localCenteredKernel X := by
    unfold localCenteredKernel
    abel
  rw [he]
  calc
    _ ≤ ‖localScaledMatrix X z - X‖ + ‖X - marginalBalancedMatrix X‖ + ‖localCenteredKernel X‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 8 * R + 2 * eps + q := add_le_add (add_le_add
      (localScaledMatrix_change_opNorm X z hrow hcol R hR0 hR1 hz)
      (marginalBalancedMatrix_change_opNorm X hp eps heps ha hb)) hEq
    _ = _ := by ring

theorem local_scaling_radius_le_quarter (C q eps : ℝ) (hC : 0 ≤ C) (hq1 : q < 1)
    (heps : 0 ≤ eps) (hsmall : eps ≤ 1 / (256 * localScalingInverseBudget C q ^ 2)) :
    4 * localScalingInverseBudget C q * eps ≤ 1 / 4 := by
  let L := localScalingInverseBudget C q
  have hL : 3 / 2 ≤ L := by
    dsimp [L, localScalingInverseBudget]
    have h := div_nonneg (sq_nonneg C) (show 0 ≤ 1 - q by linarith)
    linarith
  have hsmall' : eps * (256 * L ^ 2) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 256 * L ^ 2)).mp hsmall
  have h := mul_nonneg (show 0 ≤ L - 3 / 2 by linarith)
    (show 0 ≤ 4 * L * eps by positivity)
  change 4 * L * eps ≤ _
  nlinarith

/-- The complete dimension-uniform local scaling conclusion, including
the density and centered operator gap of the actual scaled matrix. -/
theorem exists_local_scaling (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (hmass : matrixEntryMass X = Fintype.card ι)
    (K C q eps : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1) (heps : 0 ≤ eps)
    (hXentry : ∀ i j, |X i j| ≤ K / Fintype.card ι)
    (hentry : ∀ i j, |localCenteredKernel X i j| ≤ C / Fintype.card ι)
    (hEq : ‖localCenteredKernel X‖ ≤ q)
    (ha : ∀ i, |matrixRowError X i| ≤ eps) (hb : ∀ j, |matrixColumnError X j| ≤ eps)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (hsmall : eps ≤ 1 / (256 * localScalingInverseBudget C q ^ 2))
    (hgap : eps ≤ (1 - q) / (2 * (32 * localScalingInverseBudget C q + 2))) :
    ∃ z : (ι ⊕ ι) → ℝ, ‖z‖ ≤ 4 * localScalingInverseBudget C q * eps ∧
      (∑ i, z (Sum.inl i)) = (∑ i, z (Sum.inr i)) ∧
      (∀ i, ∑ j, localScaledMatrix X z i j = 1) ∧
      (∀ j, ∑ i, localScaledMatrix X z i j = 1) ∧
      (∀ i j, |localScaledMatrix X z i j| ≤ 2 * K / Fintype.card ι) ∧
      ‖localScaledMatrix X z - averagingMatrix ι‖ ≤ (1 + q) / 2 := by
  obtain ⟨z, hz, hgauge, hr, hc⟩ := exists_local_balancing_potentials X hp hmass C q eps hC hq0 hq1 heps
    hentry hEq ha hb hrow hcol hsmall
  have hR1 := local_scaling_radius_le_quarter C q eps hC hq1 heps hsmall
  have hR0 : 0 ≤ 4 * localScalingInverseBudget C q * eps := mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (localScalingInverseBudget_nonneg C q hC hq1)) heps
  refine ⟨z, hz, hgauge, hr, hc, localScaledMatrix_dense_entry X z K hK hXentry (hz.trans hR1), ?_⟩
  have h := localScaledMatrix_centered_gap_bound X hp z q eps
    (4 * localScalingInverseBudget C q * eps) heps hEq ha hb hrow hcol hR0 hR1 hz
  have hL := localScalingInverseBudget_nonneg C q hC hq1
  have hgap' := (le_div_iff₀ (show 0 < 2 * (32 * localScalingInverseBudget C q + 2) by positivity)).mp hgap
  nlinarith

end TournamentHamiltonian
