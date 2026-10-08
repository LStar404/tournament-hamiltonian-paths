import TournamentHamiltonian.DeletionMass

namespace TournamentHamiltonian

noncomputable def pairedLeft (a : ℝ) : ℝ := (1 + a)⁻¹
noncomputable def pairedRight (a : ℝ) : ℝ := (1 - a)⁻¹
noncomputable def pairedV (a : ℝ) : ℝ := a / (1 - a ^ 2)
noncomputable def pairedW (a : ℝ) : ℝ := a ^ 2 / (1 - a ^ 2)

theorem pairedLeft_decomposition (a : ℝ) (ha : -1 < a ∧ a < 1) :
    pairedLeft a = 1 - pairedV a + pairedW a := by
  have hp : 1 + a ≠ 0 := by linarith [ha.1]
  have hm : 1 - a ≠ 0 := by linarith [ha.2]
  have hd : 1 - a ^ 2 ≠ 0 := by nlinarith [mul_ne_zero hp hm]
  unfold pairedLeft pairedV pairedW
  field_simp [hp, hd]
  ring

theorem pairedRight_decomposition (a : ℝ) (ha : -1 < a ∧ a < 1) :
    pairedRight a = 1 + pairedV a + pairedW a := by
  have hp : 1 + a ≠ 0 := by linarith [ha.1]
  have hm : 1 - a ≠ 0 := by linarith [ha.2]
  have hd : 1 - a ^ 2 ≠ 0 := by nlinarith [mul_ne_zero hp hm]
  unfold pairedRight pairedV pairedW
  field_simp [hm, hd]
  ring

theorem pairedLeft_mul_right (a : ℝ) (ha : -1 < a ∧ a < 1) :
    pairedLeft a * pairedRight a = 1 + pairedW a := by
  have hp : 1 + a ≠ 0 := by linarith [ha.1]
  have hm : 1 - a ≠ 0 := by linarith [ha.2]
  have hd : 1 - a ^ 2 ≠ 0 := by nlinarith [mul_ne_zero hp hm]
  unfold pairedLeft pairedRight pairedW
  field_simp [hp, hm, hd]
  ring

theorem score_mul_pairedV (a : ℝ) : a * pairedV a = pairedW a := by
  unfold pairedV pairedW
  ring

theorem signMatrix_bilinear_swap {n : ℕ} (T : Tournament n) (x y : Fin n → ℝ) :
    dotProduct x ((signMatrix T).mulVec y) =
      -dotProduct y ((signMatrix T).mulVec x) := by
  have h := Matrix.dotProduct_transpose_mulVec (signMatrix T) y x
  rw [signMatrix_transpose, Matrix.neg_mulVec, dotProduct_neg] at h
  exact h.symm

theorem signMatrix_mul_ones {n : ℕ} (T : Tournament n) :
    (signMatrix T).mulVec (fun _ => 1) = score T := by
  ext i
  simp [Matrix.mulVec, dotProduct, score]

theorem ones_dot_signMatrix_mul {n : ℕ} (T : Tournament n) (v : Fin n → ℝ) :
    dotProduct (fun _ => 1) ((signMatrix T).mulVec v) = -∑ i, v i * score T i := by
  rw [signMatrix_bilinear_swap, signMatrix_mul_ones]
  rfl

theorem matrixEntryMass_weighted {ι : Type*} [Fintype ι] (X : Matrix ι ι ℝ)
    (l r : ι → ℝ) :
    matrixEntryMass (fun i j => l i * X i j * r j) = dotProduct l (X.mulVec r) := by
  simp only [matrixEntryMass, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tournamentDensity_bilinear {n : ℕ} (T : Tournament n) (l r : Fin n → ℝ) :
    dotProduct l ((tournamentDensity T).mulVec r) =
      ((1 : ℝ) / (n - 1 : ℝ)) *
        ((∑ i, l i) * (∑ j, r j) - dotProduct l r +
          dotProduct l ((signMatrix T).mulVec r)) := by
  have hC : tournamentDensity T = ((1 : ℝ) / (n - 1 : ℝ)) •
      (Matrix.of (fun _ _ => 1) - (1 : Matrix (Fin n) (Fin n) ℝ) + signMatrix T) := by
    simp only [tournamentDensity_eq_shiftedSkew, shiftedSkewKernel, smul_add, smul_sub]
    abel
  have hJ : dotProduct l ((Matrix.of (fun _ _ => (1 : ℝ))).mulVec r) =
      (∑ i, l i) * (∑ j, r j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul]
    rw [← Finset.sum_mul]
  rw [hC, Matrix.smul_mulVec, dotProduct_smul]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add, dotProduct_sub,
    Matrix.one_mulVec, hJ, smul_eq_mul]

theorem pairedSkew_bilinear {n : ℕ} (T : Tournament n) (v w : Fin n → ℝ) :
    dotProduct ((fun _ => (1 : ℝ)) - v + w)
        ((signMatrix T).mulVec ((fun _ => (1 : ℝ)) + v + w)) =
      -2 * dotProduct v (score T) + 2 * dotProduct w ((signMatrix T).mulVec v) := by
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, sub_dotProduct]
  rw [skew_quadratic_zero _ (signMatrix_skew T) (fun _ => 1),
    skew_quadratic_zero _ (signMatrix_skew T) v,
    skew_quadratic_zero _ (signMatrix_skew T) w,
    signMatrix_mul_ones, ones_dot_signMatrix_mul, ones_dot_signMatrix_mul]
  rw [signMatrix_bilinear_swap T v w]
  simp only [dotProduct]
  ring

noncomputable def tournamentScorePotential {n : ℕ} (T : Tournament n) (i : Fin n) : ℝ :=
  score T i / (n - 1 : ℝ)

noncomputable def preconditionedTournamentDensity {n : ℕ} (T : Tournament n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => pairedLeft (tournamentScorePotential T i) * tournamentDensity T i j *
    pairedRight (tournamentScorePotential T j)

/-- The exact full-mass identity for the actual paired preconditioning. -/
theorem preconditionedTournamentDensity_mass {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (ha : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1) :
    matrixEntryMass (preconditionedTournamentDensity T) - n =
      ((∑ i, pairedW (tournamentScorePotential T i)) ^ 2 -
          (∑ i, pairedV (tournamentScorePotential T i)) ^ 2 +
          (∑ i, pairedW (tournamentScorePotential T i)) +
          2 * dotProduct (fun i => pairedW (tournamentScorePotential T i))
            ((signMatrix T).mulVec (fun i => pairedV (tournamentScorePotential T i)))) /
        (n - 1 : ℝ) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) - 1 ≠ 0 := by linarith
  let a := tournamentScorePotential T
  let v : Fin n → ℝ := fun i => pairedV (a i)
  let w : Fin n → ℝ := fun i => pairedW (a i)
  have hL : (fun i => pairedLeft (a i)) = (fun _ => (1 : ℝ)) - v + w := by
    funext i
    exact pairedLeft_decomposition (a i) (ha i)
  have hR : (fun i => pairedRight (a i)) = (fun _ => (1 : ℝ)) + v + w := by
    funext i
    exact pairedRight_decomposition (a i) (ha i)
  have hLs : (∑ i, pairedLeft (a i)) = (n : ℝ) - (∑ i, v i) + ∑ i, w i := by
    rw [hL]
    simp [Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hRs : (∑ i, pairedRight (a i)) = (n : ℝ) + (∑ i, v i) + ∑ i, w i := by
    rw [hR]
    simp [Pi.add_apply, Finset.sum_add_distrib]
  have hdiag : dotProduct (fun i => pairedLeft (a i)) (fun i => pairedRight (a i)) =
      (n : ℝ) + ∑ i, w i := by
    simp only [dotProduct, pairedLeft_mul_right (a _) (ha _)]
    simp [Finset.sum_add_distrib, w]
  have hscore : ∀ i, score T i = (n - 1 : ℝ) * a i := by
    intro i
    dsimp [a, tournamentScorePotential]
    field_simp [hne]
  have hv : dotProduct v (score T) = (n - 1 : ℝ) * ∑ i, w i := by
    simp only [dotProduct, hscore]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [v, w]
    rw [mul_left_comm, mul_comm (pairedV (a i)) (a i), score_mul_pairedV]
  have hbil : dotProduct (fun i => pairedLeft (a i))
      ((signMatrix T).mulVec (fun i => pairedRight (a i))) =
        -2 * ((n - 1 : ℝ) * ∑ i, w i) + 2 * dotProduct w ((signMatrix T).mulVec v) := by
    rw [hL, hR, pairedSkew_bilinear, hv]
  change matrixEntryMass (fun i j => pairedLeft (a i) * tournamentDensity T i j *
    pairedRight (a j)) - n = _
  rw [matrixEntryMass_weighted, tournamentDensity_bilinear, hLs, hRs, hdiag, hbil]
  change _ = ((∑ i, w i) ^ 2 - (∑ i, v i) ^ 2 + (∑ i, w i) +
    2 * dotProduct w ((signMatrix T).mulVec v)) / (n - 1 : ℝ)
  field_simp [hne]
  ring

theorem preconditionedTournamentDensity_row_error {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (ha : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1)
    (i : Fin n) :
    matrixRowError (preconditionedTournamentDensity T) i =
      pairedLeft (tournamentScorePotential T i) *
        ∑ j, tournamentDensity T i j * (pairedRight (tournamentScorePotential T j) - 1) := by
  have hp : 1 + tournamentScorePotential T i ≠ 0 := by linarith [(ha i).1]
  have hrow : (∑ j, tournamentDensity T i j) = 1 + tournamentScorePotential T i := by
    have h := tournamentDensity_row_error T hn i
    change (∑ j, tournamentDensity T i j) - 1 = tournamentScorePotential T i at h
    linarith
  simp only [matrixRowError, preconditionedTournamentDensity, mul_assoc,
    mul_sub, Finset.sum_sub_distrib, mul_one]
  rw [← Finset.mul_sum, hrow]
  unfold pairedLeft
  rw [inv_mul_cancel₀ hp]

theorem preconditionedTournamentDensity_column_error {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (ha : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1)
    (j : Fin n) :
    matrixColumnError (preconditionedTournamentDensity T) j =
      pairedRight (tournamentScorePotential T j) *
        ∑ i, tournamentDensity T i j * (pairedLeft (tournamentScorePotential T i) - 1) := by
  have hm : 1 - tournamentScorePotential T j ≠ 0 := by linarith [(ha j).2]
  have hcol : (∑ i, tournamentDensity T i j) = 1 - tournamentScorePotential T j := by
    have h := tournamentDensity_column_error T hn j
    change (∑ i, tournamentDensity T i j) - 1 = -score T j / (n - 1 : ℝ) at h
    rw [neg_div] at h
    change (∑ i, tournamentDensity T i j) - 1 = -tournamentScorePotential T j at h
    linarith
  have hfactor : (∑ i, preconditionedTournamentDensity T i j) =
      pairedRight (tournamentScorePotential T j) *
        ∑ i, tournamentDensity T i j * pairedLeft (tournamentScorePotential T i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold preconditionedTournamentDensity
    ring
  rw [matrixColumnError, hfactor]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_one]
  rw [hcol]
  unfold pairedRight
  rw [inv_mul_cancel₀ hm]

end TournamentHamiltonian
