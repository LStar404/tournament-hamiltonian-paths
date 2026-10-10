import TournamentHamiltonian.WeightedPrincipalGenerating

/-! Finite exponential inflation of the actual generating determinant. All
weighted errors are kept inside the score-product factor before absorption. -/
namespace TournamentHamiltonian
open scoped Classical

theorem actual_skew_kernel_det_ge_one {n : ℕ} (T : Tournament n) :
    1 ≤ ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det := by
  have h := signMatrix_normalized_kernel_det T 1
  simp only [one_pow, one_mul] at h
  rw [h]
  apply List.one_le_prod
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  linarith [pairedMasses_nonneg T x hx]

theorem weightedPrincipalMass_add_le_kernel_exp {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (w : Fin n → ℝ) (W : ℝ) (hW : 1 ≤ W) (hw1 : ∀ i, 1 ≤ w i) (hwW : ∀ i, w i ≤ W)
    (C R D : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hexcess : (∑ i, (w i - 1)) / n ≤ C * R) :
    weightedPrincipalMass T w + D / n ≤
      (2 * Real.exp 1 * ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det) *
        Real.exp (C * weightedPrincipalMoment W * R + D / n) := by
  let B := 2 * Real.exp 1 * ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det
  let x := C * weightedPrincipalMoment W * R + D / n
  have hM : 0 ≤ weightedPrincipalMoment W := weightedPrincipalMoment_nonneg W (by linarith)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hB : 1 ≤ B := by
    have he : 1 ≤ 2 * Real.exp 1 := by have h := Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1); linarith
    have h := mul_le_mul he (actual_skew_kernel_det_ge_one T) (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 ≤ 2 * Real.exp 1)
    simpa only [one_mul, B] using h
  have hmass := weightedPrincipalMass_le_kernel T hn w W hW hw1 hwW
  have herr := mul_le_mul_of_nonneg_right hexcess hM
  have hinflate := mul_le_mul_of_nonneg_right hB hx
  have hExp := mul_le_mul_of_nonneg_left (Real.add_one_le_exp x) (by linarith : 0 ≤ B)
  calc
    _ ≤ B + x := by dsimp [x, B] at *; nlinarith
    _ ≤ B * (1 + x) := by nlinarith
    _ ≤ B * Real.exp x := by convert hExp using 1; ring

end TournamentHamiltonian
