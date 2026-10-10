import TournamentHamiltonian.CoreEncodingInjectivity
import TournamentHamiltonian.CoreEncodingCount
import TournamentHamiltonian.FiniteGaussianCoreWindow

/-! Unconditional excess activity bounds for the actual centered permanent coefficients. -/

namespace TournamentHamiltonian

open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem actualCoreExcessCoefficient_finite_window_le (B : Matrix ι ι ℝ)
    (j : ℕ) (hj : 0 < j) (s : Finset ℕ) (C q R : ℝ)
    (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i l, |B i l| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (hgap : R * q < 1) :
    (∑ k ∈ s, |actualCoreExcessCoefficient B j k| * R ^ k) ≤
      compressedActivityMajorant j (C * R + C ^ 2 * R ^ 2 / (1 - R * q)) /
        (Fintype.card ι : ℝ) ^ j := by
  have hq0 : 0 ≤ q := (norm_nonneg B).trans hq
  calc
    _ ≤ ∑ k ∈ s,
        (∑ b ∈ Finset.Icc 1 (2 * j),
          decoratedCorePathMass (κ := Fin k) (Fintype.card ι) C q R j b) / (k.factorial : ℝ) :=
      Finset.sum_le_sum (fun k _ =>
        actualCoreExcessCoefficient_abs_weighted_le_decorated_mass B j k hj C q R hC hn hR hB hq)
    _ ≤ ∑ k ∈ s,
        (∑ b ∈ Finset.Icc 1 (2 * j),
          ∑ x : EncodedCoreData (Fin k) j b, encodedCorePathWeight (Fintype.card ι) C q R x) /
          (k.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro b _
      have hdec := Subsingleton.elim (instDecidableEqFin k) (Classical.decEq (Fin k))
      rw [hdec]
      exact decoratedCorePathMass_le_encoded _ C q R j b hC hq0 hR
    _ = ∑ b ∈ Finset.Icc 1 (2 * j), ∑ k ∈ s,
        (∑ x : EncodedCoreData (Fin k) j b, encodedCorePathWeight (Fintype.card ι) C q R x) /
          (k.factorial : ℝ) := by simp_rw [Finset.sum_div]; rw [Finset.sum_comm]
    _ ≤ ∑ b ∈ Finset.Icc 1 (2 * j), compressedDegreeCompensation j b *
        (C * R + C ^ 2 * R ^ 2 / (1 - R * q)) ^ (b + j) / (Fintype.card ι : ℝ) ^ j :=
      Finset.sum_le_sum (fun b _ =>
        encodedCoreData_finite_window_weight_le _ C q R j b s hC hq0 hR hgap)
    _ = _ := by rw [← Finset.sum_div]; rfl

theorem compressedActivityMajorant_mono (j : ℕ) {A W : ℝ} (hA : 0 ≤ A) (hAW : A ≤ W) :
    compressedActivityMajorant j A ≤ compressedActivityMajorant j W := by
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hAW _) (compressedDegreeCompensation_nonneg j b)

theorem actualCoreExcessCoefficient_activity_le (B : Matrix ι ι ℝ)
    (j : ℕ) (hj : 0 < j) (s : Finset ℕ) (C q R W : ℝ)
    (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i l, |B i l| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (hgap : R * q < 1) (hW : 1 ≤ W)
    (hAW : C * R + C ^ 2 * R ^ 2 / (1 - R * q) ≤ W) :
    (∑ k ∈ s, |actualCoreExcessCoefficient B j k| * R ^ k) ≤
      ((710 * W ^ 3 * (j : ℝ)) / (Fintype.card ι : ℝ)) ^ j := by
  have hA : 0 ≤ C * R + C ^ 2 * R ^ 2 / (1 - R * q) := by positivity
  calc
    _ ≤ _ := actualCoreExcessCoefficient_finite_window_le B j hj s C q R hC hn hR hB hq hgap
    _ ≤ compressedActivityMajorant j W / (Fintype.card ι : ℝ) ^ j :=
      div_le_div_of_nonneg_right (compressedActivityMajorant_mono j hA hAW) (by positivity)
    _ ≤ (710 * W ^ 3 * (j : ℝ)) ^ j / (Fintype.card ι : ℝ) ^ j :=
      div_le_div_of_nonneg_right (compressedActivityMajorant_le j W hW) (by positivity)
    _ = _ := (div_pow _ _ _).symm

theorem actualCoreExcessCoefficient_one_window_le (B : Matrix ι ι ℝ)
    (s : Finset ℕ) (C q R W : ℝ)
    (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i l, |B i l| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (hgap : R * q < 1)
    (hAW : C * R + C ^ 2 * R ^ 2 / (1 - R * q) ≤ W) :
    (∑ k ∈ s, |actualCoreExcessCoefficient B 1 k| * R ^ k) ≤
      ((3 / 2 : ℝ) * W ^ 2 + (10 / 3 : ℝ) * W ^ 3) / (Fintype.card ι : ℝ) := by
  have hA : 0 ≤ C * R + C ^ 2 * R ^ 2 / (1 - R * q) := by positivity
  have h := (actualCoreExcessCoefficient_finite_window_le B 1 (by omega) s C q R hC hn hR hB hq hgap).trans
    (div_le_div_of_nonneg_right (compressedActivityMajorant_mono 1 hA hAW) (by positivity))
  simpa only [compressedActivityMajorant_one, pow_one] using h

/-- The finite Gaussian window bound follows only from the actual matrix norms,
centering, and the explicit scalar cutoff. -/
theorem actual_gaussian_window_error_from_matrix_bounds (B : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ l, B i l = 0) (hcol : ∀ l, ∑ i, B i l = 0)
    (M : ℕ) (C q R W : ℝ) (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i l, |B i l| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (hgap : R * q < 1) (hW : 1 ≤ W)
    (hAW : C * R + C ^ 2 * R ^ 2 / (1 - R * q) ≤ W)
    (hM : 16 * (710 * W ^ 3) * (M : ℝ) ≤ Fintype.card ι) :
    (∑ k ∈ Finset.range (M + 1),
      |distinctCoordinateSum B k / (k.factorial : ℝ) - bilinearGaussianCoefficient B k| * R ^ k) ≤
      gramGaussian (R • B) *
        ((((3 / 2 : ℝ) * W ^ 2 + (10 / 3 : ℝ) * W ^ 3) / (Fintype.card ι : ℝ)) +
          8 * (710 * W ^ 3) ^ 2 / (Fintype.card ι : ℝ) ^ 2) := by
  have hW0 : 0 ≤ W := by linarith
  apply actual_gaussian_finite_window_error_le B hrow hcol (Fintype.card ι) M
    (710 * W ^ 3) ((3 / 2 : ℝ) * W ^ 2 + (10 / 3 : ℝ) * W ^ 3) R hn (by positivity) hR
    ((mul_le_mul_of_nonneg_left hq hR).trans_lt hgap) hM
  · exact actualCoreExcessCoefficient_one_window_le B (Finset.range (M + 1)) C q R W
      hC hn hR hB hq hgap hAW
  · intro j hj
    have hjpos : 0 < j := by have h := (Finset.mem_Icc.mp hj).1; omega
    simpa only [excessWindowTerm, mul_assoc] using
      actualCoreExcessCoefficient_activity_le B j hjpos (Finset.range (M + 1)) C q R W
        hC hn hR hB hq hgap hW hAW

end TournamentHamiltonian
