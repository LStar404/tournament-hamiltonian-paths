import TournamentHamiltonian.GramCentering
import TournamentHamiltonian.SkewGeometry
import TournamentHamiltonian.PreconditioningBounds
import Mathlib.Algebra.Order.Chebyshev

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem submatrix_opNorm_le (X : Matrix ι κ ℝ) (R : Finset ι) (C : Finset κ) :
    ‖X.submatrix (fun i : R => i.val) (fun j : C => j.val)‖ ≤ ‖X‖ := by
  have h := row_submatrix_opNorm_le (X.submatrix (fun i : R => i.val) id).transpose C
  have he : (X.submatrix (fun i : R => i.val) id).transpose.submatrix
      (fun j : C => j.val) id =
      (X.submatrix (fun i : R => i.val) (fun j : C => j.val)).transpose := by ext i j; rfl
  rw [he] at h
  have ht' : ‖(X.submatrix (fun i : R => i.val) id).transpose‖ =
      ‖X.submatrix (fun i : R => i.val) id‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (X.submatrix (fun i : R => i.val) id)
  have ht'' : ‖(X.submatrix (fun i : R => i.val) (fun j : C => j.val)).transpose‖ =
      ‖X.submatrix (fun i : R => i.val) (fun j : C => j.val)‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (X.submatrix (fun i : R => i.val) (fun j : C => j.val))
  rw [ht', ht''] at h
  exact h.trans (row_submatrix_opNorm_le X R)

theorem retained_flat_action_sq_le (X : Matrix ι κ ℝ) (I : Finset ι) (J : Finset κ)
    (hc : 0 < (Jᶜ : Finset κ).card) :
    (∑ i : (Iᶜ : Finset ι),
      ((X.submatrix (fun i : (Iᶜ : Finset ι) => i.val) (fun j : (Jᶜ : Finset κ) => j.val)) *ᵥ
        flatUnitVector (Jᶜ : Finset κ)) i ^ 2) ≤
      2 * ((∑ i, (∑ j, X i j) ^ 2) + (∑ i, (∑ j ∈ J, X i j) ^ 2)) /
        (Jᶜ : Finset κ).card := by
  have hcR : 0 < ((Jᶜ : Finset κ).card : ℝ) := by exact_mod_cast hc
  have he (i : (Iᶜ : Finset ι)) :
      ((X.submatrix (fun i : (Iᶜ : Finset ι) => i.val) (fun j : (Jᶜ : Finset κ) => j.val)) *ᵥ
        flatUnitVector (Jᶜ : Finset κ)) i =
        ((Real.sqrt ((Jᶜ : Finset κ).card : ℝ))⁻¹) *
          ((∑ j, X i.val j) - ∑ j ∈ J, X i.val j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, flatUnitVector,
      Fintype.card_coe]
    rw [← Finset.sum_mul, Finset.sum_coe_sort (Jᶜ) (fun j => X i.val j), mul_comm]
    congr 1
    have h := Finset.sum_add_sum_compl J (fun j => X i.val j)
    linarith
  simp only [he, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [← Finset.mul_sum]
  have hs : (∑ i : (Iᶜ : Finset ι), ((∑ j, X i.val j) - ∑ j ∈ J, X i.val j) ^ 2) ≤
      2 * ((∑ i, (∑ j, X i j) ^ 2) + ∑ i, (∑ j ∈ J, X i j) ^ 2) := by
    calc
      _ ≤ ∑ i : (Iᶜ : Finset ι),
          (2 * (∑ j, X i.val j) ^ 2 + 2 * (∑ j ∈ J, X i.val j) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg ((∑ j, X i.val j) + ∑ j ∈ J, X i.val j)]
      _ ≤ ∑ i, (2 * (∑ j, X i j) ^ 2 + 2 * (∑ j ∈ J, X i j) ^ 2) := by
        simp only [Finset.univ_eq_attach]
        rw [Finset.sum_attach (Iᶜ) (fun i =>
          2 * (∑ j, X i j) ^ 2 + 2 * (∑ j ∈ J, X i j) ^ 2)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => by positivity)
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hcR.le)

theorem shiftedSkewKernel_deleted_indicator_sq_le {n : ℕ} (T : Tournament n)
    (J : Finset (Fin n)) :
    (∑ i, (∑ j ∈ J, shiftedSkewKernel T i j) ^ 2) ≤
      (J.card : ℝ) ^ 2 * n / (n - 1 : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ i, (J.card : ℝ) * (∑ j ∈ J, shiftedSkewKernel T i j ^ 2) :=
      Finset.sum_le_sum (fun i _ => sq_sum_le_card_mul_sum_sq)
    _ = _ := by simp [shiftedSkewKernel_entry_sq, div_eq_mul_inv]; ring

noncomputable def deletedShiftedSkewKernel {n : ℕ} (T : Tournament n)
    (I J : Finset (Fin n)) : Matrix (Iᶜ : Finset (Fin n)) (Jᶜ : Finset (Fin n)) ℝ :=
  (shiftedSkewKernel T).submatrix (fun i => i.val) (fun j => j.val)

noncomputable def centeredDeletedSkewKernel {n : ℕ} (T : Tournament n)
    (I J : Finset (Fin n)) : Matrix (Iᶜ : Finset (Fin n)) (Jᶜ : Finset (Fin n)) ℝ :=
  centeringProjection (Iᶜ : Finset (Fin n)) * deletedShiftedSkewKernel T I J *
    centeringProjection (Jᶜ : Finset (Fin n))

theorem shiftedSkewKernel_transpose_deleted_indicator_sq_le {n : ℕ} (T : Tournament n)
    (I : Finset (Fin n)) :
    (∑ j, (∑ i ∈ I, (shiftedSkewKernel T).transpose j i) ^ 2) ≤
      (I.card : ℝ) ^ 2 * n / (n - 1 : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ j, (I.card : ℝ) * (∑ i ∈ I, (shiftedSkewKernel T).transpose j i ^ 2) :=
      Finset.sum_le_sum (fun j _ => sq_sum_le_card_mul_sum_sq)
    _ = _ := by simp [Matrix.transpose_apply, shiftedSkewKernel_entry_sq, div_eq_mul_inv]; ring

noncomputable def gaussianScoreVariance {n : ℕ} (T : Tournament n) : ℝ :=
  (∑ i, score T i ^ 2) / (n - 1 : ℝ) ^ 2

theorem gaussianScoreVariance_nonneg {n : ℕ} (T : Tournament n) :
    0 ≤ gaussianScoreVariance T := by
  unfold gaussianScoreVariance
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)

theorem deletedShiftedSkewKernel_row_flat_sq_le {n t : ℕ} (T : Tournament n)
    (I J : Finset (Fin n)) (_hI : I.card = t) (hJ : J.card = t) (ht : t < n) :
    (∑ i, (deletedShiftedSkewKernel T I J *ᵥ flatUnitVector (Jᶜ : Finset (Fin n))) i ^ 2) ≤
      2 * (gaussianScoreVariance T + (n : ℝ) * (1 + (t : ℝ) ^ 2) / (n - 1 : ℝ) ^ 2) /
        (n - t : ℝ) := by
  have hcard : (Jᶜ : Finset (Fin n)).card = n - t := by
    rw [Finset.card_compl, Fintype.card_fin, hJ]
  have h := retained_flat_action_sq_le (shiftedSkewKernel T) I J (by rw [hcard]; omega)
  change (∑ i, (deletedShiftedSkewKernel T I J *ᵥ flatUnitVector (Jᶜ : Finset (Fin n))) i ^ 2) ≤ _ at h
  rw [shiftedSkewKernel_row_sum_sq, hcard, Nat.cast_sub ht.le] at h
  have hm : 0 < (n - t : ℝ) := by
    have htR : (t : ℝ) < n := by exact_mod_cast ht
    linarith
  have hi := shiftedSkewKernel_deleted_indicator_sq_le T J
  rw [hJ] at hi
  apply h.trans
  apply div_le_div_of_nonneg_right _ hm.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  unfold gaussianScoreVariance
  have he : ((∑ i, score T i ^ 2) + n) / (n - 1 : ℝ) ^ 2 +
      (t : ℝ) ^ 2 * n / (n - 1 : ℝ) ^ 2 =
      (∑ i, score T i ^ 2) / (n - 1 : ℝ) ^ 2 +
        (n : ℝ) * (1 + (t : ℝ) ^ 2) / (n - 1 : ℝ) ^ 2 := by ring
  rw [← he]
  exact add_le_add_right hi _

theorem deletedShiftedSkewKernel_column_flat_sq_le {n t : ℕ} (T : Tournament n)
    (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t) (ht : t < n) :
    (∑ j, ((deletedShiftedSkewKernel T I J).transpose *ᵥ flatUnitVector (Iᶜ : Finset (Fin n))) j ^ 2) ≤
      2 * (gaussianScoreVariance T + (n : ℝ) * (1 + (t : ℝ) ^ 2) / (n - 1 : ℝ) ^ 2) /
        (n - t : ℝ) := by
  have hcard : (Iᶜ : Finset (Fin n)).card = n - t := by
    rw [Finset.card_compl, Fintype.card_fin, hI]
  have h := retained_flat_action_sq_le (shiftedSkewKernel T).transpose J I (by rw [hcard]; omega)
  have heq : (shiftedSkewKernel T).transpose.submatrix
      (fun j : (Jᶜ : Finset (Fin n)) => j.val) (fun i : (Iᶜ : Finset (Fin n)) => i.val) =
      (deletedShiftedSkewKernel T I J).transpose := by ext i j; rfl
  rw [heq] at h
  simp only [Matrix.transpose_apply] at h
  rw [shiftedSkewKernel_column_sum_sq, hcard, Nat.cast_sub ht.le] at h
  have hm : 0 < (n - t : ℝ) := by
    have htR : (t : ℝ) < n := by exact_mod_cast ht
    linarith
  have hi := shiftedSkewKernel_transpose_deleted_indicator_sq_le T I
  rw [hI] at hi
  apply h.trans
  apply div_le_div_of_nonneg_right _ hm.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  unfold gaussianScoreVariance
  have he : ((∑ i, score T i ^ 2) + n) / (n - 1 : ℝ) ^ 2 +
      (t : ℝ) ^ 2 * n / (n - 1 : ℝ) ^ 2 =
      (∑ i, score T i ^ 2) / (n - 1 : ℝ) ^ 2 +
        (n : ℝ) * (1 + (t : ℝ) ^ 2) / (n - 1 : ℝ) ^ 2 := by ring
  rw [← he]
  simpa only [Matrix.transpose_apply] using add_le_add_right hi _

theorem shiftedSkewKernel_deletion_centering_bound {n t : ℕ} (T : Tournament n)
    (hn : 4 ≤ n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t)
    (ht : t < n) :
    0 ≤ Real.log (gramGaussian (shiftedSkewKernel T)) -
      Real.log (gramGaussian (centeredDeletedSkewKernel T I J)) ∧
    Real.log (gramGaussian (shiftedSkewKernel T)) -
      Real.log (gramGaussian (centeredDeletedSkewKernel T I J)) ≤
      ((t : ℝ) * n / (n - 1 : ℝ) ^ 2 +
        2 * (gaussianScoreVariance T + (n : ℝ) * (1 + (t : ℝ) ^ 2) / (n - 1 : ℝ) ^ 2) /
          (n - t : ℝ)) / (1 - shiftedSkewNormBudget n) := by
  let q := Real.sqrt (shiftedSkewNormBudget n)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hqSq : q ^ 2 = shiftedSkewNormBudget n := Real.sq_sqrt (shiftedSkewNormBudget_nonneg n)
  have hq1 : q < 1 := by nlinarith [shiftedSkewNormBudget_lt_one n hn]
  have hY : ‖shiftedSkewKernel T‖ ≤ q := shiftedSkewKernel_opNorm_le T (by omega)
  have hg : 0 < 1 - shiftedSkewNormBudget n := sub_pos.mpr (shiftedSkewNormBudget_lt_one n hn)
  have hcardI : (Iᶜ : Finset (Fin n)).card = n - t := by
    rw [Finset.card_compl, Fintype.card_fin, hI]
  have hcardJ : (Jᶜ : Finset (Fin n)).card = n - t := by
    rw [Finset.card_compl, Fintype.card_fin, hJ]
  have hm : 0 < (n - t : ℝ) := by
    have htR : (t : ℝ) < n := by exact_mod_cast ht
    linarith
  have hd := gramGaussian_deletion_bound (shiftedSkewKernel T) Iᶜ Jᶜ q hq hq1 hY
  change 0 ≤ Real.log (gramGaussian (shiftedSkewKernel T)) -
    Real.log (gramGaussian (deletedShiftedSkewKernel T I J)) ∧ _ at hd
  simp only [compl_compl, shiftedSkewKernel_row_sq, shiftedSkewKernel_column_sq,
    Finset.sum_const, Finset.card_univ, Fintype.card_coe, hI, hJ, nsmul_eq_mul, hqSq] at hd
  have hW : ‖deletedShiftedSkewKernel T I J‖ ≤ q :=
    (submatrix_opNorm_le _ Iᶜ Jᶜ).trans hY
  have hc := gramGaussian_centering_bound (deletedShiftedSkewKernel T I J)
    (by rw [Fintype.card_coe, hcardI]; omega) (by rw [Fintype.card_coe, hcardJ]; omega)
    q hq hq1 hW
  change 0 ≤ Real.log (gramGaussian (deletedShiftedSkewKernel T I J)) -
    Real.log (gramGaussian (centeredDeletedSkewKernel T I J)) ∧ _ at hc
  rw [hqSq] at hc
  have hr := deletedShiftedSkewKernel_row_flat_sq_le T I J hI hJ ht
  have hcol := deletedShiftedSkewKernel_column_flat_sq_le T I J hI hJ ht
  have hs := div_le_div_of_nonneg_right (add_le_add hcol hr)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg.le)
  have hcenter := hc.2.trans hs
  have he : (t : ℝ) * ((n : ℝ) / (n - 1 : ℝ) ^ 2) +
      t * ((n : ℝ) / (n - 1 : ℝ) ^ 2) = 2 * ((t : ℝ) * n / (n - 1 : ℝ) ^ 2) := by ring
  rw [he] at hd
  dsimp only [centeredDeletedSkewKernel, deletedShiftedSkewKernel] at *
  constructor
  · linarith [hd.1, hc.1]
  · have heq :
        (2 * ((t : ℝ) * n / (n - 1 : ℝ) ^ 2)) / (2 * (1 - shiftedSkewNormBudget n)) +
          (2 * (gaussianScoreVariance T + (n : ℝ) * (1 + (t : ℝ) ^ 2) / (n - 1 : ℝ) ^ 2) /
              (n - t : ℝ) +
            2 * (gaussianScoreVariance T + (n : ℝ) * (1 + (t : ℝ) ^ 2) / (n - 1 : ℝ) ^ 2) /
              (n - t : ℝ)) / (2 * (1 - shiftedSkewNormBudget n)) =
          ((t : ℝ) * n / (n - 1 : ℝ) ^ 2 +
            2 * (gaussianScoreVariance T + (n : ℝ) * (1 + (t : ℝ) ^ 2) / (n - 1 : ℝ) ^ 2) /
              (n - t : ℝ)) / (1 - shiftedSkewNormBudget n) := by
        field_simp; ring
    rw [← heq]
    linarith [hd.2]

theorem finite_gaussian_deletion_constant (N t tau : ℝ) (hN : 4 ≤ N)
    (ht0 : 0 ≤ t) (ht : t ≤ N / 2) (htau : 0 ≤ tau) :
    2 * t / (N - 3) + 4 * (N - 1) ^ 2 * tau / ((N - t) * N * (N - 3)) +
        4 * (1 + t ^ 2) / ((N - t) * (N - 3)) ≤ (24 * t + 18 * tau + 8) / N := by
  have hN0 : 0 < N := by linarith
  have hN3 : 0 < N - 3 := by linarith
  have hm : 0 < N - t := by linarith
  have hd : 2 * t / (N - 3) ≤ 8 * t / N := by
    apply (div_le_div_iff₀ hN3 hN0).mpr
    have h := mul_nonneg ht0 (show 0 ≤ N - 4 by linarith)
    nlinarith
  have hc : 4 * (N - 1) ^ 2 / ((N - t) * N * (N - 3)) ≤ 18 / N := by
    apply (div_le_iff₀ (by positivity : 0 < (N - t) * N * (N - 3))).mpr
    have he : 18 / N * ((N - t) * N * (N - 3)) = 18 * (N - t) * (N - 3) := by
      field_simp
    rw [he]
    have hp : 4 * (N - 1) ^ 2 ≤ 9 * N * (N - 3) := by
      nlinarith [mul_nonneg (show 0 ≤ N - 4 by linarith) (show 0 ≤ 5 * N + 1 by linarith)]
    have hml := mul_le_mul_of_nonneg_right (show N / 2 ≤ N - t by linarith) hN3.le
    nlinarith
  have hc' : 4 * (N - 1) ^ 2 * tau / ((N - t) * N * (N - 3)) ≤ 18 * tau / N := by
    convert mul_le_mul_of_nonneg_right hc htau using 1 <;> ring
  have hconst : 4 * (1 + t ^ 2) / ((N - t) * (N - 3)) ≤ (16 * t + 8) / N := by
    apply (div_le_div_iff₀ (by positivity : 0 < (N - t) * (N - 3)) hN0).mpr
    have hsq : t ^ 2 ≤ N * t / 2 := by nlinarith [mul_nonneg ht0 (show 0 ≤ N / 2 - t by linarith)]
    have hp : 1 + t ^ 2 ≤ (2 * t + 1) * (N - 3) := by
      nlinarith [mul_nonneg ht0 (show 0 ≤ N - 4 by linarith)]
    have hp' := mul_le_mul_of_nonneg_right hp hN0.le
    have hml := mul_le_mul_of_nonneg_right (show N / 2 ≤ N - t by linarith)
      (show 0 ≤ (16 * t + 8) * (N - 3) by positivity)
    nlinarith
  have he : 8 * t / N + 18 * tau / N + (16 * t + 8) / N =
      (24 * t + 18 * tau + 8) / N := by ring
  rw [← he]
  exact add_le_add (add_le_add hd hc') hconst

theorem shiftedSkewKernel_deletion_centering_finite_bound {n t : ℕ} (T : Tournament n)
    (hn : 4 ≤ n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t)
    (ht : 2 * t ≤ n) :
    0 ≤ Real.log (gramGaussian (shiftedSkewKernel T)) -
      Real.log (gramGaussian (centeredDeletedSkewKernel T I J)) ∧
    Real.log (gramGaussian (shiftedSkewKernel T)) -
      Real.log (gramGaussian (centeredDeletedSkewKernel T I J)) ≤
      (24 * (t : ℝ) + 18 * scoreVariance T + 8) / n := by
  have ht' : t < n := by omega
  have h := shiftedSkewKernel_deletion_centering_bound T hn I J hI hJ ht'
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have htR : (t : ℝ) ≤ n / 2 := by
    have h : 2 * (t : ℝ) ≤ n := by exact_mod_cast ht
    linarith
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn3 : (n : ℝ) - 3 ≠ 0 := by linarith
  have hnt : (n - t : ℝ) ≠ 0 := by linarith
  have heq : gaussianScoreVariance T = scoreVariance T := (scoreVariance_eq_score_sq T).symm
  rw [heq] at h
  refine ⟨h.1, h.2.trans ?_⟩
  rw [shiftedSkewNormBudget_gap n (by omega)]
  have he :
      ((t : ℝ) * n / (n - 1 : ℝ) ^ 2 +
        2 * (scoreVariance T + (n : ℝ) * (1 + (t : ℝ) ^ 2) / (n - 1 : ℝ) ^ 2) /
          (n - t : ℝ)) / ((n : ℝ) * (n - 3) / (2 * (n - 1 : ℝ) ^ 2)) =
        2 * (t : ℝ) / (n - 3 : ℝ) +
          4 * (n - 1 : ℝ) ^ 2 * scoreVariance T / ((n - t : ℝ) * n * (n - 3)) +
          4 * (1 + (t : ℝ) ^ 2) / ((n - t : ℝ) * (n - 3)) := by
    field_simp [hn0, hn1, hn3, hnt]; ring
  rw [he]
  exact finite_gaussian_deletion_constant n t (scoreVariance T) hnR (Nat.cast_nonneg _) htR
    (scoreVariance_nonneg T)

theorem finite_gaussian_full_gram_constant (N : ℝ) (hN : 4 ≤ N) :
    ((2 * N - 1) / (N * (N - 1)) + N / (N - 1) ^ 2) /
      (2 * (N * (N - 3) / (2 * (N - 1) ^ 2))) ≤ 43 / (4 * N) := by
  have hN0 : 0 < N := by linarith
  have hN1 : N - 1 ≠ 0 := by linarith
  have hN3 : 0 < N - 3 := by linarith
  have he : ((2 * N - 1) / (N * (N - 1)) + N / (N - 1) ^ 2) /
      (2 * (N * (N - 3) / (2 * (N - 1) ^ 2))) =
      (3 * N ^ 2 - 3 * N + 1) / (N ^ 2 * (N - 3)) := by
    field_simp [hN0.ne', hN1, hN3.ne']; ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity : 0 < N ^ 2 * (N - 3))
    (by positivity : 0 < 4 * N)).mpr
  have hp : 4 * (3 * N ^ 2 - 3 * N + 1) ≤ 43 * N * (N - 3) := by
    nlinarith [mul_nonneg (show 0 ≤ N - 4 by linarith) (show 0 ≤ 31 * N + 7 by linarith)]
  have h := mul_le_mul_of_nonneg_right hp hN0.le
  nlinarith

theorem shiftedSkewKernel_full_gram_loss {n : ℕ} (T : Tournament n) (hn : 4 ≤ n) :
    0 ≤ Real.log (gramGaussian (shiftedSkewKernel T)) - Real.log (gaussianFactor T) ∧
    Real.log (gramGaussian (shiftedSkewKernel T)) - Real.log (gaussianFactor T) ≤
      43 / (4 * (n : ℝ)) := by
  let A := (1 : Matrix (Fin n) (Fin n) ℝ) -
    (shiftedSkewKernel T).transpose * shiftedSkewKernel T
  let D := (shiftedSkewKernel T).transpose * shiftedSkewKernel T -
    ((1 : ℝ) / (n : ℝ) ^ 2) • ((signMatrix T).transpose * signMatrix T)
  let q := Real.sqrt (shiftedSkewNormBudget n)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hqSq : q ^ 2 = shiftedSkewNormBudget n := Real.sq_sqrt (shiftedSkewNormBudget_nonneg n)
  have hq1 : q < 1 := by nlinarith [shiftedSkewNormBudget_lt_one n hn]
  have hY : ‖shiftedSkewKernel T‖ ≤ q := shiftedSkewKernel_opNorm_le T (by omega)
  have hA : A.PosDef := gram_complement_posDef _ q hq hq1 hY
  have hD : D.PosSemidef := shiftedSkewKernel_gram_difference_posSemidef T (by omega)
  have hg : 0 < 1 - shiftedSkewNormBudget n := sub_pos.mpr (shiftedSkewNormBudget_lt_one n hn)
  have hbound : ∀ x : Fin n → ℝ, (1 - shiftedSkewNormBudget n) * (∑ i, x i ^ 2) ≤
      dotProduct x (A *ᵥ x) := by
    intro x
    simpa only [hqSq] using gram_complement_quadratic_lower (shiftedSkewKernel T) q hq hY x
  have h := posDef_logdet_increment_bound A D hA hD (1 - shiftedSkewNormBudget n) hg hbound
  have he : A + D = skewGram T := by
    dsimp [A, D, skewGram]
    abel
  rw [he] at h
  have hlog : Real.log (gramGaussian (shiftedSkewKernel T)) - Real.log (gaussianFactor T) =
      (Real.log (skewGram T).det - Real.log A.det) / 2 := by
    rw [gramGaussian_log _ hA.det_pos, gaussianFactor, Real.log_inv,
      Real.log_sqrt (skewGram_det_pos T (by omega)).le]
    dsimp [A]
    ring
  rw [hlog]
  refine ⟨div_nonneg h.1 (by norm_num), ?_⟩
  have hhalf := div_le_div_of_nonneg_right h.2 (by norm_num : (0 : ℝ) ≤ 2)
  have htrace := shiftedSkewKernel_gram_difference_trace T (by omega)
  change D.trace = _ at htrace
  rw [htrace, div_div, mul_comm (1 - shiftedSkewNormBudget n),
    shiftedSkewNormBudget_gap n (by omega)] at hhalf
  exact hhalf.trans (finite_gaussian_full_gram_constant n (by exact_mod_cast hn))

/-- The manuscript's finite Gaussian deletion comparison, for independently
chosen row and column deletion sets of equal size. -/
theorem tournament_gaussian_deletion_loss {n t : ℕ} (T : Tournament n)
    (hn : 4 ≤ n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t)
    (ht : 2 * t ≤ n) :
    |Real.log (gramGaussian (centeredDeletedSkewKernel T I J)) -
      Real.log (gaussianFactor T)| ≤ (24 * (t : ℝ) + 18 * scoreVariance T + 11) / n := by
  have hdel := shiftedSkewKernel_deletion_centering_finite_bound T hn I J hI hJ ht
  have hfull := shiftedSkewKernel_full_gram_loss T hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have htR : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  have htau := scoreVariance_nonneg T
  have hdel' : (24 * (t : ℝ) + 18 * scoreVariance T + 8) / n ≤
      (24 * (t : ℝ) + 18 * scoreVariance T + 11) / n :=
    div_le_div_of_nonneg_right (by linarith) hnR.le
  have hfull' : 43 / (4 * (n : ℝ)) ≤
      (24 * (t : ℝ) + 18 * scoreVariance T + 11) / n := by
    rw [div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hnR.le
  apply abs_le.mpr
  constructor
  · have h := hdel.2.trans hdel'
    linarith [hfull.1]
  · have h := hfull.2.trans hfull'
    linarith [hdel.1]

end TournamentHamiltonian
