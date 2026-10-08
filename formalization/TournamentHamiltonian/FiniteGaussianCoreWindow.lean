import TournamentHamiltonian.GaussianCoreExcessCoefficients
import TournamentHamiltonian.GaussianSeries
import TournamentHamiltonian.FiniteExcessWindow
import Mathlib.Algebra.BigOperators.NatAntidiagonal

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

theorem finite_nonnegative_convolution_sum_le (M : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k) :
    (∑ k ∈ Finset.range (M + 1), ∑ l ∈ Finset.range (k + 1), f l * g (k - l)) ≤
      (∑ l ∈ Finset.range (M + 1), f l) * ∑ r ∈ Finset.range (M + 1), g r := by
  let rect := (Finset.range (M + 1)).product (Finset.range (M + 1))
  let tri := rect.filter (fun p => p.1 + p.2 ≤ M)
  have hmap : ∀ p ∈ tri, p.1 + p.2 ∈ Finset.range (M + 1) := by
    intro p hp
    have h := (Finset.mem_filter.mp hp).2
    exact Finset.mem_range.mpr (by omega)
  have hfiber (k : ℕ) (hk : k ∈ Finset.range (M + 1)) :
      tri.filter (fun p => p.1 + p.2 = k) = Finset.antidiagonal k := by
    have hkM := Finset.mem_range.mp hk
    ext p
    constructor
    · intro hp
      exact Finset.mem_antidiagonal.mpr (Finset.mem_filter.mp hp).2
    · intro hp
      have hpk := Finset.mem_antidiagonal.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_, by omega⟩, hpk⟩
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hsum := Finset.sum_fiberwise_of_maps_to hmap (fun p => f p.1 * g p.2)
  have heq : (∑ k ∈ Finset.range (M + 1), ∑ l ∈ Finset.range (k + 1), f l * g (k - l)) =
      ∑ p ∈ tri, f p.1 * g p.2 := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hfiber k hk]
    exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun p => f p.1 * g p.2) k).symm
  rw [heq]
  calc
    _ ≤ ∑ p ∈ rect, f p.1 * g p.2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p _ _ => mul_nonneg (hf p.1) (hg p.2))
    _ = _ := by dsimp [rect]; rw [Finset.sum_product, Finset.sum_mul]; simp_rw [Finset.mul_sum]

attribute [local instance] Classical.propDecidable Classical.decEq

variable {ι : Type*} [Fintype ι]

noncomputable def coreExcessAbsCoefficient (B : Matrix ι ι ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 k, |actualCoreExcessCoefficient B j k|

theorem actual_coefficient_core_error_le (B : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, B i j = 0) (hcol : ∀ j, ∑ i, B i j = 0) (k : ℕ) :
    |distinctCoordinateSum B k / (k.factorial : ℝ) - bilinearGaussianCoefficient B k| ≤
      ∑ l ∈ Finset.range (k + 1), bilinearGaussianCoefficient B l * coreExcessAbsCoefficient B (k - l) := by
  rw [distinctCoordinateSum_div_gaussian_excess_convolution B hrow hcol k, add_sub_cancel_left]
  calc
    _ ≤ ∑ l ∈ Finset.range (k + 1), |bilinearGaussianCoefficient B l *
        ∑ j ∈ Finset.Ico 1 (k - l), actualCoreExcessCoefficient B j (k - l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul, abs_of_nonneg (bilinearGaussianCoefficient_nonneg B l)]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (bilinearGaussianCoefficient_nonneg B l)

theorem actual_coefficient_core_error_weighted_le (B : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, B i j = 0) (hcol : ∀ j, ∑ i, B i j = 0)
    (R : ℝ) (hR : 0 ≤ R) (k : ℕ) :
    |distinctCoordinateSum B k / (k.factorial : ℝ) - bilinearGaussianCoefficient B k| * R ^ k ≤
      ∑ l ∈ Finset.range (k + 1),
        (bilinearGaussianCoefficient B l * R ^ l) *
          (coreExcessAbsCoefficient B (k - l) * R ^ (k - l)) := by
  have h := mul_le_mul_of_nonneg_right (actual_coefficient_core_error_le B hrow hcol k)
    (pow_nonneg hR k)
  apply h.trans_eq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have heq : l + (k - l) = k := by have h := Finset.mem_range.mp hl; omega
  have hpow : R ^ k = R ^ l * R ^ (k - l) := by rw [← pow_add, heq]
  rw [hpow]
  ring

theorem actual_finite_gaussian_core_error_le (B : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, B i j = 0) (hcol : ∀ j, ∑ i, B i j = 0)
    (M : ℕ) (R K : ℝ) (hR : 0 ≤ R) (hgap : R * ‖B‖ < 1)
    (hcore : (∑ k ∈ Finset.range (M + 1), coreExcessAbsCoefficient B k * R ^ k) ≤ K) :
    (∑ k ∈ Finset.range (M + 1),
      |distinctCoordinateSum B k / (k.factorial : ℝ) - bilinearGaussianCoefficient B k| * R ^ k) ≤
        gramGaussian (R • B) * K := by
  have hf (k : ℕ) : 0 ≤ bilinearGaussianCoefficient B k * R ^ k :=
    mul_nonneg (bilinearGaussianCoefficient_nonneg B k) (pow_nonneg hR k)
  have hg (k : ℕ) : 0 ≤ coreExcessAbsCoefficient B k * R ^ k := by
    unfold coreExcessAbsCoefficient
    positivity
  have hsum := Finset.sum_le_sum (s := Finset.range (M + 1)) (fun k _ =>
    actual_coefficient_core_error_weighted_le B hrow hcol R hR k)
  have hconv := finite_nonnegative_convolution_sum_le M
    (fun k => bilinearGaussianCoefficient B k * R ^ k)
      (fun k => coreExcessAbsCoefficient B k * R ^ k) hf hg
  have hG := bilinearGaussianCoefficient_finite_sum_le B R hR hgap (Finset.range (M + 1))
  have hG0 : 0 ≤ gramGaussian (R • B) :=
    (Finset.sum_nonneg (fun k _ => hf k)).trans hG
  have hmul := mul_le_mul hG hcore (Finset.sum_nonneg (fun k _ => hg k)) hG0
  exact hsum.trans (hconv.trans hmul)

theorem coreExcessAbs_window_le_sum_excess_windows (B : Matrix ι ι ℝ)
    (M : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (∑ k ∈ Finset.range (M + 1), coreExcessAbsCoefficient B k * R ^ k) ≤
      ∑ j ∈ Finset.Icc 1 M, ∑ k ∈ Finset.range (M + 1), |actualCoreExcessCoefficient B j k| * R ^ k := by
  calc
    _ ≤ ∑ k ∈ Finset.range (M + 1), ∑ j ∈ Finset.Icc 1 M,
        |actualCoreExcessCoefficient B j k| * R ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [coreExcessAbsCoefficient, Finset.sum_mul]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        have hkM := Finset.mem_range.mp hk
        simp only [Finset.mem_Ico, Finset.mem_Icc] at hj ⊢
        omega
      · intro j _ _; positivity
    _ = _ := Finset.sum_comm

theorem actual_core_finite_excess_window_le (B : Matrix ι ι ℝ)
    (n M : ℕ) (D T1 R : ℝ) (hn : 0 < n) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hM : 16 * D * (M : ℝ) ≤ n)
    (hfirst : (∑ k ∈ Finset.range (M + 1), |actualCoreExcessCoefficient B 1 k| * R ^ k) ≤ T1 / n)
    (hexcess : ∀ j ∈ Finset.Icc 2 M,
      (∑ k ∈ Finset.range (M + 1), |actualCoreExcessCoefficient B j k| * R ^ k) ≤ excessWindowTerm D n j) :
    (∑ k ∈ Finset.range (M + 1), coreExcessAbsCoefficient B k * R ^ k) ≤
      T1 / n + 8 * D ^ 2 / (n : ℝ) ^ 2 := by
  have hsub : Finset.Icc 1 M ⊆ insert 1 (Finset.Icc 2 M) := by
    intro j hj
    simp only [Finset.mem_Icc, Finset.mem_insert] at hj ⊢
    omega
  have hnonneg (j : ℕ) : 0 ≤ ∑ k ∈ Finset.range (M + 1),
      |actualCoreExcessCoefficient B j k| * R ^ k := by positivity
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hnonneg j)
  rw [Finset.sum_insert (by norm_num : 1 ∉ Finset.Icc 2 M)] at h
  have htail := (Finset.sum_le_sum hexcess).trans (finite_excess_window_tail_le D n M hn hD hM)
  exact (coreExcessAbs_window_le_sum_excess_windows B M R hR).trans
    (h.trans (add_le_add hfirst htail))

theorem actual_gaussian_finite_window_error_le (B : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, B i j = 0) (hcol : ∀ j, ∑ i, B i j = 0)
    (n M : ℕ) (D T1 R : ℝ) (hn : 0 < n) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hgap : R * ‖B‖ < 1) (hM : 16 * D * (M : ℝ) ≤ n)
    (hfirst : (∑ k ∈ Finset.range (M + 1), |actualCoreExcessCoefficient B 1 k| * R ^ k) ≤ T1 / n)
    (hexcess : ∀ j ∈ Finset.Icc 2 M,
      (∑ k ∈ Finset.range (M + 1), |actualCoreExcessCoefficient B j k| * R ^ k) ≤ excessWindowTerm D n j) :
    (∑ k ∈ Finset.range (M + 1),
      |distinctCoordinateSum B k / (k.factorial : ℝ) - bilinearGaussianCoefficient B k| * R ^ k) ≤
        gramGaussian (R • B) * (T1 / n + 8 * D ^ 2 / (n : ℝ) ^ 2) :=
  actual_finite_gaussian_core_error_le B hrow hcol M R _ hR hgap
    (actual_core_finite_excess_window_le B n M D T1 R hn hD hR hM hfirst hexcess)

end TournamentHamiltonian
