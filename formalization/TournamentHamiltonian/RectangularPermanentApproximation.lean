import TournamentHamiltonian.CoreActivityPredicate
import TournamentHamiltonian.PermanentApproximationConstant
import TournamentHamiltonian.RectangularScaling

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def rectangularPermanentKernel (Y : Matrix ι κ ℝ) (e : ι ≃ κ) : Matrix ι ι ℝ :=
  (Y - rectangularAverageMatrix ι κ).submatrix id e

theorem rectangularPermanentKernel_doublyCentered (Y : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (hrow : ∀ i, ∑ j, Y i j = 1)
    (hcol : ∀ j, ∑ i, Y i j = 1) : DoublyCentered (rectangularPermanentKernel Y e) := by
  have heq : rectangularPermanentKernel Y e = Y.submatrix id e - averagingMatrix ι := by
    rw [rectangularPermanentKernel]
    change Y.submatrix id e - (rectangularAverageMatrix ι κ).submatrix id e = _
    rw [rectangularAverageMatrix_square_reindex]
  rw [heq]
  constructor
  · intro i
    simp only [Matrix.sub_apply, Finset.sum_sub_distrib, averagingMatrix_row_sum hp]
    change (∑ j, Y i (e j)) - 1 = 0
    rw [e.sum_comp (fun j => Y i j), hrow, sub_self]
  · intro j
    simp only [Matrix.sub_apply, Finset.sum_sub_distrib, averagingMatrix_column_sum hp]
    change (∑ i, Y i (e j)) - 1 = 0
    rw [hcol, sub_self]

omit [Fintype κ] in
theorem rectangularPermanentKernel_entry_bound (Y : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K : ℝ) (hentry : ∀ i j, |Y i j| ≤ K / Fintype.card ι)
    (i j : ι) : |rectangularPermanentKernel Y e i j| ≤ (K + 1) / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  change |Y i (e j) - (Fintype.card ι : ℝ)⁻¹| ≤ _
  have h := norm_sub_le (Y i (e j)) (Fintype.card ι : ℝ)⁻¹
  simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hn] at h
  exact h.trans ((add_le_add (hentry i (e j)) le_rfl).trans_eq (by ring))

/-- The actual square reindexing of a doubly stochastic rectangular matrix,
with both its permanent and its Gaussian factor restored to original types. -/
theorem rectangularPermanent_approximation_of_activities (Y : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (hrow : ∀ i, ∑ j, Y i j = 1) (hcol : ∀ j, ∑ i, Y i j = 1)
    (hentry : ∀ i j, |Y i j| ≤ K / Fintype.card ι)
    (hgap : ‖Y - rectangularAverageMatrix ι κ‖ ≤ q)
    (hactivity : ActualCoreActivities (rectangularPermanentKernel Y e) (K + 1) q) :
    |(Fintype.card ι : ℝ) ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ) *
        rectangularPermanent Y e - gramGaussian (Y - rectangularAverageMatrix ι κ)| ≤
      uniformPermanentActivityConstant (K + 1) q / Fintype.card ι := by
  let B := rectangularPermanentKernel Y e
  let E := (Fintype.card ι : ℝ) • B
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  have hB := rectangularPermanentKernel_doublyCentered Y e hp hrow hcol
  have hnorm : (Fintype.card ι : ℝ)⁻¹ • E = B := by
    dsimp only [E]
    rw [smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
  have hEnorm : ‖(Fintype.card ι : ℝ)⁻¹ • E‖ ≤ q := by
    rw [hnorm]
    exact (matrix_l2_opNorm_submatrix_equiv _ (Equiv.refl ι) e).trans_le hgap
  have hEentry (i j : ι) : |E i j| ≤ K + 1 := by
    change |(Fintype.card ι : ℝ) * B i j| ≤ _
    rw [abs_mul, abs_of_pos hn]
    have hh := mul_le_mul_of_nonneg_left
      (rectangularPermanentKernel_entry_bound Y e hp K hentry i j) hn.le
    exact hh.trans_eq (by field_simp)
  have h := uniform_permanent_approximation_of_activity_predicate E
    (hB.real_smul _ _) hp (K + 1) q (by linarith) hq hq1 hEentry hEnorm
    (by rwa [hnorm])
  rw [hnorm] at h
  have hmat : (fun i j => 1 + E i j) = (Fintype.card ι : ℝ) • Y.submatrix id e := by
    ext i j
    change 1 + (Fintype.card ι : ℝ) * (Y i (e j) - (Fintype.card ι : ℝ)⁻¹) =
      (Fintype.card ι : ℝ) * Y i (e j)
    field_simp
    ring
  rw [hmat, Matrix.permanent_smul] at h
  have hG : gramGaussian B = gramGaussian (Y - rectangularAverageMatrix ι κ) :=
    gramGaussian_submatrix_equiv _ (Equiv.refl ι) e
  rw [hG] at h
  convert h using 1
  congr 1
  unfold rectangularPermanent
  ring

theorem gramGaussian_one_le_of_gap (B : Matrix ι κ ℝ) (hgap : ‖B‖ < 1) :
    1 ≤ gramGaussian B := by
  have h := bilinearGaussianCoefficient_finite_sum_le B 1 (by norm_num)
    (by simpa using hgap) {0}
  simpa [bilinearGaussianCoefficient, gaussianBilinearMoment,
    gaussianBilinearVariable] using h

theorem rectangularPermanent_upper_of_activities (Y : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (hrow : ∀ i, ∑ j, Y i j = 1) (hcol : ∀ j, ∑ i, Y i j = 1)
    (hentry : ∀ i j, |Y i j| ≤ K / Fintype.card ι)
    (hgap : ‖Y - rectangularAverageMatrix ι κ‖ ≤ q)
    (hactivity : ActualCoreActivities (rectangularPermanentKernel Y e) (K + 1) q) :
    rectangularPermanent Y e ≤ ((Fintype.card ι).factorial : ℝ) /
      (Fintype.card ι : ℝ) ^ Fintype.card ι * gramGaussian (Y - rectangularAverageMatrix ι κ) *
        (1 + uniformPermanentActivityConstant (K + 1) q / Fintype.card ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  have hf : (0 : ℝ) < (Fintype.card ι).factorial := by exact_mod_cast Nat.factorial_pos _
  have h := (abs_le.mp (rectangularPermanent_approximation_of_activities Y e hp K q
    hK hq hq1 hrow hcol hentry hgap hactivity)).2
  have hG := gramGaussian_one_le_of_gap (Y - rectangularAverageMatrix ι κ) (hgap.trans_lt hq1)
  have hconst : 0 ≤ uniformPermanentActivityConstant (K + 1) q / Fintype.card ι :=
    div_nonneg (uniformPermanentActivityConstant_nonneg _ q hq hq1) hn.le
  have hb : (Fintype.card ι : ℝ) ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ) *
      rectangularPermanent Y e ≤ gramGaussian (Y - rectangularAverageMatrix ι κ) *
        (1 + uniformPermanentActivityConstant (K + 1) q / Fintype.card ι) := by
    nlinarith [mul_le_mul_of_nonneg_right hG hconst]
  have hratio : 0 < (Fintype.card ι : ℝ) ^ Fintype.card ι /
      ((Fintype.card ι).factorial : ℝ) := div_pos (pow_pos hn _) hf
  have hb' : rectangularPermanent Y e ≤
      (gramGaussian (Y - rectangularAverageMatrix ι κ) *
        (1 + uniformPermanentActivityConstant (K + 1) q / Fintype.card ι)) /
          ((Fintype.card ι : ℝ) ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ)) :=
    (le_div_iff₀ hratio).mpr (by simpa only [mul_comm] using hb)
  exact hb'.trans_eq (by field_simp)

end TournamentHamiltonian
