import TournamentHamiltonian.TransitiveDeterminant
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open Filter Asymptotics
open scoped Topology

namespace TournamentHamiltonian

private theorem complex_inv_nat_tendsto :
    Tendsto (fun n : ℕ => (1 : ℂ) / n) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, one_div, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_zero] using
    (tendsto_inv_atTop_zero.comp hn).ofReal

private theorem complex_div_nat_tendsto (t : ℂ) :
    Tendsto (fun n : ℕ => t / n) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using complex_inv_nat_tendsto.const_mul t

/-- The logarithmic error behind the all-order exponential approximation. -/
theorem nat_log_one_add_error_isBigO (t : ℂ) :
    (fun n : ℕ => (n : ℂ) * Complex.log (1 + t / n) - t) =O[atTop]
      (fun n : ℕ => (1 : ℂ) / n) := by
  have hlog := Complex.log_sub_self_isBigO.comp_tendsto (complex_div_nat_tendsto t)
  have h := (isBigO_refl (fun n : ℕ => (n : ℂ)) atTop).mul hlog
  have heqL : (fun n : ℕ => (n : ℂ) * ((Complex.log (1 + t / n)) - t / n)) =ᶠ[atTop]
      (fun n : ℕ => (n : ℂ) * Complex.log (1 + t / n) - t) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  have heqR : (fun n : ℕ => (n : ℂ) * (t / n) ^ 2) =ᶠ[atTop]
      (fun n : ℕ => t ^ 2 * ((1 : ℂ) / n)) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  have h' := h.congr' heqL heqR
  exact h'.trans ((isBigO_refl (fun n : ℕ => (1 : ℂ) / n) atTop).const_mul_left (t ^ 2))

/-- The O(1/n) estimate for a fixed complex parameter, including the
imaginary parameters used in the carousel denominator. -/
theorem one_add_div_pow_error_isBigO (t : ℂ) :
    (fun n : ℕ => (1 + t / n) ^ n - Complex.exp t) =O[atTop]
      (fun n : ℕ => (1 : ℂ) / n) := by
  have hlog := nat_log_one_add_error_isBigO t
  have hU : Tendsto (fun n : ℕ => (n : ℂ) * Complex.log (1 + t / n)) atTop (𝓝 t) :=
    tendsto_sub_nhds_zero_iff.mp (hlog.trans_tendsto complex_inv_nat_tendsto)
  have hexp := ((Complex.hasDerivAt_exp t).isBigO_sub.comp_tendsto hU).trans hlog
  apply hexp.congr' ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [(complex_div_nat_tendsto t).eventually_ne
    (show (0 : ℂ) ≠ -1 by norm_num)] with n hn
  have hnz : 1 + t / (n : ℂ) ≠ 0 := by
    intro h
    apply hn
    linear_combination h
  simp only [Function.comp_def]
  rw [Complex.exp_nat_mul, Complex.exp_log hnz]

noncomputable def binomialMean (t : ℂ) (n : ℕ) : ℂ :=
  ((1 + t / n) ^ n + (1 - t / n) ^ n) / 2

theorem binomialMean_error_isBigO (t : ℂ) :
    (fun n => binomialMean t n - Complex.cosh t) =O[atTop]
      (fun n : ℕ => (1 : ℂ) / n) := by
  have h := ((one_add_div_pow_error_isBigO t).add (one_add_div_pow_error_isBigO (-t))).const_mul_left
    ((2 : ℂ)⁻¹)
  convert h using 1
  funext n
  simp only [binomialMean, Complex.cosh, neg_div]
  ring

theorem transitiveKernel_div_det (t : ℂ) (n : ℕ) :
    (transitiveKernel n (t / n)).det = binomialMean t n := transitiveKernel_det n (t / n)

noncomputable def transitiveRatio (n : ℕ) : ℂ :=
  (transitiveKernel n ((1 : ℂ) / n)).det / (transitiveKernel n (Complex.I / n)).det

theorem transitiveRatio_eq_binomialMean (n : ℕ) :
    transitiveRatio n = binomialMean 1 n / binomialMean Complex.I n := by
  rw [transitiveRatio, transitiveKernel_div_det, transitiveKernel_div_det]

theorem cos_one_pos : 0 < Real.cos 1 := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_gt_three]

private theorem complex_cosh_I : Complex.cosh Complex.I = Complex.cos 1 := by
  simpa only [one_mul] using Complex.cosh_mul_I (1 : ℂ)

theorem cos_one_complex_ne_zero : Complex.cos (1 : ℂ) ≠ 0 := by
  have heq : (Real.cos 1 : ℂ) = Complex.cos 1 := by
    simpa only [Complex.ofReal_one] using Complex.ofReal_cos (1 : ℝ)
  rw [← heq]
  exact_mod_cast cos_one_pos.ne'

theorem binomialMean_I_tendsto :
    Tendsto (binomialMean Complex.I) atTop (𝓝 (Complex.cos 1)) := by
  have hG := binomialMean_error_isBigO Complex.I
  rw [complex_cosh_I] at hG
  exact tendsto_sub_nhds_zero_iff.mp (hG.trans_tendsto complex_inv_nat_tendsto)

theorem transitiveKernel_imaginary_det_eventually_ne_zero :
    ∀ᶠ n : ℕ in atTop, (transitiveKernel n (Complex.I / n)).det ≠ 0 := by
  simpa only [transitiveKernel_div_det] using
    binomialMean_I_tendsto.eventually_ne cos_one_complex_ne_zero

/-- The exact transitive determinant ratio has the claimed O(1/n) error.
This does not yet identify the ratio with actual carousel path counts. -/
theorem transitiveRatio_error_isBigO :
    (fun n => transitiveRatio n - (lowerConstant : ℂ)) =O[atTop]
      (fun n : ℕ => (1 : ℂ) / n) := by
  have hF := binomialMean_error_isBigO 1
  have hG := binomialMean_error_isBigO Complex.I
  rw [complex_cosh_I] at hG
  have hc := cos_one_complex_ne_zero
  have hGl : Tendsto (binomialMean Complex.I) atTop (𝓝 (Complex.cos 1)) :=
    tendsto_sub_nhds_zero_iff.mp (hG.trans_tendsto complex_inv_nat_tendsto)
  have hi := isBigO_const_of_tendsto (hGl.inv₀ hc) (one_ne_zero (α := ℂ))
  have hnum := hF.sub (hG.const_mul_left (Complex.cosh 1 / Complex.cos 1))
  have h := hnum.mul hi
  simp only [mul_one] at h
  have hL : Complex.cosh (1 : ℂ) / Complex.cos 1 = (lowerConstant : ℂ) := by
    simp only [lowerConstant, Complex.ofReal_div, Complex.ofReal_cosh, Complex.ofReal_cos,
      Complex.ofReal_one]
  apply h.congr' ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [hGl.eventually_ne hc] with n hn
  rw [transitiveRatio_eq_binomialMean, ← hL]
  field_simp
  ring

theorem transitiveRatio_tendsto :
    Tendsto transitiveRatio atTop (𝓝 (lowerConstant : ℂ)) :=
  tendsto_sub_nhds_zero_iff.mp (transitiveRatio_error_isBigO.trans_tendsto complex_inv_nat_tendsto)

/-- Explicit uniform quantifiers for the asymptotic determinant-ratio estimate. -/
theorem transitiveRatio_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ‖transitiveRatio n - (lowerConstant : ℂ)‖ ≤ C / n := by
  obtain ⟨C, hC, hO⟩ := transitiveRatio_error_isBigO.exists_nonneg
  obtain ⟨N, hN⟩ := eventually_atTop.mp hO.bound
  refine ⟨C, hC, max N 1, le_max_right _ _, ?_⟩
  intro n hn
  simpa only [Complex.norm_div, norm_one, Complex.norm_natCast, mul_one_div] using
    hN n ((le_max_left N 1).trans hn)

end TournamentHamiltonian
