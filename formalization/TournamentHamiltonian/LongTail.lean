import TournamentHamiltonian.SubsetWeights
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology Asymptotics

namespace TournamentHamiltonian

noncomputable def rawSubsetCutoff (x : ℝ) : ℝ := 4 * Real.log x / Real.log (Real.log x)

noncomputable def subsetCutoffAt (x : ℝ) : ℕ := ⌈rawSubsetCutoff x⌉₊

noncomputable def subsetCutoff (n : ℕ) : ℕ := subsetCutoffAt n

theorem rawSubsetCutoff_tendsto : Tendsto rawSubsetCutoff atTop atTop := by
  have hl := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have h := ((Real.tendsto_exp_div_pow_atTop 1).const_mul_atTop
    (by norm_num : (0 : ℝ) < 4)).comp hl
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with x hx
  simp [rawSubsetCutoff, Real.exp_log hx, pow_one, mul_div_assoc]

theorem subsetCutoffAt_tendsto : Tendsto subsetCutoffAt atTop atTop :=
  tendsto_nat_ceil_atTop.comp rawSubsetCutoff_tendsto

theorem cutoff_rounding_ratio_tendsto :
    Tendsto (fun x => (subsetCutoffAt x : ℝ) / rawSubsetCutoff x) atTop (𝓝 1) :=
  tendsto_nat_ceil_div_atTop.comp rawSubsetCutoff_tendsto

theorem cutoff_log_ratio_tendsto :
    Tendsto (fun x => Real.log (subsetCutoffAt x : ℝ) / Real.log (Real.log x))
      atTop (𝓝 1) := by
  have hl := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hr : Tendsto (fun x => Real.log ((subsetCutoffAt x : ℝ) / rawSubsetCutoff x))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp cutoff_rounding_ratio_tendsto
  have hsmall : Tendsto (fun x => Real.log (Real.log (Real.log x)) / Real.log (Real.log x))
      atTop (𝓝 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hl
  have hterm := (hr.add (tendsto_const_nhds (x := Real.log 4))).div_atTop hl
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add hterm |>.sub hsmall
  simp only [add_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ),
    subsetCutoffAt_tendsto.eventually_ge_atTop 1] with x hx hN
  have hll : 0 < Real.log (Real.log x) := Real.log_pos hx
  have hraw : 0 < rawSubsetCutoff x := by unfold rawSubsetCutoff; positivity
  have hNr : (0 : ℝ) < subsetCutoffAt x := Nat.cast_pos.mpr (by omega)
  simp only [Function.comp_def]
  rw [Real.log_div hNr.ne' hraw.ne']
  simp only [rawSubsetCutoff,
    Real.log_div (by positivity : (4 * Real.log x) ≠ 0) hll.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : Real.log x ≠ 0)]
  field_simp
  ring

theorem cutoff_div_log_tendsto :
    Tendsto (fun x => (subsetCutoffAt x : ℝ) / Real.log x) atTop (𝓝 0) := by
  have hl := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have h := (cutoff_rounding_ratio_tendsto.mul_const 4).div_atTop hl
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)] with x hx
  have hll : 0 < Real.log (Real.log x) := Real.log_pos hx
  simp only [Function.comp_def]
  unfold rawSubsetCutoff
  field_simp

theorem cutoff_mul_log_div_log_tendsto :
    Tendsto (fun x => (subsetCutoffAt x : ℝ) * Real.log (subsetCutoffAt x : ℝ) / Real.log x)
      atTop (𝓝 4) := by
  have h := (cutoff_rounding_ratio_tendsto.mul_const 4).mul cutoff_log_ratio_tendsto
  simp only [one_mul, mul_one] at h
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)] with x hx
  have hll : 0 < Real.log (Real.log x) := Real.log_pos hx
  unfold rawSubsetCutoff
  field_simp

noncomputable def tailExponent (c x : ℝ) : ℝ :=
  Real.log 2 + (subsetCutoffAt x : ℝ) * Real.log c +
    (subsetCutoffAt x : ℝ) / 2 * (Real.log 12 + 1 - Real.log (subsetCutoffAt x : ℝ))

theorem tailExponent_ratio_tendsto (c : ℝ) :
    Tendsto (fun x => tailExponent c x / Real.log x) atTop (𝓝 (-2)) := by
  have hconst : Tendsto (fun x => Real.log 2 / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h := hconst.add (cutoff_div_log_tendsto.mul_const (Real.log c + (Real.log 12 + 1) / 2))
    |>.sub (cutoff_mul_log_div_log_tendsto.div_const 2)
  norm_num only at h
  simp only [zero_mul, add_zero, zero_sub] at h
  convert h using 1
  funext x
  unfold tailExponent
  ring

noncomputable def subsetTailAt (c x : ℝ) : ℝ :=
  ∑' m, c ^ (subsetCutoffAt x + m) * subsetWeight (subsetCutoffAt x + m)

theorem subsetTailAt_nonneg {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : 0 ≤ subsetTailAt c x := by
  apply tsum_nonneg
  intro m
  exact mul_nonneg (pow_nonneg hc _) (subsetWeight_nonneg _)

theorem subsetTailAt_eventually_le_exp {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x in atTop, subsetTailAt c x ≤ Real.exp (tailExponent c x) := by
  have hcut := (tendsto_natCast_atTop_atTop.comp subsetCutoffAt_tendsto).eventually_ge_atTop
    (48 * c ^ 2 : ℝ)
  filter_upwards [hcut, subsetCutoffAt_tendsto.eventually_ge_atTop 1] with x hx hN
  simp only [Function.comp_def] at hx
  rw [tailExponent, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_nat_mul, Real.exp_log hc]
  exact subsetWeight_exp_tail_le hc.le (subsetCutoffAt x) hN (by linarith)

/-- The manuscript's tail statement, interpreted as a uniform upper bound:
for every fixed positive c and every positive epsilon the tail is eventually
at most n^(-2+epsilon). The sum includes the cutoff term, so it also bounds
the strictly longer subsets. -/
theorem subsetTailAt_eventually_le_rpow {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, subsetTailAt c x ≤ x ^ (-2 + ε) := by
  have hlim := (tailExponent_ratio_tendsto c).eventually_le_const
    (show (-2 : ℝ) < -2 + ε by linarith)
  filter_upwards [subsetTailAt_eventually_le_exp hc, hlim, eventually_gt_atTop (1 : ℝ)]
    with x htail hratio hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hexp : tailExponent c x ≤ (-2 + ε) * Real.log x :=
    (div_le_iff₀ hlog).mp hratio
  calc
    _ ≤ Real.exp (tailExponent c x) := htail
    _ ≤ Real.exp ((-2 + ε) * Real.log x) := Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.rpow_def_of_pos (by linarith : 0 < x)]; congr 1; ring

theorem subsetTail_eventually_le_rpow {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, subsetTailAt c n ≤ (n : ℝ) ^ (-2 + ε) :=
  tendsto_natCast_atTop_atTop.eventually (subsetTailAt_eventually_le_rpow hc hε)

/-- The scalar long-subset tail remains o(1/n) after the square-root
Bregman prefactor. Applying this to the actual convolution still requires
the exact convolution and tournament permanent bound. -/
theorem scaled_subsetTail_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => x * Real.sqrt (x + 1) * subsetTailAt c x) atTop (𝓝 0) := by
  have hupper : Tendsto (fun x : ℝ => 2 * x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
      (subsetTailAt_nonneg hc.le x)
  · have htail := subsetTailAt_eventually_le_rpow hc (by norm_num : (0 : ℝ) < 1 / 4)
    norm_num only at htail
    filter_upwards [htail, eventually_ge_atTop (1 : ℝ)] with x ht hx
    have hx0 : 0 ≤ x := by linarith
    have hs : Real.sqrt (x + 1) ≤ 2 * Real.sqrt x := by
      nlinarith [Real.sq_sqrt hx0, Real.sq_sqrt (by linarith : 0 ≤ x + 1),
        Real.sqrt_nonneg x, Real.sqrt_nonneg (x + 1)]
    have hm : x * Real.sqrt (x + 1) ≤ 2 * x * Real.sqrt x := by
      convert mul_le_mul_of_nonneg_left hs hx0 using 1
      ring
    have hp : x * Real.sqrt x * x ^ (-(7 / 4 : ℝ)) = x ^ (-(1 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      nth_rw 1 [← Real.rpow_one x]
      rw [← Real.rpow_add (by linarith : 0 < x), ← Real.rpow_add (by linarith : 0 < x)]
      norm_num
    calc
      _ ≤ x * Real.sqrt (x + 1) * x ^ (-(7 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left ht (mul_nonneg hx0 (Real.sqrt_nonneg _))
      _ ≤ (2 * x * Real.sqrt x) * x ^ (-(7 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hx0 _)
      _ = 2 * (x * Real.sqrt x * x ^ (-(7 / 4 : ℝ))) := by ring
      _ = _ := by rw [hp]

theorem scaled_subsetTail_nat_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.sqrt (n + 1) * subsetTailAt c n) atTop (𝓝 0) :=
  (scaled_subsetTail_tendsto_zero hc).comp tendsto_natCast_atTop_atTop

theorem scaled_subsetTail_isLittleO {c : ℝ} (hc : 0 < c) :
    (fun n : ℕ => Real.sqrt (n + 1) * subsetTailAt c n) =o[atTop]
      (fun n : ℕ => (1 : ℝ) / n) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn hz
    have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact False.elim ((one_div_ne_zero hne) hz)
  · convert scaled_subsetTail_nat_tendsto_zero hc using 1
    funext n
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    ring

/-- A common scalar threshold for all tournaments once their long-subset
contributions have been bounded by the displayed Bregman prefactor. -/
theorem scaled_subsetTail_eventually_small {c : ℝ} (hc : 0 < c) (C : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (C / 2) * Real.sqrt (n + 1) * subsetTailAt c n ≤ ε / n := by
  have h := (scaled_subsetTail_nat_tendsto_zero hc).const_mul (C / 2)
  simp only [mul_zero] at h
  filter_upwards [h.eventually_le_const hε, eventually_ge_atTop (1 : ℕ)] with n hn hpos
  apply (le_div_iff₀ (Nat.cast_pos.mpr (by omega : 0 < n))).mpr
  convert hn using 1
  ring

end TournamentHamiltonian
