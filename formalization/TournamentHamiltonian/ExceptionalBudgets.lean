import TournamentHamiltonian.ExceptionalDegrees
import TournamentHamiltonian.UniformPreconditioningBudgets

/-! Uniform scalar error budgets for exceptional four-block suppression. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter

noncomputable def exceptionalCrossEps (n : ℕ) : ℝ := 2 * (401 * Real.log (n : ℝ) + 1) / n
noncomputable def exceptionalCrossBeta (n : ℕ) : ℝ := 20 * Real.sqrt (2400 * Real.log (n : ℝ) / n)
noncomputable def exceptionalCrossCap (n : ℕ) : ℝ :=
  19 / 100 + 4 * exceptionalCrossEps n + 4 * exceptionalCrossBeta n + 4 * exceptionalCrossBeta n ^ 2

theorem exceptionalCrossBeta_tendsto_zero : Tendsto exceptionalCrossBeta atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (hlog.const_mul 2400).sqrt.const_mul 20
  simp only [mul_zero, Real.sqrt_zero] at h
  convert h using 1
  ext n
  dsimp [exceptionalCrossBeta]
  congr 2
  ring

theorem exceptionalCrossCap_tendsto : Tendsto exceptionalCrossCap atTop (𝓝 (19 / 100)) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have heps := ((hlog.const_mul 802).add (hinv.const_mul 2))
  have hb := exceptionalCrossBeta_tendsto_zero
  have h := ((((tendsto_const_nhds : Tendsto (fun _ : ℕ => (19 / 100 : ℝ)) atTop (𝓝 (19 / 100 : ℝ))).add (heps.const_mul 4)).add (hb.const_mul 4)).add ((hb.pow 2).const_mul 4))
  simp only [mul_zero, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h
  convert h using 1
  ext n
  dsimp [exceptionalCrossCap, exceptionalCrossEps]
  ring

theorem exceptional_cross_profiles_uniform_eventually :
    ∀ᶠ n : ℕ in atTop, ∀ d N beta : ℝ,
      0 ≤ d → d ≤ 401 * Real.log (n : ℝ) → (n : ℝ) / 2 ≤ N →
      0 ≤ beta → beta ≤ exceptionalCrossBeta n →
      19 / 100 + 4 * ((d + 1) / N) + 4 * beta + 4 * beta ^ 2 ≤ 1 / 4 ∧
        2 + 2 * beta ≤ 3 := by
  filter_upwards [exceptionalCrossCap_tendsto.eventually_le_const (by norm_num : (19 / 100 : ℝ) < 1 / 4),
    exceptionalCrossBeta_tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (1 : ℕ)] with n hc hb hn d N beta hd hdA hN hbeta hbetaA
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hb0 : 0 ≤ exceptionalCrossBeta n := by unfold exceptionalCrossBeta; positivity
  have heps : (d + 1) / N ≤ exceptionalCrossEps n := by
    apply (div_le_div_of_nonneg_right (add_le_add hdA (le_refl 1)) hN0.le).trans
    dsimp [exceptionalCrossEps]
    have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ 401 * Real.log (n : ℝ) + 1)
      (by positivity : 0 < (n : ℝ) / 2) hN
    convert h using 1; ring
  have hs := (sq_le_sq₀ hbeta hb0).mpr hbetaA
  constructor
  · apply le_trans _ hc
    dsimp [exceptionalCrossCap]
    linarith
  · linarith

theorem fourBlock_error_le_coarse (f N c L : ℝ) (_hf : 0 ≤ f) (hN : 0 < N)
    (hc : 19 / 100 ≤ c) (hL0 : 0 ≤ L) (hL : L ≤ 3) :
    4 * f ^ 2 / N + 2 * L ^ 2 * f ^ 2 / (c ^ 2 * N) ≤ 604 * f ^ 2 / N := by
  have hc0 : 0 < c := by linarith
  have hLsq : L ^ 2 ≤ 9 := by nlinarith
  have hcsq : (19 / 100 : ℝ) ^ 2 ≤ c ^ 2 := by nlinarith
  have hnum : 2 * L ^ 2 ≤ 600 * c ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hnum (sq_nonneg f)
  have hh : 2 * L ^ 2 * f ^ 2 / (c ^ 2 * N) ≤ 600 * f ^ 2 / N := by
    apply (div_le_iff₀ (by positivity : 0 < c ^ 2 * N)).mpr
    have heq : (600 * f ^ 2 / N) * (c ^ 2 * N) = 600 * c ^ 2 * f ^ 2 := by field_simp
    rw [heq]
    exact hprod
  calc
    _ ≤ 4 * f ^ 2 / N + 600 * f ^ 2 / N := add_le_add (le_refl _) hh
    _ = _ := by ring

theorem exceptional_fourBlock_error_uniform_eventually_small (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ f N c L : ℝ,
      0 ≤ f → f ≤ 400 * Real.log (n : ℝ) → (n : ℝ) / 2 ≤ N →
      19 / 100 ≤ c → 0 ≤ L → L ≤ 3 →
      4 * f ^ 2 / N + 2 * L ^ 2 * f ^ 2 / (c ^ 2 * N) ≤ eps := by
  have hlim := (log_pow_div_sqrt_nat_tendsto_zero 2).const_mul (200000000 : ℝ)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually_le_const heps, eventually_ge_atTop (1 : ℕ)]
    with n he hn f N c L hf hfA hN hc hL0 hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hf2 := (sq_le_sq₀ hf (by positivity : 0 ≤ 400 * Real.log (n : ℝ))).mpr hfA
  have h1 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf2 (by norm_num : (0 : ℝ) ≤ 604)) hN0.le
  have h2 := div_le_div_of_nonneg_left (by positivity : 0 ≤ 604 * (400 * Real.log (n : ℝ)) ^ 2)
    (by positivity : 0 < (n : ℝ) / 2) hN
  have hs : Real.sqrt n ≤ n := by nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg (n : ℝ)]
  have h3 := div_le_div_of_nonneg_left (by positivity : 0 ≤ 200000000 * Real.log (n : ℝ) ^ 2)
    (Real.sqrt_pos.mpr hn0) hs
  apply (fourBlock_error_le_coarse f N c L hf hN0 hc hL0 hL).trans
  apply h1.trans
  apply h2.trans
  apply le_trans _ he
  have h4 : 604 * (400 * Real.log (n : ℝ)) ^ 2 / ((n : ℝ) / 2) ≤
      200000000 * Real.log (n : ℝ) ^ 2 / n := by
    field_simp
    nlinarith [sq_nonneg (Real.log (n : ℝ))]
  exact h4.trans (by convert h3 using 1; ring)

theorem convolution_cutoff_error_eventually_small (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, 2 * (subsetCutoff n : ℝ) ^ 2 / n ≤ eps := by
  have hlim := (log_pow_div_sqrt_nat_tendsto_zero 2).const_mul (2 : ℝ)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually_le_const heps, short_cutoff_eventually_small] with n he hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hk2 := (sq_le_sq₀ (by positivity : 0 ≤ (subsetCutoff n : ℝ)) hlog).mpr hn.2.1
  have h1 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk2 (by norm_num : (0 : ℝ) ≤ 2)) hn0.le
  have hs : Real.sqrt n ≤ n := by nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg (n : ℝ)]
  have h2 := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * Real.log (n : ℝ) ^ 2)
    (Real.sqrt_pos.mpr hn0) hs
  apply h1.trans
  apply h2.trans
  simpa only [mul_div_assoc] using he

theorem exceptional_suppression_uniform_eventually :
    ∀ᶠ n : ℕ in atTop, ∀ f d N beta : ℝ,
      0 ≤ f → f ≤ 400 * Real.log (n : ℝ) →
      0 ≤ d → d ≤ 401 * Real.log (n : ℝ) → (n : ℝ) / 2 ≤ N →
      0 ≤ beta → beta ≤ exceptionalCrossBeta n →
      let c := 19 / 100 + 4 * ((d + 1) / N) + 4 * beta + 4 * beta ^ 2
      let L := 2 + 2 * beta
      c ≤ 1 / 4 ∧
        4 * f ^ 2 / N + 2 * L ^ 2 * f ^ 2 / (c ^ 2 * N) +
          2 * (subsetCutoff n : ℝ) ^ 2 / n ≤ Real.log (6 / 5 : ℝ) / 2 := by
  let eps : ℝ := Real.log (6 / 5 : ℝ) / 4
  have heps : 0 < eps := by dsimp [eps]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  filter_upwards [exceptional_cross_profiles_uniform_eventually,
    exceptional_fourBlock_error_uniform_eventually_small eps heps,
    convolution_cutoff_error_eventually_small eps heps, eventually_ge_atTop (1 : ℕ)]
    with n hcap herr hcut hn f d N beta hf hfA hd hdA hN hb hbA
  let c : ℝ := 19 / 100 + 4 * ((d + 1) / N) + 4 * beta + 4 * beta ^ 2
  let L : ℝ := 2 + 2 * beta
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hc : 19 / 100 ≤ c := by
    dsimp [c]
    have hratio : 0 ≤ (d + 1) / N := by positivity
    nlinarith [sq_nonneg beta]
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hp := hcap d N beta hd hdA hN hb hbA
  have he := herr f N c L hf hfA hN hc hL0 hp.2
  exact ⟨hp.1, by dsimp [eps] at he hcut; linarith⟩

end TournamentHamiltonian
