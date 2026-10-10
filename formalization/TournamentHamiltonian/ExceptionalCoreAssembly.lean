import TournamentHamiltonian.DeletedFourBlockBounds
import TournamentHamiltonian.AmbientCoreMinors
import TournamentHamiltonian.CrudeExceptionalExclusion

/-! Actual ambient core-minor input to the global exceptional exclusion. The
analytic input is stated explicitly; all four-block, normalization and convolution
operations in this module are proved for the original actual tournament. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter

noncomputable def exceptionalAssemblyError (n : ℕ) : ℝ :=
  200000000 * Real.log (n : ℝ) ^ 2 / Real.sqrt n

theorem exceptionalAssemblyError_tendsto_zero : Tendsto exceptionalAssemblyError atTop (𝓝 0) := by
  have h := (log_pow_div_sqrt_nat_tendsto_zero 2).const_mul (200000000 : ℝ)
  simp only [mul_zero] at h
  convert h using 1
  ext n
  dsimp [exceptionalAssemblyError]
  ring

theorem exceptional_assembly_error_le {n : ℕ} (hn : 1 ≤ n) (f N : ℝ)
    (hf : 0 ≤ f) (hfa : f ≤ 400 * Real.log (n : ℝ)) (hN : (n : ℝ) / 2 ≤ N) :
    292 * f ^ 2 / N ≤ exceptionalAssemblyError n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hf2 := (sq_le_sq₀ hf (by positivity : 0 ≤ 400 * Real.log (n : ℝ))).mpr hfa
  have h1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hf2 (by norm_num : (0 : ℝ) ≤ 292)) hN0.le
  have h2 := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ 292 * (400 * Real.log (n : ℝ)) ^ 2)
    (by positivity : 0 < (n : ℝ) / 2) hN
  have hs : Real.sqrt n ≤ n := by nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg (n : ℝ)]
  have h3 := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ 200000000 * Real.log (n : ℝ) ^ 2) (Real.sqrt_pos.mpr hn0) hs
  calc
    _ ≤ 292 * (400 * Real.log (n : ℝ)) ^ 2 / N := h1
    _ ≤ 292 * (400 * Real.log (n : ℝ)) ^ 2 / ((n : ℝ) / 2) := h2
    _ ≤ 200000000 * Real.log (n : ℝ) ^ 2 / n := by
      apply (le_div_iff₀ hn0).mpr
      have heq : (292 * (400 * Real.log (n : ℝ)) ^ 2 / ((n : ℝ) / 2)) * n =
          93440000 * Real.log (n : ℝ) ^ 2 := by field_simp; ring
      rw [heq]
      nlinarith [sq_nonneg (Real.log (n : ℝ))]
    _ ≤ exceptionalAssemblyError n := h3

/-- The remaining analytic obligation concerns actual nonprincipal core minors.
The factor 2 is the established absolute bound for their own actual Gaussian factor. -/
def HasUniformExceptionalCoreMinorBound (E : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
    degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
    ∀ U : Finset (Fin n), U.card < subsetCutoff n → Disjoint U (exceptionalVertices T) →
    let F := exceptionalVertices T
    let M := (F ∪ U)ᶜ
    ∀ s ≤ F.card, ∀ I ∈ M.powersetCard (F.card - s), ∀ J ∈ M.powersetCard (F.card - s),
      selectedPermanent (adjacency T) (M \ J) (M \ I) ≤
        ((2 * Real.exp (-1) * Real.exp (E n)) *
          (((M.card - (F.card - s)).factorial : ℝ) / (2 : ℝ) ^ (M.card - (F.card - s)))) *
          (∏ i ∈ I, ambientCoreLeft T M i) * (∏ j ∈ J, ambientCoreRight T M j)

theorem hasCrudeUniformExceptionalPermanentBound_of_core (E : ℕ → ℝ)
    (hcore : HasUniformExceptionalCoreMinorBound E) :
    HasCrudeUniformExceptionalPermanentBound (fun n => E n + exceptionalAssemblyError n) := by
  filter_upwards [hcore, short_deleted_permanent_fourBlock_eventually,
    short_deleted_exceptional_core_uniform_dense, eventually_ge_atTop (2 : ℕ)]
    with n hc hfour hdense hn T hV U hU hUF
  let F := exceptionalVertices T
  let M := (F ∪ U)ᶜ
  let B := 2 * Real.exp (-1) * Real.exp (E n)
  have h := hfour T hV U hU hUF B (by dsimp [B]; positivity) (hc T hV U hU hUF)
  have herr := exceptional_assembly_error_le (show 1 ≤ n by omega) (F.card : ℝ) (M.card : ℝ)
    (by positivity) (exceptionalVertices_card_le_log T hn hV) (hdense T hV U hU).2.1
  have hexp := Real.exp_le_exp.mpr herr
  have hm := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ B * (1 / 4 : ℝ) ^ F.card)
  have hnorm := h.trans hm
  have heq : B * (1 / 4 : ℝ) ^ F.card * Real.exp (exceptionalAssemblyError n) =
      2 * Real.exp (-1) * (1 / 4 : ℝ) ^ F.card * Real.exp (E n + exceptionalAssemblyError n) := by
    dsimp [B]
    rw [Real.exp_add]
    ring
  rw [heq] at hnorm
  exact (div_le_iff₀ (by positivity : 0 <
    ((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))).mp hnorm

theorem largeScore_eventually_lt_mean_of_core_minor_bound (E : ℕ → ℝ)
    (hE : Tendsto E atTop (𝓝 0)) (hcore : HasUniformExceptionalCoreMinorBound E) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      1 ≤ (exceptionalVertices T).card → (pathCount T : ℝ) < meanPaths n := by
  have hlim := hE.add exceptionalAssemblyError_tendsto_zero
  simp only [add_zero] at hlim
  exact largeScore_eventually_lt_mean_of_crude_bound _ hlim
    (hasCrudeUniformExceptionalPermanentBound_of_core E hcore)

end TournamentHamiltonian
