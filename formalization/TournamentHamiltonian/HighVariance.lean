import TournamentHamiltonian.NormalizedConvolution

/-! Uniform exclusion of actual tournaments with high degree variance. -/

namespace TournamentHamiltonian

open scoped Classical Topology
open Filter

theorem highVariance_retained_of_small_cut {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) (hn : 1 ≤ n)
    (hV : 16 * (n : ℝ) ^ 2 * Real.log n ≤ degreeVariance T)
    (hk : (Uᶜ.card : ℝ) ≤ Real.log n) (hlog : Real.log n ≤ (n : ℝ) / 16) :
    13 * (n : ℝ) ^ 2 * Real.log n ≤ degreeVariance (inducedTournament T U) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hk0 : (0 : ℝ) ≤ Uᶜ.card := by positivity
  have h1 := mul_le_mul_of_nonneg_right hk (sq_nonneg (n : ℝ))
  have hsq := (sq_le_sq₀ hk0 hL).mpr hk
  have h2 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
  have h3 := mul_le_mul_of_nonneg_left hlog
    (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) * Real.log n)
  have hv := degreeVariance_inducedTournament_ge T U
  nlinarith

theorem short_cutoff_eventually_small :
    ∀ᶠ n : ℕ in atTop,
      4 ≤ n ∧ (subsetCutoff n : ℝ) ≤ Real.log n ∧ Real.log n ≤ (n : ℝ) / 16 := by
  have hk := cutoff_div_log_tendsto.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hk.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    hl.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 16), eventually_ge_atTop (4 : ℕ)]
    with n hk hl hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  refine ⟨hn, ?_, ?_⟩
  · simpa [subsetCutoff] using (div_le_iff₀ hlog).mp hk
  · have h := (div_le_iff₀ hnpos).mp hl
    linarith

theorem highVariance_short_permanent_eventually_le :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      16 * (n : ℝ) ^ 2 * Real.log n ≤ degreeVariance T →
      ∀ U : Finset (Fin n), U.card < subsetCutoff n →
        ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
          Real.exp 7 * Real.sqrt ((Uᶜ.card : ℝ) + 1) * (Uᶜ.card.factorial : ℝ) / (2 : ℝ) ^ Uᶜ.card *
            (n : ℝ) ^ (-(13 / 8 : ℝ)) := by
  filter_upwards [short_cutoff_eventually_small] with n hn T hV U hU
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hcut : (U.card : ℝ) ≤ Real.log n := by
    have hc : (U.card : ℝ) ≤ subsetCutoff n := by exact_mod_cast (show U.card ≤ subsetCutoff n by omega)
    exact hc.trans hn.2.1
  have hcard : Uᶜ.card = n - U.card := by simpa using Finset.card_compl U
  have hUc : 3 ≤ Uᶜ.card := by
    have hkN : (U.card : ℝ) ≤ (n : ℝ) / 16 := hcut.trans hn.2.2
    have hkcard : U.card ≤ n := by simpa using U.card_le_univ
    have hcast : (Uᶜ.card : ℝ) = (n : ℝ) - U.card := by
      rw [hcard, Nat.cast_sub hkcard]
    have h3 : (3 : ℝ) ≤ Uᶜ.card := by linarith
    exact_mod_cast h3
  have hv := highVariance_retained_of_small_cut T Uᶜ (by omega) hV (by simpa using hcut) hn.2.2
  have hper := adjacency_permanent_le_stirling_variance (inducedTournament T Uᶜ) hUc
  rw [← adjacency_principal_permanent_eq_induced] at hper
  apply hper.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hnpos : (0 : ℝ) < n := by linarith
  have hL : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hm : (Uᶜ.card : ℝ) ≤ n := by exact_mod_cast (show Uᶜ.card ≤ n by simpa using Uᶜ.card_le_univ)
  have hmp : (0 : ℝ) < Uᶜ.card := by exact_mod_cast (show 0 < Uᶜ.card by omega)
  have hvar : (13 / 8 : ℝ) * Real.log n ≤ degreeVariance (inducedTournament T Uᶜ) / (8 * (Uᶜ.card : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hs := (sq_le_sq₀ hmp.le hnpos.le).mpr hm
    have hh := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 13 * Real.log n)
    nlinarith
  rw [Real.rpow_def_of_pos hnpos]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  linarith

noncomputable def shortConvolution {n : ℕ} (T : Tournament n) (N : ℕ) : ℝ :=
  ∑ U, if U.card < N then convolutionTerm T U else 0

theorem shortConvolution_add_longConvolution {n : ℕ} (T : Tournament n) (N : ℕ) :
    shortConvolution T N + longConvolution T N = (pathCount T : ℝ) := by
  rw [pathCount_eq_positive_convolution]
  unfold shortConvolution longConvolution
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro U _
  change (if U.card < N then convolutionTerm T U else 0) +
    (if N ≤ U.card then convolutionTerm T U else 0) = convolutionTerm T U
  by_cases h : U.card < N
  · simp [h, show ¬N ≤ U.card by omega]
  · simp [h, show N ≤ U.card by omega]

theorem subsetWeight_summable : Summable subsetWeight := by
  have h := subsetMoment_summable (by norm_num : (0 : ℝ) ≤ 1) 0
  convert h using 1
  funext k
  simp [subsetMoment]

noncomputable def subsetWeightMass : ℝ := ∑' k, subsetWeight k

theorem subsetWeightMass_nonneg : 0 ≤ subsetWeightMass :=
  tsum_nonneg subsetWeight_nonneg

theorem shortConvolution_le_factor {n : ℕ} (T : Tournament n) (N : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hper : ∀ U : Finset (Fin n), U.card < N →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        Real.exp 7 * Real.sqrt ((Uᶜ.card : ℝ) + 1) * (Uᶜ.card.factorial : ℝ) / (2 : ℝ) ^ Uᶜ.card * q) :
    shortConvolution T N ≤ Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n *
      subsetWeightMass * q := by
  let B : ℝ := Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n * q
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsum : shortConvolution T N ≤ B *
      (∑ k ∈ Finset.range (n + 1), if k < N then subsetWeight k else 0) := by
    unfold shortConvolution
    rw [sum_finsets_by_card, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
    by_cases hN : k < N
    · have he : (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          if U.card < N then convolutionTerm T U else 0) =
          ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k, convolutionTerm T U := by
        apply Finset.sum_congr rfl
        intro U hU
        rw [(Finset.mem_powersetCard.mp hU).2, ite_eq_left hN]
      rw [he, ite_eq_left hN]
      have h := sum_convolution_card_le_of_permanent_bound T k hkn q hq (fun U hU =>
        hper U (by rwa [(Finset.mem_powersetCard.mp hU).2]))
      convert h using 1
      dsimp [B]
      ring
    · have he : (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          if U.card < N then convolutionTerm T U else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro U hU
        rw [(Finset.mem_powersetCard.mp hU).2, ite_eq_right hN]
      rw [he, ite_eq_right hN, mul_zero]
  have hmass : (∑ k ∈ Finset.range (n + 1), if k < N then subsetWeight k else 0) ≤ subsetWeightMass := by
    apply (Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (n + 1)) => ?_)).trans
      (subsetWeight_summable.sum_le_tsum _ (fun _ _ => subsetWeight_nonneg _))
    split_ifs
    · rfl
    · exact subsetWeight_nonneg _
  have h := hsum.trans (mul_le_mul_of_nonneg_left hmass hB)
  convert h using 1
  dsimp [B]
  ring

theorem highVariance_short_normalized_eventually_le :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      16 * (n : ℝ) ^ 2 * Real.log n ≤ degreeVariance T →
      shortConvolution T (subsetCutoff n) / meanPaths n ≤
        (Real.exp 7 / 2) * Real.sqrt ((n : ℝ) + 1) * subsetWeightMass * (n : ℝ) ^ (-(13 / 8 : ℝ)) := by
  filter_upwards [highVariance_short_permanent_eventually_le, eventually_ge_atTop (1 : ℕ)]
    with n hper hn T hV
  have h := shortConvolution_le_factor T (subsetCutoff n) ((n : ℝ) ^ (-(13 / 8 : ℝ)))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hper T hV)
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  apply (div_le_iff₀ hm).mpr
  rw [meanPaths_eq_twice_normalization n hn]
  convert h using 1
  ring

theorem scaled_highVariance_prefactor_tendsto_zero :
    Tendsto (fun x : ℝ => x * Real.sqrt (x + 1) * x ^ (-(13 / 8 : ℝ))) atTop (𝓝 0) := by
  have hupper : Tendsto (fun x : ℝ => 2 * x ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 ≤ x := by linarith
    have hs : Real.sqrt (x + 1) ≤ 2 * Real.sqrt x := by
      nlinarith [Real.sq_sqrt hx0, Real.sq_sqrt (by linarith : 0 ≤ x + 1),
        Real.sqrt_nonneg x, Real.sqrt_nonneg (x + 1)]
    have hm : x * Real.sqrt (x + 1) ≤ 2 * x * Real.sqrt x := by
      convert mul_le_mul_of_nonneg_left hs hx0 using 1
      ring
    have hp : x * Real.sqrt x * x ^ (-(13 / 8 : ℝ)) = x ^ (-(1 / 8 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      nth_rw 1 [← Real.rpow_one x]
      rw [← Real.rpow_add (by linarith : 0 < x), ← Real.rpow_add (by linarith : 0 < x)]
      norm_num
    calc
      _ ≤ (2 * x * Real.sqrt x) * x ^ (-(13 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hx0 _)
      _ = 2 * (x * Real.sqrt x * x ^ (-(13 / 8 : ℝ))) := by ring
      _ = _ := by rw [hp]

theorem highVariance_short_eventually_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      16 * (n : ℝ) ^ 2 * Real.log n ≤ degreeVariance T →
      shortConvolution T (subsetCutoff n) / meanPaths n ≤ ε / n := by
  have hscalar := (scaled_highVariance_prefactor_tendsto_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul ((Real.exp 7 / 2) * subsetWeightMass)
  simp only [mul_zero] at hscalar
  filter_upwards [highVariance_short_normalized_eventually_le,
    hscalar.eventually_le_const hε, eventually_ge_atTop (1 : ℕ)] with n hbound hsmall hn T hV
  dsimp only [Function.comp_def] at hsmall
  apply (hbound T hV).trans
  apply (le_div_iff₀ (Nat.cast_pos.mpr (show 0 < n by omega))).mpr
  convert hsmall using 1
  ring

/-- The manuscript's high-variance exclusion, quantified with one common
threshold for all actual tournaments and the original Hamiltonian count. -/
theorem highVariance_pathCount_eventually_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      16 * (n : ℝ) ^ 2 * Real.log n ≤ degreeVariance T →
      (pathCount T : ℝ) / meanPaths n ≤ ε / n := by
  filter_upwards [highVariance_short_eventually_small (show 0 < ε / 2 by positivity),
    longConvolution_eventually_small (show 0 < ε / 2 by positivity)] with n hshort hlong T hV
  rw [← shortConvolution_add_longConvolution T (subsetCutoff n), add_div]
  have hs := hshort T hV
  have hl := hlong T
  exact (add_le_add hs hl).trans_eq (by ring)

end TournamentHamiltonian
