import TournamentHamiltonian.ExceptionalDegrees

/-! Actual density and variance under further core deletions. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter

theorem deleted_exceptional_core_score_le {n : ℕ} (T : Tournament n) (D : Finset (Fin n)) (hFD : exceptionalVertices T ⊆ D)
    (i : Fin Dᶜ.card) :
    |score (inducedTournament T Dᶜ) i| ≤
      (9 / 10 : ℝ) * ((n : ℝ) - 1) + D.card := by
  rw [score_inducedTournament]
  let v := subsetVertexEquiv Dᶜ i
  have hv : (v : Fin n) ∉ exceptionalVertices T := by
    intro hvF
    exact Finset.mem_compl.mp v.property (hFD hvF)
  have hd := subsetScore_sub_score_abs_le T Dᶜ v
  simp only [compl_compl] at hd
  have ha := abs_add_le (subsetScore T Dᶜ v - score T v) (score T v)
  have he : subsetScore T Dᶜ v - score T v + score T v =
      subsetScore T Dᶜ v := by ring
  rw [he] at ha
  exact ha.trans (by linarith [nonexceptional_score_le T v hv])

theorem deleted_exceptional_core_normalized_score_le {n : ℕ} (T : Tournament n) (D : Finset (Fin n)) (hFD : exceptionalVertices T ⊆ D) (hn : 2 ≤ n)
    (hf : (D.card : ℝ) ≤ ((n : ℝ) - 1) / 40)
    (i : Fin Dᶜ.card) :
    |score (inducedTournament T Dᶜ) i /
      ((Dᶜ.card : ℝ) - 1)| ≤ 19 / 20 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : D.card ≤ n := by simpa using D.card_le_univ
  have hm : ((Dᶜ.card : ℝ)) = (n : ℝ) - D.card := by
    have hc : Dᶜ.card = n - D.card := by
      simpa using Finset.card_compl D
    rw [hc, Nat.cast_sub hk]
  have hp : 0 < ((Dᶜ.card : ℝ) - 1) := by linarith
  rw [abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have h := deleted_exceptional_core_score_le T D hFD i
  linarith

theorem deleted_exceptional_core_variance_le_log {n : ℕ} (T : Tournament n) (D : Finset (Fin n)) (hn : 4 ≤ n)
    (hV : degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n)
    (hd : (D.card : ℝ) ≤ 401 * Real.log n)
    (hf : (D.card : ℝ) ≤ ((n : ℝ) - 1) / 40)
    (hlog : Real.log n ≤ (n : ℝ) / 162000) :
    scoreVariance (inducedTournament T Dᶜ) ≤ 600 * Real.log n := by
  let F := D
  let m : ℕ := Fᶜ.card
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hf0 : (0 : ℝ) ≤ F.card := by positivity
  have hfL : (F.card : ℝ) ≤ 401 * Real.log n := hd
  have hfsq := (sq_le_sq₀ hf0 (by positivity : (0 : ℝ) ≤ 401 * Real.log n)).mpr hfL
  have hlogmul := mul_le_mul_of_nonneg_left hlog
    (by positivity : (0 : ℝ) ≤ 81000 * (n : ℝ) * Real.log n)
  have hv := degreeVariance_inducedTournament_le T Fᶜ
  simp only [compl_compl] at hv
  have hvmul := mul_le_mul_of_nonneg_left hfsq (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
  have hvbound : degreeVariance (inducedTournament T Fᶜ) ≤ (65 / 2 : ℝ) * (n : ℝ) ^ 2 * Real.log n := by
    nlinarith
  have hcard : (m : ℝ) = (n : ℝ) - F.card := by
    have he : m = n - F.card := by dsimp [m]; simpa using Finset.card_compl F
    rw [he, Nat.cast_sub (show F.card ≤ n by simpa using F.card_le_univ)]
  have hm : (n : ℝ) / 2 ≤ (m : ℝ) - 1 := by change (F.card : ℝ) ≤ _ at hf; linarith
  have hmpos : 0 < (m : ℝ) - 1 := by linarith
  have hmsq : (n : ℝ) ^ 2 / 4 ≤ ((m : ℝ) - 1) ^ 2 := by nlinarith
  rw [scoreVariance_eq_degreeVariance]
  apply (div_le_iff₀ (sq_pos_of_pos hmpos)).mpr
  have hh := mul_le_mul_of_nonneg_left hmsq (by positivity : (0 : ℝ) ≤ 600 * Real.log n)
  nlinarith

theorem deleted_exceptional_core_uniform_dense :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
      ∀ D : Finset (Fin n), exceptionalVertices T ⊆ D →
      (D.card : ℝ) ≤ 401 * Real.log n →
      2 ≤ Dᶜ.card ∧ (n : ℝ) / 2 ≤ (Dᶜ.card : ℝ) ∧
        (∀ i, |tournamentScorePotential (inducedTournament T Dᶜ) i| ≤ 19 / 20) ∧
        scoreVariance (inducedTournament T Dᶜ) ≤ 600 * Real.log n ∧
        scoreVariance (inducedTournament T Dᶜ) ≤ 1200 * Real.log (Dᶜ.card : ℝ) := by
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hl.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 162000),
    eventually_ge_atTop (4 : ℕ)] with n hlog hn T hV D hFD hd
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl' := (div_le_iff₀ hn0).mp hlog
  have hf : (D.card : ℝ) ≤ ((n : ℝ) - 1) / 40 := by linarith
  have hcard : (Dᶜ.card : ℝ) = (n : ℝ) - D.card := by
    have hc : Dᶜ.card = n - D.card := by simpa using Finset.card_compl D
    rw [hc, Nat.cast_sub (show D.card ≤ n by simpa using D.card_le_univ)]
  have hm2 : (2 : ℝ) ≤ Dᶜ.card := by linarith
  have hmpos : (0 : ℝ) < Dᶜ.card := by linarith
  have hNm : (n : ℝ) / 2 ≤ (Dᶜ.card : ℝ) := by linarith
  have hcap (i : Fin Dᶜ.card) : |tournamentScorePotential (inducedTournament T Dᶜ) i| ≤ 19 / 20 :=
    deleted_exceptional_core_normalized_score_le T D hFD (by omega) hf i
  have hvar := deleted_exceptional_core_variance_le_log T D hn hV hd hf (by linarith)
  have htwom : (n : ℝ) ≤ 2 * (Dᶜ.card : ℝ) := by linarith
  have hLn := Real.log_le_log hn0 htwom
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmpos.ne'] at hLn
  have hLtwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hm2
  exact ⟨by exact_mod_cast hm2, hNm, hcap, hvar, by linarith⟩

theorem short_deleted_exceptional_core_uniform_dense :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
      ∀ U : Finset (Fin n), U.card < subsetCutoff n →
      let D := exceptionalVertices T ∪ U
      2 ≤ Dᶜ.card ∧ (n : ℝ) / 2 ≤ (Dᶜ.card : ℝ) ∧
        (∀ i, |tournamentScorePotential (inducedTournament T Dᶜ) i| ≤ 19 / 20) ∧
        scoreVariance (inducedTournament T Dᶜ) ≤ 600 * Real.log n ∧
        scoreVariance (inducedTournament T Dᶜ) ≤ 1200 * Real.log (Dᶜ.card : ℝ) := by
  filter_upwards [deleted_exceptional_core_uniform_dense, short_cutoff_eventually_small]
    with n hcore hn T hV U hU
  apply hcore T hV (exceptionalVertices T ∪ U) Finset.subset_union_left
  have hf := exceptionalVertices_card_le_log T (by omega) hV
  have hk : (U.card : ℝ) ≤ Real.log (n : ℝ) :=
    (by exact_mod_cast hU.le : (U.card : ℝ) ≤ subsetCutoff n).trans hn.2.1
  have hc : ((exceptionalVertices T ∪ U).card : ℝ) ≤ (exceptionalVertices T).card + U.card := by
    exact_mod_cast Finset.card_union_le (exceptionalVertices T) U
  linarith

end TournamentHamiltonian
