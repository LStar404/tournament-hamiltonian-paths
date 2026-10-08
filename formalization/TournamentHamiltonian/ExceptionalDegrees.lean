import TournamentHamiltonian.HighVariance
import TournamentHamiltonian.PreconditioningBounds

/-! Actual exceptional degrees and the induced dense core. -/

namespace TournamentHamiltonian

open scoped Classical Topology
open Filter

noncomputable def exceptionalVertices {n : ℕ} (T : Tournament n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (9 / 10 : ℝ) * ((n : ℝ) - 1) < |score T i|)

theorem mem_exceptionalVertices_iff_degree {n : ℕ} (T : Tournament n) (hn : 2 ≤ n)
    (i : Fin n) :
    i ∈ exceptionalVertices T ↔
      (rowDegree T.val i : ℝ) / ((n : ℝ) - 1) < 1 / 20 ∨
        19 / 20 < (rowDegree T.val i : ℝ) / ((n : ℝ) - 1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) - 1 := by linarith
  simp only [exceptionalVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    score_eq_twice_rowDegree, lt_abs, div_lt_iff₀ hp, lt_div_iff₀ hp]
  constructor <;> rintro (h | h)
  · right; linarith
  · left; linarith
  · right; linarith
  · left; linarith

theorem exceptionalVertices_score_mass {n : ℕ} (T : Tournament n) (hn : 1 ≤ n) :
    (exceptionalVertices T).card * (81 / 100 : ℝ) * ((n : ℝ) - 1) ^ 2 ≤
      4 * degreeVariance T := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlocal : ∀ i ∈ exceptionalVertices T,
      (81 / 100 : ℝ) * ((n : ℝ) - 1) ^ 2 ≤ score T i ^ 2 := by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    have hpos : (0 : ℝ) ≤ (9 / 10 : ℝ) * ((n : ℝ) - 1) := by positivity
    have hs := (sq_le_sq₀ hpos (abs_nonneg (score T i))).mpr h.le
    nlinarith [sq_abs (score T i)]
  have hs := Finset.sum_le_sum hlocal
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have ht : (∑ i ∈ exceptionalVertices T, score T i ^ 2) ≤ ∑ i, score T i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  rw [degreeVariance_eq_score_sum]
  nlinarith

theorem exceptionalVertices_card_le_log {n : ℕ} (T : Tournament n) (hn : 2 ≤ n)
    (hV : degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n) :
    ((exceptionalVertices T).card : ℝ) ≤ 400 * Real.log n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hm := exceptionalVertices_score_mass T (by omega)
  have hratio : (n : ℝ) ^ 2 ≤ 4 * ((n : ℝ) - 1) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hratio hL
  have hden : 0 < ((n : ℝ) - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have h : ((exceptionalVertices T).card : ℝ) * ((n : ℝ) - 1) ^ 2 ≤
      400 * Real.log n * ((n : ℝ) - 1) ^ 2 := by nlinarith
  exact le_of_mul_le_mul_right h hden

theorem nonexceptional_score_le {n : ℕ} (T : Tournament n) (i : Fin n)
    (hi : i ∉ exceptionalVertices T) :
    |score T i| ≤ (9 / 10 : ℝ) * ((n : ℝ) - 1) := by
  simpa [exceptionalVertices] using hi

theorem exceptional_core_score_le {n : ℕ} (T : Tournament n)
    (i : Fin (exceptionalVertices T)ᶜ.card) :
    |score (inducedTournament T (exceptionalVertices T)ᶜ) i| ≤
      (9 / 10 : ℝ) * ((n : ℝ) - 1) + (exceptionalVertices T).card := by
  rw [score_inducedTournament]
  let v := subsetVertexEquiv (exceptionalVertices T)ᶜ i
  have hv : (v : Fin n) ∉ exceptionalVertices T := by
    exact Finset.mem_compl.mp v.property
  have hd := subsetScore_sub_score_abs_le T (exceptionalVertices T)ᶜ v
  simp only [compl_compl] at hd
  have ha := abs_add_le (subsetScore T (exceptionalVertices T)ᶜ v - score T v) (score T v)
  have he : subsetScore T (exceptionalVertices T)ᶜ v - score T v + score T v =
      subsetScore T (exceptionalVertices T)ᶜ v := by ring
  rw [he] at ha
  exact ha.trans (by linarith [nonexceptional_score_le T v hv])

theorem exceptional_core_normalized_score_le {n : ℕ} (T : Tournament n) (hn : 2 ≤ n)
    (hf : ((exceptionalVertices T).card : ℝ) ≤ ((n : ℝ) - 1) / 40)
    (i : Fin (exceptionalVertices T)ᶜ.card) :
    |score (inducedTournament T (exceptionalVertices T)ᶜ) i /
      (((exceptionalVertices T)ᶜ.card : ℝ) - 1)| ≤ 19 / 20 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : (exceptionalVertices T).card ≤ n := by simpa using (exceptionalVertices T).card_le_univ
  have hm : (((exceptionalVertices T)ᶜ.card : ℝ)) = (n : ℝ) - (exceptionalVertices T).card := by
    have hc : (exceptionalVertices T)ᶜ.card = n - (exceptionalVertices T).card := by
      simpa using Finset.card_compl (exceptionalVertices T)
    rw [hc, Nat.cast_sub hk]
  have hp : 0 < (((exceptionalVertices T)ᶜ.card : ℝ) - 1) := by linarith
  rw [abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have h := exceptional_core_score_le T i
  linarith

theorem exceptional_core_normalized_score_eventually_le :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
      ∀ i : Fin (exceptionalVertices T)ᶜ.card,
        |score (inducedTournament T (exceptionalVertices T)ᶜ) i /
          (((exceptionalVertices T)ᶜ.card : ℝ) - 1)| ≤ 19 / 20 := by
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hl.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 32000),
    eventually_ge_atTop (2 : ℕ)] with n hlog hn T hV i
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl' := (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mp hlog
  apply exceptional_core_normalized_score_le T hn _ i
  have hf := exceptionalVertices_card_le_log T hn hV
  linarith

theorem degreeVariance_inducedTournament_le {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) :
    degreeVariance (inducedTournament T U) ≤ 2 * degreeVariance T +
      (n : ℝ) * (Uᶜ.card : ℝ) ^ 2 / 2 := by
  have hlocal (i : Fin n) : subsetScore T U i ^ 2 ≤
      2 * score T i ^ 2 + 2 * (Uᶜ.card : ℝ) ^ 2 := by
    have hd := subsetScore_sub_score_abs_le T U i
    have hs := (sq_le_sq₀ (abs_nonneg (subsetScore T U i - score T i))
      (Nat.cast_nonneg Uᶜ.card)).mpr hd
    simp only [sq_abs] at hs
    nlinarith [sq_nonneg (score T i - (subsetScore T U i - score T i))]
  have hs := Finset.sum_le_sum (s := U) (fun i _ => hlocal i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at hs
  have hfull : (∑ i ∈ U, score T i ^ 2) ≤ ∑ i, score T i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) (fun _ _ _ => sq_nonneg _)
  have hcard : (U.card : ℝ) ≤ n := by exact_mod_cast (show U.card ≤ n by simpa using U.card_le_univ)
  have hmul := mul_le_mul_of_nonneg_right hcard (sq_nonneg (Uᶜ.card : ℝ))
  rw [degreeVariance_inducedTournament_eq, degreeVariance_eq_score_sum]
  nlinarith

theorem scoreVariance_eq_degreeVariance {n : ℕ} (T : Tournament n) :
    scoreVariance T = 4 * degreeVariance T / ((n : ℝ) - 1) ^ 2 := by
  rw [scoreVariance_eq_score_sq, degreeVariance_eq_score_sum]
  ring

theorem exceptional_core_variance_le_log {n : ℕ} (T : Tournament n) (hn : 4 ≤ n)
    (hV : degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n)
    (hf : ((exceptionalVertices T).card : ℝ) ≤ ((n : ℝ) - 1) / 40)
    (hlog : Real.log n ≤ (n : ℝ) / 160000) :
    scoreVariance (inducedTournament T (exceptionalVertices T)ᶜ) ≤ 600 * Real.log n := by
  let F := exceptionalVertices T
  let m : ℕ := Fᶜ.card
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hf0 : (0 : ℝ) ≤ F.card := by positivity
  have hfL : (F.card : ℝ) ≤ 400 * Real.log n := exceptionalVertices_card_le_log T (by omega) hV
  have hfsq := (sq_le_sq₀ hf0 (by positivity : (0 : ℝ) ≤ 400 * Real.log n)).mpr hfL
  have hlogmul := mul_le_mul_of_nonneg_left hlog
    (by positivity : (0 : ℝ) ≤ 80000 * (n : ℝ) * Real.log n)
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

theorem exceptional_core_variance_eventually_le_log :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
      scoreVariance (inducedTournament T (exceptionalVertices T)ᶜ) ≤ 600 * Real.log n := by
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hl.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 160000),
    eventually_ge_atTop (4 : ℕ)] with n hlog hn T hV
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hl' := (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mp hlog
  have hf := exceptionalVertices_card_le_log T (by omega) hV
  apply exceptional_core_variance_le_log T hn hV _ (by linarith)
  linarith

/-- The actual induced core is in one fixed dense class, uniformly over all
low-variance tournaments. The logarithm is taken at the core's own order. -/
theorem exceptional_core_uniform_dense :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
      2 ≤ (exceptionalVertices T)ᶜ.card ∧
        (∀ i, |tournamentScorePotential (inducedTournament T (exceptionalVertices T)ᶜ) i| ≤ 19 / 20) ∧
        scoreVariance (inducedTournament T (exceptionalVertices T)ᶜ) ≤
          1200 * Real.log ((exceptionalVertices T)ᶜ.card : ℝ) := by
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [exceptional_core_normalized_score_eventually_le,
    exceptional_core_variance_eventually_le_log,
    hl.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 32000),
    eventually_ge_atTop (4 : ℕ)] with n hcap hvar hlog hn T hV
  let m : ℕ := (exceptionalVertices T)ᶜ.card
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hl' := (div_le_iff₀ hnpos).mp hlog
  have hf := exceptionalVertices_card_le_log T (by omega) hV
  have hm : (m : ℝ) = (n : ℝ) - (exceptionalVertices T).card := by
    have he : m = n - (exceptionalVertices T).card := by dsimp [m]; simpa using Finset.card_compl (exceptionalVertices T)
    rw [he, Nat.cast_sub (show (exceptionalVertices T).card ≤ n by simpa using (exceptionalVertices T).card_le_univ)]
  have hm2 : (2 : ℝ) ≤ m := by linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have htwom : (n : ℝ) ≤ 2 * (m : ℝ) := by linarith
  have hL := Real.log_le_log hnpos htwom
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmpos.ne'] at hL
  have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hm2
  refine ⟨by exact_mod_cast hm2, fun i => hcap T hV i, ?_⟩
  have hv := hvar T hV
  change scoreVariance (inducedTournament T (exceptionalVertices T)ᶜ) ≤ 1200 * Real.log (m : ℝ)
  linarith

end TournamentHamiltonian
