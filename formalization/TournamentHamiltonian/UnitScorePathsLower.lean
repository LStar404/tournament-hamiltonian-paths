import TournamentHamiltonian.SmallScorePathsLower
import TournamentHamiltonian.UniformUnitScoreMinors

namespace TournamentHamiltonian
open Filter
open scoped Topology Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def unitScorePathLowerConstant : ℝ :=
  12*Real.exp 1+smallScoreUniformPermanentConstant*principalErrorMomentConstant+1

theorem unitScorePathLowerConstant_pos : 0<unitScorePathLowerConstant := by
  have hc := smallScoreUniformPermanentConstant_pos
  have hm := principalErrorMomentConstant_nonneg
  unfold unitScorePathLowerConstant
  positivity

theorem principal_subset_tail_eventually_le_inverse :
    ∀ᶠ n : ℕ in atTop,subsetTailAt 1 n≤1/(n : ℝ) := by
  have h := scaled_subsetTail_eventually_small (by norm_num : (0 : ℝ)<1) 2 (by norm_num : (0 : ℝ)<1)
  filter_upwards [h] with n hn
  norm_num only at hn
  simp only [one_mul] at hn
  have hs : 1≤Real.sqrt ((n : ℝ)+1) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1 : ℝ)≤n+1)
  have ht : 0≤subsetTailAt 1 n := by
    unfold subsetTailAt
    exact tsum_nonneg (fun k=>mul_nonneg (by positivity) (subsetWeight_nonneg _))
  have hb := mul_le_mul_of_nonneg_right hs ht
  simp only [one_mul] at hb
  exact hb.trans hn

theorem unit_score_pathCount_spectral_lower_uniform :
    ∃ N : ℕ,20≤N ∧ ∀ n : ℕ,N≤n → ∀ T : Tournament n,(∀ i,|score T i|≤1) →
      spectralRatio T-unitScorePathLowerConstant/n≤(pathCount T : ℝ)/meanPaths n := by
  obtain ⟨Nm,hNm,hm⟩ := unit_score_principal_minors_uniform
  obtain ⟨Nt,ht⟩ := eventually_atTop.mp principal_subset_tail_eventually_le_inverse
  refine ⟨max Nm Nt,hNm.trans (le_max_left _ _),?_⟩
  intro n hn T hs
  have hnNm : Nm≤n := by omega
  have hnNt : Nt≤n := by omega
  have hn20 : 20≤n := hNm.trans hnNm
  have hn0 : 0<n := by omega
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn0
  obtain ⟨_hvar,hminors⟩ := hm n hnNm T hs
  have hlower := pathCount_spectral_lower_from_actual_minors T hn0
    smallScoreUniformPermanentConstant (12*Real.exp 1) smallScoreUniformPermanentConstant_pos.le (by positivity)
    (tournament_generating_det_lower_unit_scores_absolute T hn0 hs)
    (fun U hU=>(hminors U hU).1) (fun U hU=>(hminors U hU).2.2)
  have hb : ((12*Real.exp 1+smallScoreUniformPermanentConstant*principalErrorMomentConstant)/n+subsetTailAt 1 n)≤
      unitScorePathLowerConstant/n := by
    apply (add_le_add (le_refl _) (ht n hnNt)).trans_eq
    unfold unitScorePathLowerConstant
    ring
  exact (sub_le_sub_left hb (spectralRatio T)).trans hlower

end TournamentHamiltonian
