import TournamentHamiltonian.PrincipalLowerMoments
import TournamentHamiltonian.SmallScoreGeneratingLower
import TournamentHamiltonian.CrudeSpectralDeterminant

namespace TournamentHamiltonian
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def pathLowerPermanentFactor {n : ℕ} (T : Tournament n) : ℝ := Real.exp (-1)*gaussianFactor T

theorem pathLowerPermanentFactor_bounds {n : ℕ} (T : Tournament n) (hn : 0<n) :
    0≤pathLowerPermanentFactor T ∧ pathLowerPermanentFactor T/2≤1 := by
  obtain ⟨hG,hG2⟩ := gaussianFactor_bounds T hn
  have he : Real.exp (-1)≤1 := Real.exp_le_one_iff.mpr (by norm_num)
  constructor
  · exact mul_nonneg (Real.exp_pos _).le hG.le
  · unfold pathLowerPermanentFactor
    have h := mul_le_mul he hG2.le hG.le (by norm_num : (0 : ℝ)≤1)
    nlinarith

theorem pathCount_spectral_lower_from_actual_minors {n : ℕ} (T : Tournament n)
    (hn : 0<n) (c Cg : ℝ) (hc : 0≤c) (hCg : 0≤Cg)
    (hgen : 2*Real.exp 1*((1 : Matrix (Fin n) (Fin n) ℝ)+(1/(n : ℝ))•signMatrix T).det-Cg/n≤
      ((1 : Matrix (Fin n) (Fin n) ℝ)+(2/(n : ℝ))•(1+adjacency T)).det)
    (hsmall : ∀ U : Finset (Fin n), U.card<subsetCutoff n → c*((U.card : ℝ)+2)^2/n≤1)
    (hper : ∀ U : Finset (Fin n), U.card<subsetCutoff n →
      pathLowerPermanentFactor T*(((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card))*(1-c*((U.card : ℝ)+2)^2/n)≤
        ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n))→Fin n) Subtype.val).permanent) :
    spectralRatio T-((Cg+c*principalErrorMomentConstant)/n+subsetTailAt 1 n)≤
      (pathCount T : ℝ)/meanPaths n := by
  obtain ⟨hQ0,hQ1⟩ := pathLowerPermanentFactor_bounds T hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have htail : 0≤subsetTailAt 1 n := by
    unfold subsetTailAt
    exact tsum_nonneg (fun k=>mul_nonneg (by positivity) (subsetWeight_nonneg _))
  have hE : 0≤(Cg+c*principalErrorMomentConstant)/n+subsetTailAt 1 n := by
    have hM := principalErrorMomentConstant_nonneg
    positivity
  have hbase := pathCount_normalized_lower_from_small_minors T hn
    (pathLowerPermanentFactor T) c hQ0 hc hsmall hper
  have h1 := sub_le_sub_right (sub_le_sub_right hgen (subsetTailAt 1 n))
    (c/n*principalErrorMomentConstant)
  have h2 := (mul_le_mul_of_nonneg_left h1 (by positivity : 0≤pathLowerPermanentFactor T/2)).trans hbase
  have he : Real.exp (-1)*Real.exp 1=1 := by rw [←Real.exp_add]; norm_num
  have hEq : pathLowerPermanentFactor T/2*(2*Real.exp 1*
      ((1 : Matrix (Fin n) (Fin n) ℝ)+(1/(n : ℝ))•signMatrix T).det-Cg/n-
        subsetTailAt 1 n-c/n*principalErrorMomentConstant)=
      spectralRatio T-(pathLowerPermanentFactor T/2)*((Cg+c*principalErrorMomentConstant)/n+subsetTailAt 1 n) := by
    unfold pathLowerPermanentFactor spectralRatio
    calc
      _ = (Real.exp (-1)*Real.exp 1)*gaussianFactor T*
          ((1 : Matrix (Fin n) (Fin n) ℝ)+(1/(n : ℝ))•signMatrix T).det-
            (Real.exp (-1)*gaussianFactor T/2)*((Cg+c*principalErrorMomentConstant)/n+subsetTailAt 1 n) := by ring
      _ = _ := by rw [he]; ring
  rw [hEq] at h2
  have h3 := mul_le_mul_of_nonneg_right hQ1 hE
  simp only [one_mul] at h3
  linarith

theorem tournament_generating_det_lower_unit_scores_absolute {n : ℕ} (T : Tournament n)
    (hn : 0<n) (hs : ∀ i, |score T i|≤1) :
    2*Real.exp 1*((1 : Matrix (Fin n) (Fin n) ℝ)+(1/(n : ℝ))•signMatrix T).det-
      (12*Real.exp 1)/n≤((1 : Matrix (Fin n) (Fin n) ℝ)+(2/(n : ℝ))•(1+adjacency T)).det := by
  have h := tournament_generating_det_lower_unit_scores T hn hs
  have hd := (tournament_skew_kernel_det_lt_five_thirds T hn).le
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have hc : 0≤6*Real.exp 1/(n : ℝ) := by positivity
  have hdet2 : ((1 : Matrix (Fin n) (Fin n) ℝ)+(1/(n : ℝ))•signMatrix T).det≤2 := by linarith
  have he := mul_le_mul_of_nonneg_left hdet2 hc
  have heq : (6*Real.exp 1/(n : ℝ))*2=(12*Real.exp 1)/n := by ring
  rw [heq] at he
  linarith

end TournamentHamiltonian
