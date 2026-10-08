import TournamentHamiltonian.ExceptionalConvolution
import TournamentHamiltonian.CoreGenerating
import TournamentHamiltonian.DeletionFactorial

/-! Finite assembly of the actual short convolution disjoint from exceptional vertices. -/
namespace TournamentHamiltonian
open scoped Classical

theorem disjointShortConvolution_le_generating {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (K : ℕ) (hn : 0 < n) (hK : 2 * K ≤ n) (Q : ℝ) (hQ : 0 ≤ Q)
    (hper : ∀ U : Finset (Fin n), U.card < K → Disjoint U F →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) :
    disjointShortConvolution T F K / meanPaths n ≤
      (Q / 2) * Real.exp (2 * (K : ℝ) ^ 2 / n) *
        ∑ U ∈ Fᶜ.powerset, (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det := by
  let Z : ℝ := (n.factorial : ℝ) / (2 : ℝ) ^ n
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  have hmZ : meanPaths n = 2 * Z := by
    dsimp [Z]
    simpa only [mul_div_assoc] using meanPaths_eq_twice_normalization n (by omega)
  have hsum : Fᶜ.powerset = (Finset.univ : Finset (Finset (Fin n))).filter (fun U => U ⊆ Fᶜ) := by
    ext U; simp
  rw [disjointShortConvolution, Finset.sum_div, Finset.mul_sum, hsum, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro U _
  have hdet : 0 ≤ (principalWeightMatrix T U).det := (principal_weight_pos T U).le
  by_cases hshort : U.card < K ∧ Disjoint U F
  · have hsub : U ⊆ Fᶜ := by
      intro x hx
      exact Finset.mem_compl.mpr (fun hf => Finset.disjoint_left.mp hshort.2 hx hf)
    simp only [hshort, hsub, ite_true]
    have hkK : (U.card : ℝ) ≤ K := by exact_mod_cast hshort.1.le
    have hkN : 2 * U.card ≤ n := by omega
    have hf := convolution_factorial_ratio_le n U.card hn hkN
    have hexp : Real.exp (2 * (U.card : ℝ) ^ 2 / n) ≤ Real.exp (2 * (K : ℝ) ^ 2 / n) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ (n : ℝ))
      nlinarith [show (0 : ℝ) ≤ U.card by positivity]
    have hf' := hf.trans (mul_le_mul_of_nonneg_right hexp (by positivity : 0 ≤ (2 / (n : ℝ)) ^ U.card))
    calc
      convolutionTerm T U / meanPaths n ≤
          (Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) * (principalWeightMatrix T U).det / meanPaths n := by
        apply div_le_div_of_nonneg_right _ hm.le
        unfold convolutionTerm
        have h := mul_le_mul_of_nonneg_right (hper U hshort.1 hshort.2) hdet
        simpa only [mul_comm] using h
      _ = (Q / 2 * (principalWeightMatrix T U).det) *
          ((((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) / Z) := by
        rw [hmZ]
        ring
      _ ≤ (Q / 2 * (principalWeightMatrix T U).det) *
          (Real.exp (2 * (K : ℝ) ^ 2 / n) * (2 / (n : ℝ)) ^ U.card) :=
        mul_le_mul_of_nonneg_left hf' (mul_nonneg (by positivity) hdet)
      _ = _ := by ring
  · simp only [hshort, ite_false, zero_div]
    split_ifs <;> positivity

theorem disjointShortConvolution_le_core_det {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (K : ℕ) (hn : 0 < n) (hK : 2 * K ≤ n) (Q : ℝ) (hQ : 0 ≤ Q)
    (hper : ∀ U : Finset (Fin n), U.card < K → Disjoint U F →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) :
    disjointShortConvolution T F K / meanPaths n ≤
      Q * Real.exp 1 * Real.exp (2 * (K : ℝ) ^ 2 / n) *
        ((1 : Matrix (Fin Fᶜ.card) (Fin Fᶜ.card) ℝ) +
          (1 / (Fᶜ.card : ℝ)) • signMatrix (inducedTournament T Fᶜ)).det := by
  apply (disjointShortConvolution_le_generating T F K hn hK Q hQ hper).trans
  have h := mul_le_mul_of_nonneg_left (core_principalWeight_generating_le T Fᶜ hn)
    (by positivity : 0 ≤ (Q / 2) * Real.exp (2 * (K : ℝ) ^ 2 / n))
  convert h using 1
  ring

theorem disjointShortConvolution_le_spectral {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (K : ℕ) (hn : 0 < n) (hK : 2 * K ≤ n) (hN : 0 < Fᶜ.card) (c E : ℝ) (hc : 0 ≤ c)
    (hper : ∀ U : Finset (Fin n), U.card < K → Disjoint U F →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        (Real.exp (-1) * gaussianFactor (inducedTournament T Fᶜ) * c ^ F.card * Real.exp E) *
          (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) :
    disjointShortConvolution T F K / meanPaths n ≤
      spectralRatio (inducedTournament T Fᶜ) * c ^ F.card *
        Real.exp (E + 2 * (K : ℝ) ^ 2 / n) := by
  have hG := (gaussianFactor_bounds (inducedTournament T Fᶜ) hN).1.le
  have h := disjointShortConvolution_le_core_det T F K hn hK
    (Real.exp (-1) * gaussianFactor (inducedTournament T Fᶜ) * c ^ F.card * Real.exp E)
    (by positivity) hper
  convert h using 1
  rw [spectralRatio, Real.exp_add, Real.exp_neg]
  field_simp

theorem pathCount_le_spectral_meeting_long {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (K : ℕ) (hn : 0 < n) (hK : 2 * K ≤ n) (hN : 0 < Fᶜ.card) (c E : ℝ) (hc : 0 ≤ c)
    (hper : ∀ U : Finset (Fin n), U.card < K → Disjoint U F →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        (Real.exp (-1) * gaussianFactor (inducedTournament T Fᶜ) * c ^ F.card * Real.exp E) *
          (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) :
    (pathCount T : ℝ) / meanPaths n ≤
      spectralRatio (inducedTournament T Fᶜ) * c ^ F.card * Real.exp (E + 2 * (K : ℝ) ^ 2 / n) +
        meetingShortConvolution T F K / meanPaths n + longConvolution T K / meanPaths n := by
  rw [pathCount_eq_disjoint_meeting_long T F K, add_div, add_div]
  exact add_le_add (add_le_add
    (disjointShortConvolution_le_spectral T F K hn hK hN c E hc hper) (le_refl _)) (le_refl _)

theorem exceptional_pathCount_lt_mean_of_core_bound {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (K : ℕ) (hn : 0 < n) (hK : 2 * K ≤ n) (hN : 0 < Fᶜ.card) (hF : 1 ≤ F.card)
    (c E : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1 / 4)
    (hE : Real.exp (E + 2 * (K : ℝ) ^ 2 / n) ≤ 6 / 5)
    (hm : meetingShortConvolution T F K / meanPaths n ≤ 1 / 25)
    (hl : longConvolution T K / meanPaths n ≤ 1 / 25)
    (hper : ∀ U : Finset (Fin n), U.card < K → Disjoint U F →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        (Real.exp (-1) * gaussianFactor (inducedTournament T Fᶜ) * c ^ F.card * Real.exp E) *
          (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) :
    (pathCount T : ℝ) < meanPaths n := by
  have hrho := spectralRatio_bounds (inducedTournament T Fᶜ) hN
  have hpow : c ^ F.card ≤ 1 / 4 := by
    have h := pow_le_pow_of_le_one hc (by linarith : c ≤ 1) hF
    exact (show c ^ F.card ≤ c by simpa only [pow_one] using h).trans hc1
  have h1 := mul_le_mul hrho.2 hpow (pow_nonneg hc _) (by norm_num : (0 : ℝ) ≤ 3)
  have h2 := mul_le_mul h1 hE (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 * (1 / 4))
  have h := pathCount_le_spectral_meeting_long T F K hn hK hN c E hc hper
  have hbound : (pathCount T : ℝ) / meanPaths n ≤ 49 / 50 := by nlinarith
  have hm0 : 0 < meanPaths n := by unfold meanPaths; positivity
  exact (div_lt_one hm0).mp (lt_of_le_of_lt hbound (by norm_num))

end TournamentHamiltonian
