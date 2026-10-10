import TournamentHamiltonian.LowerDeletionFactorial
import TournamentHamiltonian.ShortWeightedConvolution

namespace TournamentHamiltonian
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

noncomputable def shortPrincipalMass {n : ℕ} (T : Tournament n) (K : ℕ) : ℝ :=
  ∑ U : Finset (Fin n), if U.card<K then (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det else 0

noncomputable def shortPrincipalErrorMoment {n : ℕ} (T : Tournament n) (K : ℕ) : ℝ :=
  ∑ U : Finset (Fin n), if U.card<K then
    (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det*((U.card : ℝ)+2)^2 else 0

theorem shortConvolution_lower_from_minors {n : ℕ} (T : Tournament n) (K : ℕ)
    (hn : 0<n) (Q c : ℝ) (hQ : 0≤Q)
    (hsmall : ∀ U : Finset (Fin n), U.card<K → c*((U.card : ℝ)+2)^2/n≤1)
    (hper : ∀ U : Finset (Fin n), U.card<K →
      Q*(((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card))*(1-c*((U.card : ℝ)+2)^2/n)≤
        ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n))→Fin n) Subtype.val).permanent) :
    Q/2*(shortPrincipalMass T K-c/n*shortPrincipalErrorMoment T K)≤shortConvolution T K/meanPaths n := by
  let Z : ℝ := (n.factorial : ℝ)/(2 : ℝ)^n
  have hZ : 0<Z := by dsimp [Z]; positivity
  have hm : 0<meanPaths n := by unfold meanPaths; positivity
  have hmZ : meanPaths n=2*Z := by
    dsimp [Z]
    simpa only [mul_div_assoc] using meanPaths_eq_twice_normalization n (by omega)
  have hloc (U : Finset (Fin n)) :
      (if U.card<K then Q/2*((2/(n : ℝ))^U.card*(principalWeightMatrix T U).det)*
        (1-c*((U.card : ℝ)+2)^2/n) else 0)≤
      (if U.card<K then convolutionTerm T U else 0)/meanPaths n := by
    by_cases hs : U.card<K
    · simp only [hs,ite_true]
      have hk : U.card≤n := by simpa using U.card_le_univ
      have hd := (principal_weight_pos T U).le
      have hr : 0≤1-c*((U.card : ℝ)+2)^2/n := by linarith [hsmall U hs]
      have hfac := convolution_factorial_ratio_ge n U.card hn hk
      have hlow := mul_le_mul_of_nonneg_left hfac
        (show 0≤Q/2*(principalWeightMatrix T U).det*(1-c*((U.card : ℝ)+2)^2/n) by positivity)
      calc
        _ = (Q/2*(principalWeightMatrix T U).det*(1-c*((U.card : ℝ)+2)^2/n))*(2/(n : ℝ))^U.card := by ring
        _ ≤ (Q/2*(principalWeightMatrix T U).det*(1-c*((U.card : ℝ)+2)^2/n))*
            ((((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card))/Z) := hlow
        _ = (principalWeightMatrix T U).det*
            (Q*(((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card))*(1-c*((U.card : ℝ)+2)^2/n))/meanPaths n := by rw [hmZ]; ring
        _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hper U hs) hd) hm.le
    · simp [hs]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun U _ => hloc U)
  rw [←Finset.sum_div] at hsum
  change _≤shortConvolution T K/meanPaths n at hsum
  apply le_trans _ hsum
  apply le_of_eq
  rw [shortPrincipalMass,shortPrincipalErrorMoment,Finset.mul_sum,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  split_ifs <;>ring

theorem shortConvolution_le_pathCount {n : ℕ} (T : Tournament n) (K : ℕ) :
    shortConvolution T K≤(pathCount T : ℝ) := by
  have h := shortConvolution_add_longConvolution T K
  linarith [longConvolution_nonneg T K]

end TournamentHamiltonian
