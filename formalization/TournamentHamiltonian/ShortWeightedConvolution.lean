import TournamentHamiltonian.WeightedPrincipalGenerating
import TournamentHamiltonian.DeletionFactorial

/-! Actual short Hamiltonian convolution with paired weights. The factorial
correction is summed against a second subset moment, keeping an absolute O(1/n)
error instead of losing a cutoff squared factor. -/
namespace TournamentHamiltonian
open scoped Classical
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem exp_sub_one_le_self_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_nonneg x)
  have he : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  rw [he] at h
  nlinarith

theorem shortConvolution_le_weighted_mass {n : ℕ} (T : Tournament n) (K : ℕ)
    (hn : 0 < n) (hK : 2 * K ≤ n) (hsmall : 2 * (K : ℝ) ^ 2 / n ≤ 1)
    (Q : ℝ) (hQ : 0 ≤ Q) (w : Fin n → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw0 : ∀ i, 0 ≤ w i) (hwW : ∀ i, w i ≤ W)
    (hper : ∀ U : Finset (Fin n), U.card < K →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) * ∏ i ∈ U, w i) :
    shortConvolution T K / meanPaths n ≤
      (Q / 2) * (weightedPrincipalMass T w +
        (2 * Real.exp 1 / n) * ∑' k, subsetMoment W 2 k) := by
  let Z : ℝ := (n.factorial : ℝ) / (2 : ℝ) ^ n
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  have hmZ : meanPaths n = 2 * Z := by
    dsimp [Z]
    simpa only [mul_div_assoc] using meanPaths_eq_twice_normalization n (by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let b : Finset (Fin n) → ℝ := fun U =>
    (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det * ∏ i ∈ U, w i
  have hb : ∀ U, 0 ≤ b U := by
    intro U
    have hd := (principal_weight_pos T U).le
    have hp := Finset.prod_nonneg (s := U) (fun i _ => hw0 i)
    dsimp [b]
    positivity
  have hloc (U : Finset (Fin n)) :
      (if U.card < K then convolutionTerm T U else 0) / meanPaths n ≤
        (Q / 2) * (b U + (2 * Real.exp 1 / n) * ((U.card : ℝ) ^ 2 * b U)) := by
    have hpw := Finset.prod_nonneg (s := U) (fun i _ => hw0 i)
    have hbU := hb U
    by_cases hs : U.card < K
    · simp only [hs, ite_true]
      have hkN : 2 * U.card ≤ n := by omega
      have hkK : (U.card : ℝ) ≤ K := by exact_mod_cast hs.le
      have hx : 2 * (U.card : ℝ) ^ 2 / n ≤ 1 := by
        apply le_trans _ hsmall
        apply div_le_div_of_nonneg_right _ hn0.le
        nlinarith [show (0 : ℝ) ≤ U.card by positivity]
      have he : Real.exp (2 * (U.card : ℝ) ^ 2 / n) ≤
          1 + (2 * Real.exp 1 / n) * (U.card : ℝ) ^ 2 := by
        have ha := exp_sub_one_le_self_mul_exp (2 * (U.card : ℝ) ^ 2 / n)
        have hb' := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx)
          (by positivity : 0 ≤ 2 * (U.card : ℝ) ^ 2 / n)
        have heq : (2 * (U.card : ℝ) ^ 2 / n) * Real.exp 1 =
            (2 * Real.exp 1 / n) * (U.card : ℝ) ^ 2 := by ring
        rw [heq] at hb'
        linarith
      have hf := (convolution_factorial_ratio_le n U.card hn hkN).trans
        (mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ (2 / (n : ℝ)) ^ U.card))
      have hd := (principal_weight_pos T U).le
      calc
        convolutionTerm T U / meanPaths n ≤
            (Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) * ∏ i ∈ U, w i) *
              (principalWeightMatrix T U).det / meanPaths n := by
          apply div_le_div_of_nonneg_right _ hm.le
          unfold convolutionTerm
          calc
            _ ≤ (principalWeightMatrix T U).det *
                (Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) * ∏ i ∈ U, w i) :=
              mul_le_mul_of_nonneg_left (hper U hs) hd
            _ = _ := mul_comm _ _
        _ = (Q / 2 * (principalWeightMatrix T U).det * ∏ i ∈ U, w i) *
            ((((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) / Z) := by rw [hmZ]; ring
        _ ≤ (Q / 2 * (principalWeightMatrix T U).det * ∏ i ∈ U, w i) *
            ((1 + (2 * Real.exp 1 / n) * (U.card : ℝ) ^ 2) * (2 / (n : ℝ)) ^ U.card) :=
          mul_le_mul_of_nonneg_left hf (by positivity)
        _ = _ := by dsimp [b]; ring
    · simp only [hs, ite_false, zero_div]
      positivity
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun U _ => hloc U)
  change shortConvolution T K / meanPaths n ≤ _
  have heq : shortConvolution T K / meanPaths n =
      ∑ U : Finset (Fin n), (if U.card < K then convolutionTerm T U else 0) / meanPaths n := by
    rw [shortConvolution, Finset.sum_div]
  rw [heq]
  apply hs.trans
  have hmoment := weighted_principal_powerMoment_le T hn 2 w W hW hw0 hwW
  have heqmoment : (∑ U : Finset (Fin n), (U.card : ℝ) ^ 2 * b U) =
      ∑ U : Finset (Fin n), (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det *
        (U.card : ℝ) ^ 2 * ∏ i ∈ U, w i := by
    apply Finset.sum_congr rfl
    intro U _
    dsimp [b]
    ring
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, heqmoment]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ Q / 2)
  apply add_le_add (le_refl _)
  exact mul_le_mul_of_nonneg_left hmoment (by positivity)

end TournamentHamiltonian
