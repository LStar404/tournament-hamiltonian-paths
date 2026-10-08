import TournamentHamiltonian.SmallScoreRestorationIdentity
import TournamentHamiltonian.RectangularPermanentUnconditional

open scoped Matrix.Norms.L2Operator

namespace TournamentHamiltonian

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem adjacency_nonprincipal_normalized_restoration {n t : ℕ} (T : Tournament n)
    (hn : 2≤n) (I J : Finset (Fin n)) (hI : I.card=t) (hJ : J.card=t) (ht : t<n)
    (ha : ∀ i, -1<tournamentScorePotential T i ∧ tournamentScorePotential T i<1)
    (hM : 0<matrixEntryMass (preconditionedTournamentDensity T))
    (hQ : 0<matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J))
    (x : (Iᶜ : Finset (Fin n))→ℝ) (y : (Jᶜ : Finset (Fin n))→ℝ) :
    let e := deletedComplementEquiv I J (hI.trans hJ.symm)
    let Y := rectangularExpScaling (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y
    rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J) e =
      (pairedScoreProduct T*(∏ i∈I,pairedLeft (tournamentScorePotential T i))*(∏ j∈J,pairedRight (tournamentScorePotential T j)))*
      (((n-1 : ℝ)/(((n-t : ℕ) : ℝ)*preconditioningDeletionEta (t := t) T I J))^(n-t))*
      (((n-t).factorial : ℝ)/(2 : ℝ)^(n-t))*Real.exp (-((∑ i,x i)+∑ j,y j))*
      ((((n-t : ℕ) : ℝ)^(n-t)/((n-t).factorial : ℝ))*rectangularPermanent Y e) := by
  have hrestore := adjacency_nonprincipal_true_scaling_restoration T hn I J hI hJ ht ha hM.ne' hQ.ne' x y
  have hm : (0 : ℝ)<(n-t : ℕ) := by exact_mod_cast (show 0<n-t by omega)
  have hf : (0 : ℝ)<(n-t).factorial := by exact_mod_cast Nat.factorial_pos (n-t)
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have heta : 0<preconditioningDeletionEta (t := t) T I J := by unfold preconditioningDeletionEta; positivity
  dsimp only at hrestore ⊢
  rw [hrestore]
  rw [div_pow,div_pow,mul_pow,mul_pow]
  field_simp

noncomputable def pairedDeletionScoreFactor {n : ℕ} (T : Tournament n) (I J : Finset (Fin n)) : ℝ :=
  pairedScoreProduct T*(∏ i∈I,pairedLeft (tournamentScorePotential T i))*(∏ j∈J,pairedRight (tournamentScorePotential T j))

noncomputable def preconditioningDeletedMassPower {n t : ℕ} (T : Tournament n) (I J : Finset (Fin n)) : ℝ :=
  ((n-1 : ℝ)/(((n-t : ℕ) : ℝ)*preconditioningDeletionEta (t := t) T I J))^(n-t)

noncomputable def nonprincipalRestorationLog {n t : ℕ} (T : Tournament n) (I J : Finset (Fin n))
    (x : (Iᶜ : Finset (Fin n))→ℝ) (y : (Jᶜ : Finset (Fin n))→ℝ) : ℝ :=
  Real.log (pairedDeletionScoreFactor T I J)+(Real.log (preconditioningDeletedMassPower (t := t) T I J)+1)-
    ((∑ i,x i)+∑ j,y j)+
    (Real.log (gramGaussian (rectangularExpScaling
      (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y-rectangularAverageMatrix _ _))-
      Real.log (gaussianFactor T))

theorem adjacency_nonprincipal_gaussian_error_from_actual_budgets {n t : ℕ} (T : Tournament n)
    (hn : 2≤n) (I J : Finset (Fin n)) (hI : I.card=t) (hJ : J.card=t) (ht : t<n)
    (ha : ∀ i, -1<tournamentScorePotential T i ∧ tournamentScorePotential T i<1)
    (hM : 0<matrixEntryMass (preconditionedTournamentDensity T))
    (hQ : 0<matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J))
    (x : (Iᶜ : Finset (Fin n))→ℝ) (y : (Jᶜ : Finset (Fin n))→ℝ)
    (E r : ℝ) (hr : 0≤r) (hE : E≤1)
    (hgap : ‖rectangularExpScaling (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y-
      rectangularAverageMatrix _ _‖<1)
    (herror : |(((n-t : ℕ) : ℝ)^(n-t)/((n-t).factorial : ℝ))*
      rectangularPermanent (rectangularExpScaling (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y)
        (deletedComplementEquiv I J (hI.trans hJ.symm))-
      gramGaussian (rectangularExpScaling (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y-
        rectangularAverageMatrix _ _)|≤r)
    (hlog : |nonprincipalRestorationLog (t := t) T I J x y|≤E) :
    |rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J) (deletedComplementEquiv I J (hI.trans hJ.symm))-
      Real.exp (-1)*gaussianFactor T*(((n-t).factorial : ℝ)/(2 : ℝ)^(n-t))|≤
      Real.exp (-1)*gaussianFactor T*(((n-t).factorial : ℝ)/(2 : ℝ)^(n-t))*(3*r+2*E) := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hm0 : (0 : ℝ)<(n-t : ℕ) := by exact_mod_cast (show 0<n-t by omega)
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have heta : 0<preconditioningDeletionEta (t := t) T I J := by unfold preconditioningDeletionEta; positivity
  have hP : 0<preconditioningDeletedMassPower (t := t) T I J := by
    unfold preconditioningDeletedMassPower
    apply pow_pos
    exact div_pos (by linarith) (mul_pos hm0 heta)
  have hS : 0<pairedDeletionScoreFactor T I J := by
    unfold pairedDeletionScoreFactor
    have hG : 0<pairedScoreProduct T := by
      unfold pairedScoreProduct
      apply Finset.prod_pos
      intro i _
      have h1 : 0<1+tournamentScorePotential T i := by linarith [(ha i).1]
      have h2 : 0<1-tournamentScorePotential T i := by linarith [(ha i).2]
      nlinarith [mul_pos h1 h2]
    have hL : 0<∏ i∈I,pairedLeft (tournamentScorePotential T i) := by
      apply Finset.prod_pos
      intro i _
      exact inv_pos.mpr (by linarith [(ha i).1])
    have hR : 0<∏ j∈J,pairedRight (tournamentScorePotential T j) := by
      apply Finset.prod_pos
      intro j _
      exact inv_pos.mpr (by linarith [(ha j).2])
    positivity
  have hD := (gaussianFactor_bounds T (by omega)).1
  let W := rectangularExpScaling (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y-
    rectangularAverageMatrix (Iᶜ : Finset (Fin n)) (Jᶜ : Finset (Fin n))
  have hGc := gramGaussian_one_le_of_gap W hgap
  have hGdec : @gramGaussian _ _ _ _ (Classical.decEq _) W = gramGaussian W := by congr 1
  rw [hGdec] at hGc
  have hG : 1 ≤ gramGaussian W := hGc
  change |Real.log (pairedDeletionScoreFactor T I J)+(Real.log (preconditioningDeletedMassPower (t := t) T I J)+1)-
    ((∑ i,x i)+∑ j,y j)+
    (Real.log (gramGaussian (rectangularExpScaling (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y-rectangularAverageMatrix _ _))-
      Real.log (gaussianFactor T))|≤E at hlog
  have h := gaussian_restoration_log_error (pairedDeletionScoreFactor T I J)
    (preconditioningDeletedMassPower (t := t) T I J) (((n-t).factorial : ℝ)/(2 : ℝ)^(n-t))
    ((∑ i,x i)+∑ j,y j)
    ((((n-t : ℕ) : ℝ)^(n-t)/((n-t).factorial : ℝ))*
      rectangularPermanent (rectangularExpScaling (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y)
        (deletedComplementEquiv I J (hI.trans hJ.symm)))
    (gramGaussian (rectangularExpScaling (normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) x y-rectangularAverageMatrix _ _))
    (gaussianFactor T) E r
    hS hP (by positivity) hG hD hr herror hlog hE
  rw [adjacency_nonprincipal_normalized_restoration T hn I J hI hJ ht ha hM hQ x y]
  exact h

end TournamentHamiltonian
