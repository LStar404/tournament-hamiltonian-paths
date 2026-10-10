import TournamentHamiltonian.ExceptionalCoreAssembly
import TournamentHamiltonian.UniformPairedPermanentGaussian
import TournamentHamiltonian.PairedPermanentCoarseBudget

/-! Unconditional exclusion of actual large scores. Every core-minor estimate is
obtained from the proved paired/nonprincipal theorem for the actual induced core. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem exists_uniformExceptionalCoreMinorBound :
    ∃ K : ℝ, 0 < K ∧ HasUniformExceptionalCoreMinorBound (exceptionalMinorError K) := by
  obtain ⟨K, hK, Np, hNp, hp⟩ := adjacency_nonprincipal_gaussian_uniform_log
    (A := 1200) (B := 800) (a0 := 19 / 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨K, hK, ?_⟩
  filter_upwards [short_deleted_exceptional_core_uniform_dense, eventually_ge_atTop (2 * Np)]
    with n hdense hn T hV U hU hUF
  dsimp only
  intro s hs I hI J hJ
  let F := exceptionalVertices T
  let M := (F ∪ U)ᶜ
  let S := inducedTournament T M
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hN2, hNhalf, hcap, hτA, hτN⟩ := hdense T hV U hU
  have hNpN : Np ≤ M.card := by
    have hnR : (2 * Np : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [M, F]
    exact_mod_cast (show (Np : ℝ) ≤ (exceptionalVertices T ∪ U)ᶜ.card by linarith)
  have hN0 : (0 : ℝ) < M.card := by exact_mod_cast (show 0 < M.card by dsimp [M, F]; omega)
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.log (M.card : ℝ) := by
    have h := Real.log_le_log hn0 (show (n : ℝ) ≤ 2 * M.card by dsimp [M, F]; linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at h
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ M.card by exact_mod_cast hN2)
    linarith
  have hf := exceptionalVertices_card_le_log T hn2 hV
  have htA : ((F.card - s : ℕ) : ℝ) ≤ 400 * Real.log (n : ℝ) := by
    have hsf : ((F.card - s : ℕ) : ℝ) ≤ F.card := by exact_mod_cast Nat.sub_le F.card s
    dsimp [F] at hsf
    linarith
  have htN : ((F.card - s : ℕ) : ℝ) ≤ 800 * Real.log (M.card : ℝ) := by linarith
  have hτ : 0 ≤ scoreVariance S := scoreVariance_nonneg S
  have herror := pairedPermanentErrorBudget_deleted_log_le (show 1 ≤ n by omega)
    (show 1 ≤ M.card by dsimp [M, F]; omega) hNhalf (scoreVariance S) K hτ hK.le hτA htA
  apply ambient_core_minor_bound_of_rectangular T M (F.card - s)
    (2 * Real.exp (-1) * Real.exp (exceptionalMinorError K n)) _ I hI J hJ
  intro P Q hP hQ
  let e := deletedComplementEquiv P Q (hP.trans hQ.symm)
  have hu := hp M.card (F.card - s) hNpN S hcap hτN htN P Q hP hQ
  have hGamma : pairedScoreProduct S ≤ 1 :=
    (pairedScoreProduct_le_exp S (fun i => (hcap i).trans (by norm_num))).trans
      (Real.exp_le_one_iff.mpr (by linarith))
  have hG := gaussianFactor_bounds S (show 0 < M.card by dsimp [M, F]; omega)
  have hGG : pairedScoreProduct S * gaussianFactor S ≤ 2 :=
    (mul_le_mul hGamma hG.2.le hG.1.le (by norm_num)).trans_eq (by ring)
  have hexp : Real.exp (-1 + K * pairedPermanentErrorBudget M.card (F.card - s) (scoreVariance S)) ≤
      Real.exp (-1 + exceptionalMinorError K n) := Real.exp_le_exp.mpr (by linarith)
  have hmul := mul_le_mul hGG hexp (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have hleft : 0 ≤ ∏ i ∈ P, pairedLeft (tournamentScorePotential S i) := by
    apply Finset.prod_nonneg
    intro i _
    exact pairedLeft_nonneg _ (by have h := (abs_le.mp (hcap i)).1; linarith)
  have hright : 0 ≤ ∏ j ∈ Q, pairedRight (tournamentScorePotential S j) := by
    apply Finset.prod_nonneg
    intro j _
    exact pairedRight_nonneg _ (by have h := (abs_le.mp (hcap j)).2; linarith)
  have hscale : 0 ≤ (((M.card - (F.card - s)).factorial : ℝ) / (2 : ℝ) ^ (M.card - (F.card - s))) *
      (∏ i ∈ P, pairedLeft (tournamentScorePotential S i)) *
      (∏ j ∈ Q, pairedRight (tournamentScorePotential S j)) := by positivity
  have hbound := mul_le_mul_of_nonneg_right hmul hscale
  have hactual : rectangularPermanent (nonprincipalSubmatrix (adjacency S) P Q) e ≤
      (pairedScoreProduct S * gaussianFactor S *
        Real.exp (-1 + K * pairedPermanentErrorBudget M.card (F.card - s) (scoreVariance S))) *
        ((((M.card - (F.card - s)).factorial : ℝ) / (2 : ℝ) ^ (M.card - (F.card - s))) *
          (∏ i ∈ P, pairedLeft (tournamentScorePotential S i)) *
          (∏ j ∈ Q, pairedRight (tournamentScorePotential S j))) := by
    convert hu using 1
    ring
  apply hactual.trans
  convert hbound using 1
  rw [Real.exp_add]
  ring

theorem actual_largeScore_eventually_lt_mean :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      1 ≤ (exceptionalVertices T).card → (pathCount T : ℝ) < meanPaths n := by
  obtain ⟨K, _, hcore⟩ := exists_uniformExceptionalCoreMinorBound
  exact largeScore_eventually_lt_mean_of_core_minor_bound (exceptionalMinorError K)
    (exceptionalMinorError_tendsto_zero K) hcore

end TournamentHamiltonian
