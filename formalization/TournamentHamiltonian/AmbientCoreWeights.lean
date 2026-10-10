import TournamentHamiltonian.TournamentWeightDisplacement
import TournamentHamiltonian.DeletedExceptionalCore
import TournamentHamiltonian.ExceptionalBudgets

/-! Actual paired core weights extended to ambient vertices and their uniform budgets. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter

noncomputable def ambientCorePotential {n : ℕ} (T : Tournament n) (M : Finset (Fin n)) (x : Fin n) : ℝ :=
  if x ∈ M then subsetScore T M x / ((M.card : ℝ) - 1) else 0
noncomputable def ambientCoreLeft {n : ℕ} (T : Tournament n) (M : Finset (Fin n)) (x : Fin n) : ℝ :=
  pairedLeft (ambientCorePotential T M x)
noncomputable def ambientCoreRight {n : ℕ} (T : Tournament n) (M : Finset (Fin n)) (x : Fin n) : ℝ :=
  pairedRight (ambientCorePotential T M x)

theorem ambientCorePotential_equiv {n : ℕ} (T : Tournament n) (M : Finset (Fin n)) (i : Fin M.card) :
    ambientCorePotential T M (subsetVertexEquiv M i) =
      tournamentScorePotential (inducedTournament T M) i := by
  rw [tournamentScorePotential, score_inducedTournament]
  simp only [ambientCorePotential, (subsetVertexEquiv M i).property, ite_true]

theorem ambientCorePotential_sum {n : ℕ} (T : Tournament n) (M : Finset (Fin n)) (f : ℝ → ℝ) :
    (∑ x ∈ M, f (ambientCorePotential T M x)) =
      ∑ i, f (tournamentScorePotential (inducedTournament T M) i) := by
  have h := (subsetVertexEquiv M).sum_comp (fun x : M => f (ambientCorePotential T M x))
  simp_rw [ambientCorePotential_equiv] at h
  rw [Finset.sum_coe_sort M (fun x => f (ambientCorePotential T M x))] at h
  exact h.symm

theorem ambientCorePotential_cap {n : ℕ} (T : Tournament n) (M : Finset (Fin n))
    (a0 : ℝ) (ha0 : 0 ≤ a0) (ha : ∀ i, |tournamentScorePotential (inducedTournament T M) i| ≤ a0) :
    ∀ x, |ambientCorePotential T M x| ≤ a0 := by
  intro x
  by_cases hx : x ∈ M
  · let i := (subsetVertexEquiv M).symm ⟨x, hx⟩
    have h := ambientCorePotential_equiv T M i
    have hi : (subsetVertexEquiv M i : Fin n) = x := by
      exact congrArg Subtype.val ((subsetVertexEquiv M).apply_symm_apply ⟨x, hx⟩)
    rw [hi] at h
    rw [h]
    exact ha i
  · simp only [ambientCorePotential, hx, ite_false, abs_zero]
    exact ha0

theorem ambientCore_weights_nonneg {n : ℕ} (T : Tournament n) (M : Finset (Fin n))
    (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1)
    (ha : ∀ i, |tournamentScorePotential (inducedTournament T M) i| ≤ a0) :
    (∀ x, 0 ≤ ambientCoreLeft T M x) ∧ (∀ x, 0 ≤ ambientCoreRight T M x) := by
  have hcap := ambientCorePotential_cap T M a0 h0 ha
  constructor
  · intro x
    exact pairedLeft_nonneg _ (by have := (abs_le.mp (hcap x)).1; linarith)
  · intro x
    exact pairedRight_nonneg _ (by have := (abs_le.mp (hcap x)).2; linarith)

theorem ambientCore_weight_displacements {n : ℕ} (T : Tournament n) (M : Finset (Fin n))
    (a0 : ℝ) (h1 : a0 < 1)
    (ha : ∀ i, |tournamentScorePotential (inducedTournament T M) i| ≤ a0) :
    (∑ x ∈ M, |ambientCoreLeft T M x - 1|) ≤ (M.card : ℝ) *
        ((1 / (1 - a0)) * Real.sqrt (scoreVariance (inducedTournament T M) / M.card)) ∧
      (∑ x ∈ M, |ambientCoreRight T M x - 1|) ≤ (M.card : ℝ) *
        ((1 / (1 - a0)) * Real.sqrt (scoreVariance (inducedTournament T M) / M.card)) := by
  change (∑ x ∈ M, |pairedLeft (ambientCorePotential T M x) - 1|) ≤ _ ∧
    (∑ x ∈ M, |pairedRight (ambientCorePotential T M x) - 1|) ≤ _
  rw [ambientCorePotential_sum T M (fun a => |pairedLeft a - 1|),
    ambientCorePotential_sum T M (fun a => |pairedRight a - 1|)]
  exact tournament_paired_weight_displacements _ a0 h1 ha

theorem ambient_deleted_core_weight_budgets :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
      ∀ U : Finset (Fin n), U.card < subsetCutoff n →
      let M := (exceptionalVertices T ∪ U)ᶜ
      (∀ x, 0 ≤ ambientCoreLeft T M x) ∧ (∀ x, 0 ≤ ambientCoreRight T M x) ∧
        (∑ x ∈ M, |ambientCoreLeft T M x - 1|) ≤ (M.card : ℝ) * exceptionalCrossBeta n ∧
        (∑ x ∈ M, |ambientCoreRight T M x - 1|) ≤ (M.card : ℝ) * exceptionalCrossBeta n := by
  filter_upwards [short_deleted_exceptional_core_uniform_dense, eventually_ge_atTop (2 : ℕ)]
    with n hcore hn T hV U hU
  obtain ⟨hM, hMN, hcap, hvar, _⟩ := hcore T hV U hU
  let M := (exceptionalVertices T ∪ U)ᶜ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hM0 : (0 : ℝ) < M.card := by
    dsimp [M]
    exact_mod_cast (show 0 < (exceptionalVertices T ∪ U)ᶜ.card by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hratio : scoreVariance (inducedTournament T M) / M.card ≤ 2400 * Real.log (n : ℝ) / n := by
    apply (div_le_div_of_nonneg_right hvar hM0.le).trans
    have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ 600 * Real.log (n : ℝ))
      (by positivity : 0 < (n : ℝ) / 2) hMN
    apply h.trans
    field_simp
    nlinarith
  have hroot := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio) (by norm_num : (0 : ℝ) ≤ 20)
  have hdisp := ambientCore_weight_displacements T M (19 / 20) (by norm_num) hcap
  rw [show (1 / (1 - (19 / 20 : ℝ))) = 20 by norm_num] at hdisp
  have hm := mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ M.card)
  have hnonneg := ambientCore_weights_nonneg T M (19 / 20) (by norm_num) (by norm_num) hcap
  exact ⟨hnonneg.1, hnonneg.2, hdisp.1.trans hm, hdisp.2.trans hm⟩

end TournamentHamiltonian
