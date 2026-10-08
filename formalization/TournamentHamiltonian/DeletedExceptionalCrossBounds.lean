import TournamentHamiltonian.AmbientCoreWeights
import TournamentHamiltonian.DeletedExceptionalProfiles

/-! Uniform actual paired cross suppression after every short core deletion. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter

theorem actual_deleted_exceptional_cross_bounds :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
      ∀ U : Finset (Fin n), U.card < subsetCutoff n →
      ∀ x ∈ exceptionalVertices T,
      let M := (exceptionalVertices T ∪ U)ᶜ
      let u := 2 / (M.card : ℝ) * ∑ j ∈ M, adjacency T x j * ambientCoreRight T M j
      let v := 2 / (M.card : ℝ) * ∑ j ∈ M, ambientCoreLeft T M j * adjacency T j x
      0 ≤ u ∧ 0 ≤ v ∧ u ≤ 3 ∧ v ≤ 3 ∧ u * v ≤ 1 / 4 := by
  filter_upwards [ambient_deleted_core_weight_budgets, short_deleted_exceptional_core_uniform_dense,
    exceptional_cross_profiles_uniform_eventually, short_cutoff_eventually_small]
    with n hweight hcore hbudget hn T hV U hU x hx
  let D := exceptionalVertices T ∪ U
  let M := Dᶜ
  have hn2 : 2 ≤ n := by omega
  have hN0 : 0 < M.card := by
    have hc := (hcore T hV U hU).1
    dsimp [M, D]
    omega
  obtain ⟨hl, hr, hdl, hdr⟩ := hweight T hV U hU
  have hb : 0 ≤ exceptionalCrossBeta n := by unfold exceptionalCrossBeta; positivity
  have hp := deleted_exceptional_weighted_cross_pair T hn2 D x hx
    (Finset.mem_union_left U hx) hN0 (ambientCoreLeft T M) (ambientCoreRight T M)
    (exceptionalCrossBeta n) hb hl hr hdl hdr
  have hd : (D.card : ℝ) ≤ 401 * Real.log (n : ℝ) := by
    have hf := exceptionalVertices_card_le_log T hn2 hV
    have hk : (U.card : ℝ) ≤ Real.log (n : ℝ) :=
      (by exact_mod_cast hU.le : (U.card : ℝ) ≤ subsetCutoff n).trans hn.2.1
    have hu : (D.card : ℝ) ≤ (exceptionalVertices T).card + U.card := by
      dsimp [D]
      exact_mod_cast Finset.card_union_le (exceptionalVertices T) U
    linarith
  have hN := (hcore T hV U hU).2.1
  have hc := hbudget (D.card : ℝ) (M.card : ℝ) (exceptionalCrossBeta n)
    (by positivity) hd hN hb le_rfl
  exact ⟨hp.1, hp.2.1, hp.2.2.1.trans hc.2, hp.2.2.2.1.trans hc.2,
    hp.2.2.2.2.trans hc.1⟩

end TournamentHamiltonian
