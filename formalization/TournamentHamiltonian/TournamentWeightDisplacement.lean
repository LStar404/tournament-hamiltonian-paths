import TournamentHamiltonian.PairedWeightL1
import TournamentHamiltonian.ExceptionalDegrees

/-! L1 budgets for the actual score preconditioning of the exceptional core. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter

theorem tournament_paired_weight_displacements {n : ℕ} (T : Tournament n) (a0 : ℝ)
    (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    (∑ i, |pairedLeft (tournamentScorePotential T i) - 1|) ≤
        (n : ℝ) * ((1 / (1 - a0)) * Real.sqrt (scoreVariance T / n)) ∧
      (∑ i, |pairedRight (tournamentScorePotential T i) - 1|) ≤
        (n : ℝ) * ((1 / (1 - a0)) * Real.sqrt (scoreVariance T / n)) := by
  have heq : Real.sqrt ((Fintype.card (Fin n) : ℝ) * ∑ i, tournamentScorePotential T i ^ 2) /
      (1 - a0) = (n : ℝ) * ((1 / (1 - a0)) * Real.sqrt (scoreVariance T / n)) := by
    rw [Fintype.card_fin, ← scoreVariance, sqrt_mul_eq_mul_sqrt_div (n : ℝ) (scoreVariance T)
      (by positivity) (scoreVariance_nonneg T)]
    ring
  constructor
  · exact (pairedLeft_total_displacement_le (tournamentScorePotential T) a0 h1 ha).trans_eq heq
  · exact (pairedRight_total_displacement_le (tournamentScorePotential T) a0 h1 ha).trans_eq heq

theorem exceptional_core_weight_displacements_eventually :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
      let U := (exceptionalVertices T)ᶜ
      let G := inducedTournament T U
      let beta := 20 * Real.sqrt (1200 * Real.log (U.card : ℝ) / U.card)
      (∑ i, |pairedLeft (tournamentScorePotential G i) - 1|) ≤ (U.card : ℝ) * beta ∧
        (∑ i, |pairedRight (tournamentScorePotential G i) - 1|) ≤ (U.card : ℝ) * beta := by
  filter_upwards [exceptional_core_uniform_dense] with n hn T hV
  obtain ⟨hN, hcap, hvar⟩ := hn T hV
  let U := (exceptionalVertices T)ᶜ
  let G := inducedTournament T U
  have h := tournament_paired_weight_displacements G (19 / 20) (by norm_num) hcap
  rw [show (1 / (1 - (19 / 20 : ℝ))) = 20 by norm_num] at h
  have hroot := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hvar (by positivity : (0 : ℝ) ≤ U.card))
  have hm := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ (U.card : ℝ) * 20)
  constructor <;> first
  | exact h.1.trans (by simpa only [mul_assoc] using hm)
  | exact h.2.trans (by simpa only [mul_assoc] using hm)

end TournamentHamiltonian
