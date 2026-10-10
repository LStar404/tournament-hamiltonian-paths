import TournamentHamiltonian.UniformPermanentFromActivities

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

/-- The two remaining graph estimates, on actual centered graph coefficients.
This records a proof obligation, not an axiom or an analytic estimate. -/
structure ActualCoreActivities (B : Matrix ι ι ℝ) (C q : ℝ) : Prop where
  first : (∑ k ∈ Finset.range (Nat.floor (permanentWindowFraction C q * Fintype.card ι) + 1),
    |actualCoreExcessCoefficient B 1 k| * permanentAnalyticRadius q ^ k) ≤
      permanentFirstExcessBudget C q / Fintype.card ι
  excess : ∀ j ∈ Finset.Icc 2 (Nat.floor (permanentWindowFraction C q * Fintype.card ι)),
    (∑ k ∈ Finset.range (Nat.floor (permanentWindowFraction C q * Fintype.card ι) + 1),
      |actualCoreExcessCoefficient B j k| * permanentAnalyticRadius q ^ k) ≤
        excessWindowTerm (permanentExcessBudget C q) (Fintype.card ι) j

theorem uniform_permanent_approximation_of_activity_predicate (E : Matrix ι ι ℝ)
    (hE : DoublyCentered E) (hp : 0 < Fintype.card ι) (C q : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1) (hentry : ∀ i j, |E i j| ≤ C)
    (hZ : ‖(Fintype.card ι : ℝ)⁻¹ • E‖ ≤ q)
    (hactivity : ActualCoreActivities ((Fintype.card ι : ℝ)⁻¹ • E) C q) :
    |(Matrix.permanent (fun i j => 1 + E i j)) / ((Fintype.card ι).factorial : ℝ) -
        gramGaussian ((Fintype.card ι : ℝ)⁻¹ • E)| ≤
      uniformPermanentActivityConstant C q / Fintype.card ι :=
  uniform_permanent_approximation_of_actual_activities E hE hp C q hC hq hq1 hentry hZ
    hactivity.first hactivity.excess

end TournamentHamiltonian
