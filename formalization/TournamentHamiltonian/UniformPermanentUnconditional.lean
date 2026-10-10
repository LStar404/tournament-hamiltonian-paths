import TournamentHamiltonian.ActualCoreActivityPredicate

open scoped BigOperators Matrix.Norms.L2Operator

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

/-- The actual normalized permanent approximation, with all graph activities discharged. -/
theorem uniform_permanent_approximation_from_matrix_bounds (E : Matrix ι ι ℝ)
    (hE : DoublyCentered E) (hp : 0<Fintype.card ι) (C q : ℝ)
    (hC : 0≤C) (hq : 0≤q) (hq1 : q<1) (hentry : ∀ i j, |E i j|≤C)
    (hZ : ‖(Fintype.card ι : ℝ)⁻¹ • E‖≤q) :
    |Matrix.permanent (fun i j => 1+E i j)/((Fintype.card ι).factorial : ℝ)-
      gramGaussian ((Fintype.card ι : ℝ)⁻¹ • E)|≤
        uniformPermanentActivityConstant C q/Fintype.card ι := by
  have hn : (0 : ℝ)<Fintype.card ι := by exact_mod_cast hp
  apply uniform_permanent_approximation_of_activity_predicate E hE hp C q hC hq hq1 hentry hZ
  apply actualCoreActivities_of_matrix_bounds _ C q hp hC hq hq1 _ hZ
  intro i j
  change |(Fintype.card ι : ℝ)⁻¹ * E i j|≤C/Fintype.card ι
  rw [abs_mul,abs_of_pos (inv_pos.mpr hn)]
  simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left (hentry i j) (inv_nonneg.mpr hn.le)

end TournamentHamiltonian
