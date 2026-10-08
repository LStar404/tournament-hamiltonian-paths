import TournamentHamiltonian.Packing

/-! Exact rational enclosures, with Mathlib's proved bounds on π. No
floating-point approximation or external numerical oracle is used. -/

namespace TournamentHamiltonian

theorem upperConstant_decimal_bounds :
    (2.857401177672316 : ℝ) < upperConstant ∧
      upperConstant < 2.857401177672317 := by
  let p₀ : ℝ := 3.14159265358979323846
  let p₁ : ℝ := 3.14159265358979323847
  have hlo : p₀ < Real.pi := Real.pi_gt_d20
  have hhi : Real.pi < p₁ := Real.pi_lt_d20
  have hslo : p₀ ^ 2 < Real.pi ^ 2 := by
    dsimp [p₀] at *
    nlinarith [Real.pi_pos]
  have hshi : Real.pi ^ 2 < p₁ ^ 2 := by
    dsimp [p₁] at *
    nlinarith [Real.pi_pos]
  have hfourlo : p₀ ^ 4 < Real.pi ^ 4 := by
    dsimp [p₀] at *
    nlinarith [sq_nonneg (Real.pi ^ 2 - p₀ ^ 2)]
  have hfourhi : Real.pi ^ 4 < p₁ ^ 4 := by
    dsimp [p₁] at *
    nlinarith [sq_nonneg (Real.pi ^ 2 - p₁ ^ 2)]
  dsimp [p₀, p₁] at *
  unfold upperConstant
  constructor
  · apply (lt_div_iff₀ upperConstant_den_pos).2
    nlinarith only [hfourlo, hshi]
  · apply (div_lt_iff₀ upperConstant_den_pos).2
    nlinarith only [hfourhi, hslo]

end TournamentHamiltonian
