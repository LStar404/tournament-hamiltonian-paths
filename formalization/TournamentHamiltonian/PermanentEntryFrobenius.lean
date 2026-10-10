import TournamentHamiltonian.FrobeniusGeometry

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι : Type*} [Fintype ι]

theorem realFrobeniusNorm_le_entry_budget (B : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (C : ℝ) (hC : 0 ≤ C)
    (hentry : ∀ i j, |B i j| ≤ C / Fintype.card ι) :
    realFrobeniusNorm B ≤ C := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  apply (sq_le_sq₀ (realFrobeniusNorm_nonneg B) hC).mp
  rw [realFrobeniusNorm_sq]
  calc
    _ ≤ ∑ i : ι, ∑ j : ι, (C / Fintype.card ι) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hentry i j) 2
    _ = C ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

theorem realFrobeniusNorm_normalized_entry_budget (E : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (C : ℝ) (hC : 0 ≤ C)
    (hentry : ∀ i j, |E i j| ≤ C) :
    realFrobeniusNorm ((Fintype.card ι : ℝ)⁻¹ • E) ≤ C := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  apply realFrobeniusNorm_le_entry_budget _ hp C hC
  intro i j
  change |(Fintype.card ι : ℝ)⁻¹ * E i j| ≤ C / Fintype.card ι
  rw [abs_mul, abs_inv, abs_of_pos hn, div_eq_mul_inv, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hentry i j) (inv_nonneg.mpr hn.le)

end TournamentHamiltonian
