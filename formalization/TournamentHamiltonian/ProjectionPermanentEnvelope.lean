import TournamentHamiltonian.RankOneGramFactor
import TournamentHamiltonian.ComplexSpectralFrobenius

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

/-- An actual rank-one projection plus a centered PSD perturbation satisfies the
Gaussian permanent envelope using its operator and Frobenius norms. -/
theorem rankOne_projection_permanent_le_exponential (U : Matrix ι Unit ℂ)
    (hU : U.conjTranspose * U = 1) (K : Matrix ι ι ℂ) (hK : K.PosSemidef)
    (hUK : (U * U.conjTranspose) * K = 0) (hp : 0 < Fintype.card ι)
    (q C : ℝ) (hq : q < 1) (hC : 0 ≤ C) (hgap : ‖K‖ ≤ q)
    (hL2 : complexFrobeniusSq K ≤ C ^ 2) :
    (U * U.conjTranspose + K).permanent.re ≤ (Fintype.card ι).factorial /
      (Fintype.card ι : ℝ) ^ Fintype.card ι *
        Real.exp (C * Real.sqrt (Fintype.card ι) / (1 - q)) := by
  have hev : ∀ i, hK.isHermitian.eigenvalues i ≤ q :=
    fun i => (complex_posSemidef_eigenvalue_le_norm K hK hp i).trans hgap
  have hsq : ∑ i, hK.isHermitian.eigenvalues i ^ 2 ≤ C ^ 2 := by
    rwa [complex_posSemidef_eigenvalue_sq_sum K hK]
  exact (rankOne_projection_permanent_le_geometric U hU K hK hUK hp
    (fun i => (hev i).trans_lt hq)).trans (mul_le_mul_of_nonneg_left
      (geometric_product_le_exp_sqrt _ q C hK.eigenvalues_nonneg hev hq hC hsq)
      (by positivity))

end TournamentHamiltonian
