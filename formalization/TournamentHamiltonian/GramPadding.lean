import TournamentHamiltonian.GramDeletion

open scoped Matrix

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {m n p r : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq r]

/-- Add any finite number of identically zero rows. -/
def padZeroRows (Z : Matrix m n ℝ) : Matrix (m ⊕ p) n ℝ :=
  Sum.elim Z (fun _ _ => 0)

omit [Fintype n] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem padZeroRows_gram (Z : Matrix m n ℝ) :
    (padZeroRows (p := p) Z).transpose * padZeroRows Z = Z.transpose * Z := by
  ext i j
  simp [padZeroRows, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]

omit [DecidableEq m] [DecidableEq p] in
/-- Zero row padding preserves the actual Gaussian Gram factor. -/
theorem gramGaussian_padZeroRows (Z : Matrix m n ℝ) :
    gramGaussian (padZeroRows (p := p) Z) = gramGaussian Z := by
  unfold gramGaussian
  rw [padZeroRows_gram]

/-- Add any finite number of identically zero columns. -/
def padZeroColumns (Z : Matrix m n ℝ) : Matrix m (n ⊕ r) ℝ :=
  (padZeroRows (p := r) Z.transpose).transpose

theorem gramGaussian_padZeroColumns (Z : Matrix m n ℝ) :
    gramGaussian (padZeroColumns (r := r) Z) = gramGaussian Z := by
  rw [padZeroColumns, gramGaussian_transpose, gramGaussian_padZeroRows, gramGaussian_transpose]

end TournamentHamiltonian
