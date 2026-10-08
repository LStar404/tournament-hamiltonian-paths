import TournamentHamiltonian.FourBlockPermanent
import TournamentHamiltonian.RectangularScaling

/-! The unrestricted bijection sum agrees with the existing actual rectangular
permanent whenever the row and column index types have equal cardinality. -/

namespace TournamentHamiltonian

open scoped Classical

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem bijectionPermanent_eq_rectangularPermanent (X : Matrix ι κ ℝ) (e : ι ≃ κ) :
    bijectionPermanent X = rectangularPermanent X e := by
  have h := rectangularPermanent_submatrix_equiv X e (Equiv.refl ι)
  change (X.submatrix id e).permanent = bijectionPermanent X at h
  exact h.symm

theorem selectedPermanent_eq_rectangularPermanent {n : ℕ} (T : Tournament n)
    (cols rows : Finset (Fin n)) (e : rows ≃ cols) :
    selectedPermanent (adjacency T) cols rows =
      rectangularPermanent ((adjacency T).submatrix (Subtype.val : rows → Fin n) Subtype.val) e :=
  bijectionPermanent_eq_rectangularPermanent
    ((adjacency T).submatrix (Subtype.val : rows → Fin n) (Subtype.val : cols → Fin n)) e

end TournamentHamiltonian
