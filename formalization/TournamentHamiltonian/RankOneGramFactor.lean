import TournamentHamiltonian.RectangularGramAMGM
import TournamentHamiltonian.OrthogonalPolarBridge
import Mathlib.Data.Matrix.ColumnRowPartitioned

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

noncomputable def rankOneSpectralGramFactor (U : Matrix ι Unit ℂ)
    (K : Matrix ι ι ℂ) (hK : K.PosSemidef) : Matrix ι (Unit ⊕ ι) ℂ :=
  Matrix.fromCols U (psdSpectralFactor K hK)

theorem rankOneSpectralGramFactor_row_gram (U : Matrix ι Unit ℂ)
    (K : Matrix ι ι ℂ) (hK : K.PosSemidef) :
    rankOneSpectralGramFactor U K hK * (rankOneSpectralGramFactor U K hK).conjTranspose =
      U * U.conjTranspose + K := by
  rw [rankOneSpectralGramFactor, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows, psdSpectralFactor_self_mul_star]

theorem unit_column_perp_factor (U : Matrix ι Unit ℂ) (hU : U.conjTranspose * U = 1)
    (K : Matrix ι ι ℂ) (hK : K.PosSemidef) (hUK : (U * U.conjTranspose) * K = 0) :
    U.conjTranspose * psdSpectralFactor K hK = 0 := by
  have hUK' : U.conjTranspose * K = 0 := by
    calc
      _ = (U.conjTranspose * U) * U.conjTranspose * K := by rw [hU, Matrix.one_mul]
      _ = U.conjTranspose * ((U * U.conjTranspose) * K) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hUK]; simp
  apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
  have hzero : (U.conjTranspose * psdSpectralFactor K hK) *
      (U.conjTranspose * psdSpectralFactor K hK).conjTranspose = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = U.conjTranspose * (psdSpectralFactor K hK *
          (psdSpectralFactor K hK).conjTranspose) * U := by simp only [Matrix.mul_assoc]
      _ = U.conjTranspose * K * U := by rw [psdSpectralFactor_self_mul_star]
      _ = 0 := by rw [hUK']; simp
  rw [hzero, Matrix.trace_zero]

theorem rankOneSpectralGramFactor_column_gram (U : Matrix ι Unit ℂ)
    (hU : U.conjTranspose * U = 1) (K : Matrix ι ι ℂ) (hK : K.PosSemidef)
    (hUK : (U * U.conjTranspose) * K = 0) :
    (rankOneSpectralGramFactor U K hK).conjTranspose * rankOneSpectralGramFactor U K hK =
      Matrix.diagonal (Sum.elim (fun _ : Unit => (1 : ℂ))
        (fun i => (hK.isHermitian.eigenvalues i : ℂ))) := by
  have hcross := unit_column_perp_factor U hU K hK hUK
  have hcross' : (psdSpectralFactor K hK).conjTranspose * U = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hcross
  rw [rankOneSpectralGramFactor, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols, hU, hcross, hcross', psdSpectralFactor_star_mul_self]
  ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.diagonal_apply]

noncomputable def nonLeftUnitEquiv (ι : Type*) :
    {i : Unit ⊕ ι // i ≠ Sum.inl ()} ≃ ι where
  toFun i := match i with
    | ⟨Sum.inl u, hi⟩ => False.elim (hi (by cases u; rfl))
    | ⟨Sum.inr j, _⟩ => j
  invFun j := ⟨Sum.inr j, by simp⟩
  left_inv i := by
    rcases i with ⟨i, hi⟩
    cases i with
    | inl u => cases u; exact False.elim (hi rfl)
    | inr j => rfl
  right_inv j := rfl

/-- A real projection summand is represented by one additional circular variable,
so the other eigenvalues are exactly those of the centered PSD perturbation. -/
theorem rankOne_projection_permanent_le_geometric (U : Matrix ι Unit ℂ)
    (hU : U.conjTranspose * U = 1) (K : Matrix ι ι ℂ) (hK : K.PosSemidef)
    (hUK : (U * U.conjTranspose) * K = 0) (hp : 0 < Fintype.card ι)
    (hgap : ∀ i, hK.isHermitian.eigenvalues i < 1) :
    (U * U.conjTranspose + K).permanent.re ≤ (Fintype.card ι).factorial /
      (Fintype.card ι : ℝ) ^ Fintype.card ι *
        ∏ i, (1 - hK.isHermitian.eigenvalues i)⁻¹ := by
  let : DecidableEq (Unit ⊕ ι) := Classical.decEq _
  let A := rankOneSpectralGramFactor U K hK
  let d : Unit ⊕ ι → ℝ := Sum.elim (fun _ => 1) hK.isHermitian.eigenvalues
  have hA : A.conjTranspose * A = Matrix.diagonal (fun i => (d i : ℂ)) := by
    convert rankOneSpectralGramFactor_column_gram U hU K hK hUK using 1
    all_goals first
      | rfl
      | exact Subsingleton.elim _ _
      | ext i j; cases i <;> cases j <;> simp [Matrix.diagonal_apply, d]
  have h := rectangularGramPermanent_le_geometric A d hA hp (Sum.inl ())
    (by
      intro i
      cases i with
      | inl u => norm_num [d]
      | inr j => exact hK.eigenvalues_nonneg j)
    rfl (by
      intro i hi
      cases i with
      | inl u => cases u; exact False.elim (hi rfl)
      | inr j => exact hgap j)
  rw [rankOneSpectralGramFactor_row_gram] at h
  have hprod : (∏ i : {i : Unit ⊕ ι // i ≠ Sum.inl ()}, (1 - d i.val)⁻¹) =
      ∏ i, (1 - hK.isHermitian.eigenvalues i)⁻¹ := by
    exact Fintype.prod_equiv (nonLeftUnitEquiv ι) _ _ (fun i => by
      rcases i with ⟨i, hi⟩
      cases i with
      | inl u => cases u; exact False.elim (hi rfl)
      | inr j => rfl)
  rwa [hprod] at h

end TournamentHamiltonian
