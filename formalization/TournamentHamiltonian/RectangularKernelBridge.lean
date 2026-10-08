import TournamentHamiltonian.RectangularScaling

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem centeringProjection_submatrix_equiv (e : ι ≃ κ) :
    (centeringProjection κ).submatrix e e = centeringProjection ι := by
  rw [centeringProjection_eq, centeringProjection_eq]
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.submatrix_apply, ← Fintype.card_congr e]
  · have he : e i ≠ e j := fun hh => h (e.injective hh)
    simp [Matrix.submatrix_apply, h, he, ← Fintype.card_congr e]

theorem rectangular_centering_square_reindex (X : Matrix ι κ ℝ) (e : ι ≃ κ) :
    (centeringProjection ι * X * centeringProjection κ).submatrix id e =
      centeringProjection ι * X.submatrix id e * centeringProjection ι := by
  have h1 := Matrix.submatrix_mul_equiv (centeringProjection ι) X id (Equiv.refl ι) e
  change centeringProjection ι * X.submatrix id e = (centeringProjection ι * X).submatrix id e at h1
  have h2 := Matrix.submatrix_mul_equiv (centeringProjection ι * X) (centeringProjection κ) id e e
  change (centeringProjection ι * X).submatrix id e * (centeringProjection κ).submatrix e e = _ at h2
  rw [← h2, ← h1, centeringProjection_submatrix_equiv]

/-- The manuscript's actual two-sided rectangular projection is exactly the
centered kernel used by the local-scaling theorem. -/
theorem rectangularCenteredKernel_eq_centering (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (hmass : matrixEntryMass X = Fintype.card ι) :
    rectangularCenteredKernel X = centeringProjection ι * X * centeringProjection κ := by
  have hm : matrixEntryMass (X.submatrix id e) = Fintype.card ι := by
    have h := matrixEntryMass_submatrix_equiv X (Equiv.refl ι) e
    change matrixEntryMass (X.submatrix id e) = matrixEntryMass X at h
    rwa [hmass] at h
  have h := localCenteredKernel_eq_centering (X.submatrix id e) hp hm
  rw [rectangularCenteredKernel_square_reindex, ← rectangular_centering_square_reindex] at h
  ext i j
  have hj := congrFun (congrFun h i) (e.symm j)
  simpa only [Matrix.submatrix_apply, id_eq, Equiv.apply_symm_apply] using hj

omit [DecidableEq ι] [DecidableEq κ] in
theorem rectangularCenteredKernel_density_bound (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K eps : ℝ)
    (hX : ∀ i j, |X i j| ≤ K / Fintype.card ι)
    (ha : ∀ i, |matrixRowError X i| ≤ eps) (hb : ∀ j, |matrixColumnError X j| ≤ eps)
    (i : ι) (j : κ) :
    |rectangularCenteredKernel X i j| ≤ (K + 2 * eps + 1) / Fintype.card ι := by
  have h := localCenteredKernel_density_bound (X.submatrix id e) hp K eps
    (fun a b => hX a (e b))
    (by intro a; rw [matrixRowError_square_reindex]; exact ha a)
    (by intro b; rw [matrixColumnError_square_reindex]; exact hb (e b)) i (e.symm j)
  rw [rectangularCenteredKernel_square_reindex] at h
  simpa only [Matrix.submatrix_apply, id_eq, Equiv.apply_symm_apply] using h

end TournamentHamiltonian
