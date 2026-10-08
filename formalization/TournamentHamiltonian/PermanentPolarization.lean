import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem complex_posSemidef_block_diagonal (L R : Matrix ι ι ℂ)
    (hL : L.PosSemidef) (hR : R.PosSemidef) :
    (Matrix.fromBlocks L 0 0 R).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (Matrix.fromBlocks L 0 0 R).conjTranspose = Matrix.fromBlocks L 0 0 R
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, hL.isHermitian.eq,
      hR.isHermitian.eq]
  · intro x
    have h1 := hL.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have h2 := hR.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    convert add_nonneg h1 h2 using 1
    simp only [dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec,
      Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero, zero_add,
      Pi.star_apply, Function.comp_apply]

/-- The actual polar block matrix is positive semidefinite, including for
singular and nonnormal complex matrices. -/
theorem permanent_polarization_block_posSemidef (Z : Matrix ι ι ℂ) :
    (Matrix.fromBlocks (CFC.abs Z.conjTranspose) Z Z.conjTranspose (CFC.abs Z)).PosSemidef := by
  let A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := Matrix.fromBlocks 0 Z Z.conjTranspose 0
  let D : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    Matrix.fromBlocks (CFC.abs Z.conjTranspose) 0 0 (CFC.abs Z)
  have hA : A.IsHermitian := by
    change A.conjTranspose = A
    simp only [A, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_conjTranspose]
  have hD : D.PosSemidef := complex_posSemidef_block_diagonal _ _
    (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg Z.conjTranspose))
    (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg Z))
  have hDsq : D * D = A * A := by
    simp only [D, A, Matrix.fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add,
      CFC.abs_mul_abs, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hAbs : CFC.abs A = D := by
    rw [CFC.abs, hA.isSelfAdjoint.star_eq]
    apply (CFC.sqrt_eq_iff _ _ (by
      simpa only [hA.isSelfAdjoint.star_eq] using star_mul_self_nonneg A) hD.nonneg).mpr
    exact hDsq
  have hnonneg : 0 ≤ CFC.abs A + A := by
    rw [CFC.abs_add_self A hA.isSelfAdjoint]
    exact smul_nonneg (by norm_num : (0 : ℕ) ≤ 2) (CFC.posPart_nonneg A)
  rw [hAbs] at hnonneg
  change 0 ≤ D + A at hnonneg
  simpa only [D, A, Matrix.fromBlocks_add, zero_add, add_zero] using
    Matrix.nonneg_iff_posSemidef.mp hnonneg

section FiniteGram

variable {κ η : Type*} [Finite η]

omit [Fintype ι] [DecidableEq ι] in
theorem finite_product_gram_posSemidef (H : Matrix κ κ ℂ) (hH : H.PosSemidef)
    (eval : η → ι → κ) (s : Finset ι) :
    (Matrix.of (fun f g : η => ∏ i ∈ s, H (eval f i) (eval g i))).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      convert Matrix.posSemidef_vecMulVec_self_star (fun _ : η => (1 : ℂ)) using 1
      ext f g
      simp [Matrix.vecMulVec_apply, Pi.star_apply]
  | @insert a s ha ih =>
      have h := (hH.submatrix (fun f : η => eval f a)).hadamard ih
      convert h using 1
      ext f g
      simp [Finset.prod_insert ha, Matrix.hadamard_apply]

end FiniteGram

noncomputable def permanentGram (A : Matrix ι ι ℂ) : Matrix (Equiv.Perm ι) (Equiv.Perm ι) ℂ :=
  fun σ τ => ∏ i, A (σ i) (τ i)

omit [DecidableEq ι] in
theorem permanentGram_posSemidef (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    (permanentGram A).PosSemidef :=
  finite_product_gram_posSemidef A hA (fun (σ : Equiv.Perm ι) i => σ i) Finset.univ

theorem permanentGram_sum (A : Matrix ι ι ℂ) :
    (∑ σ, ∑ τ, permanentGram A σ τ) = (Fintype.card (Equiv.Perm ι) : ℂ) * A.permanent := by
  have hinner (τ : Equiv.Perm ι) : (∑ σ : Equiv.Perm ι, ∏ i, A (σ i) (τ i)) = A.permanent :=
    Matrix.permanent_permute_rows τ A
  rw [Finset.sum_comm]
  simp only [permanentGram, hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem complex_posSemidef_two_cauchy (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef) :
    ‖M 0 1‖ ^ 2 ≤ (M 0 0).re * (M 1 1).re := by
  have h0 : (M 0 0).im = 0 := (Complex.nonneg_iff.mp hM.diag_nonneg).2.symm
  have h1 : (M 1 1).im = 0 := (Complex.nonneg_iff.mp hM.diag_nonneg).2.symm
  have h10 : M 1 0 = star (M 0 1) := (hM.isHermitian.apply 1 0).symm
  have hd := (Complex.nonneg_iff.mp hM.det_nonneg).1
  rw [Matrix.det_fin_two, h10] at hd
  simp only [Complex.sub_re, Complex.mul_re, h0, h1, mul_zero, sub_zero,
    Complex.star_def, Complex.conj_re, Complex.conj_im] at hd
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  nlinarith

noncomputable def polarizedPermanentGram (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    Matrix (Equiv.Perm ι ⊕ Equiv.Perm ι) (Equiv.Perm ι ⊕ Equiv.Perm ι) ℂ :=
  fun f g => ∏ i, H (Sum.elim (fun σ : Equiv.Perm ι => Sum.inl (σ i))
    (fun τ : Equiv.Perm ι => Sum.inr (τ i)) f)
    (Sum.elim (fun σ : Equiv.Perm ι => Sum.inl (σ i))
    (fun τ : Equiv.Perm ι => Sum.inr (τ i)) g)

omit [DecidableEq ι] in
theorem polarizedPermanentGram_posSemidef (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (hH : H.PosSemidef) :
    (polarizedPermanentGram H).PosSemidef :=
  finite_product_gram_posSemidef H hH
    (fun f i => Sum.elim (fun σ : Equiv.Perm ι => Sum.inl (σ i))
      (fun τ : Equiv.Perm ι => Sum.inr (τ i)) f) Finset.univ

noncomputable def permanentBlockCollapse : Matrix (Equiv.Perm ι ⊕ Equiv.Perm ι) (Fin 2) ℂ :=
  fun k b => Sum.elim (fun _ => if b = 0 then 1 else 0)
    (fun _ => if b = 1 then 1 else 0) k

noncomputable def permanentPolarCompression (L Z R : Matrix ι ι ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (permanentBlockCollapse (ι := ι)).conjTranspose *
    polarizedPermanentGram (Matrix.fromBlocks L Z Z.conjTranspose R) * permanentBlockCollapse

theorem permanentBlockCollapse_entry (L Z R : Matrix ι ι ℂ) (a b : Fin 2) :
    permanentPolarCompression L Z R a b =
      (Fintype.card (Equiv.Perm ι) : ℂ) *
        (if a = 0 then (if b = 0 then L.permanent else Z.permanent)
          else (if b = 0 then Z.conjTranspose.permanent else R.permanent)) := by
  fin_cases a <;> fin_cases b <;>
    simp [permanentPolarCompression, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_sum_type, permanentBlockCollapse, polarizedPermanentGram]
  · rw [Finset.sum_comm]
    exact permanentGram_sum L
  · rw [Finset.sum_comm]
    exact permanentGram_sum Z
  · rw [Finset.sum_comm]
    exact permanentGram_sum Z.conjTranspose
  · rw [Finset.sum_comm]
    exact permanentGram_sum R

theorem complex_posSemidef_permanent_nonnegative (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    0 ≤ A.permanent := by
  have h := (permanentGram_posSemidef A hA).dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_one, one_mul, mul_one] at h
  rw [permanentGram_sum] at h
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm ι) := by exact_mod_cast Fintype.card_pos
  have hh := Complex.nonneg_iff.mp h
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at hh
  apply Complex.nonneg_iff.mpr
  constructor
  · nlinarith [hh.1]
  · have hi : A.permanent.im = 0 := by nlinarith [hh.2]
    exact hi.symm

/-- The actual matrix permanent inherits the Cauchy inequality from the
positive block permanent Gram form. -/
theorem complex_permanent_block_cauchy (L Z R : Matrix ι ι ℂ)
    (hH : (Matrix.fromBlocks L Z Z.conjTranspose R).PosSemidef) :
    ‖Z.permanent‖ ^ 2 ≤ L.permanent.re * R.permanent.re := by
  have hK := polarizedPermanentGram_posSemidef _ hH
  have hM := hK.conjTranspose_mul_mul_same (permanentBlockCollapse (ι := ι))
  change (permanentPolarCompression L Z R).PosSemidef at hM
  have h := complex_posSemidef_two_cauchy _ hM
  rw [permanentBlockCollapse_entry L Z R 0 1, permanentBlockCollapse_entry L Z R 0 0,
    permanentBlockCollapse_entry L Z R 1 1] at h
  have hfin : (1 : Fin 2) ≠ 0 := by decide
  simp only [Fin.isValue, hfin, ite_true, ite_false] at h
  norm_num only [norm_mul, Complex.norm_natCast, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero, mul_pow] at h
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm ι) := by exact_mod_cast Fintype.card_pos
  apply le_of_mul_le_mul_left _ (sq_pos_of_pos hc)
  convert h using 1
  ring

/-- Permanent polarization for every complex matrix, without normality or
invertibility assumptions. The square-root factors are actual PSD permanents. -/
theorem permanent_polarization (Z : Matrix ι ι ℂ) :
    ‖Z.permanent‖ ≤ Real.sqrt ((CFC.abs Z).permanent.re * (CFC.abs Z.conjTranspose).permanent.re) := by
  have h := complex_permanent_block_cauchy _ Z _ (permanent_polarization_block_posSemidef Z)
  have hL := Complex.nonneg_iff.mp (complex_posSemidef_permanent_nonnegative (CFC.abs Z)
    (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg Z)))
  have hR := Complex.nonneg_iff.mp (complex_posSemidef_permanent_nonnegative (CFC.abs Z.conjTranspose)
    (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg Z.conjTranspose)))
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (mul_nonneg hL.1 hR.1)]
  simpa only [mul_comm] using h

end TournamentHamiltonian
