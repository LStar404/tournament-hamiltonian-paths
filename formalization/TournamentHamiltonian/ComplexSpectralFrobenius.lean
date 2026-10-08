import TournamentHamiltonian.PolarSpectralBound
import TournamentHamiltonian.GramLipschitz

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

noncomputable def complexFrobeniusSq {κ : Type*} [Fintype κ] (A : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem complexFrobeniusSq_eq_trace_gram {κ : Type*} [Fintype κ] (A : Matrix ι κ ℂ) :
    complexFrobeniusSq A = (A * A.conjTranspose).trace.re := by
  simp only [complexFrobeniusSq, Matrix.trace, Matrix.diag, Complex.re_sum, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change ‖A i j‖ ^ 2 = (A i j * (starRingEnd ℂ) (A i j)).re
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem complex_hermitian_eigenvalue_sq_sum (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (∑ i, hH.eigenvalues i ^ 2) = (H * H).trace.re := by
  let U := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  let D := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
  have hu : U.conjTranspose * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hs : H = U * D * U.conjTranspose := hH.spectral_theorem
  have hsq : H * H = U * (D * D) * U.conjTranspose := by
    rw [hs]
    calc
      _ = U * D * (U.conjTranspose * U) * D * U.conjTranspose := by noncomm_ring
      _ = _ := by rw [hu, Matrix.mul_one]; noncomm_ring
  rw [hsq, Matrix.trace_mul_cycle, hu, Matrix.one_mul]
  simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum,
    ← Complex.ofReal_mul, Complex.ofReal_re, pow_two]

theorem complex_posSemidef_eigenvalue_sq_sum (H : Matrix ι ι ℂ) (hH : H.PosSemidef) :
    (∑ i, hH.isHermitian.eigenvalues i ^ 2) = complexFrobeniusSq H := by
  rw [complex_hermitian_eigenvalue_sq_sum, complexFrobeniusSq_eq_trace_gram, hH.isHermitian.eq]

theorem complexFrobeniusSq_abs (B : Matrix ι ι ℂ) :
    complexFrobeniusSq (CFC.abs B) = complexFrobeniusSq B := by
  rw [complexFrobeniusSq_eq_trace_gram,
    (complex_abs_posSemidef B).isHermitian.eq]
  rw [CFC.abs_mul_abs, Matrix.star_eq_conjTranspose, Matrix.trace_mul_comm,
    ← complexFrobeniusSq_eq_trace_gram]

theorem complexFrobeniusSq_conjTranspose (B : Matrix ι ι ℂ) :
    complexFrobeniusSq B.conjTranspose = complexFrobeniusSq B := by
  simp only [complexFrobeniusSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

theorem complexFrobeniusSq_real_smul (B : Matrix ι ι ℂ) (R : ℝ) :
    complexFrobeniusSq (R • B) = R ^ 2 * complexFrobeniusSq B := by
  simp only [complexFrobeniusSq, Matrix.smul_apply, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, Finset.mul_sum]

theorem complexFrobeniusSq_ofReal (B : Matrix ι ι ℝ) :
    complexFrobeniusSq (Complex.ofRealHom.mapMatrix B) = realFrobeniusNorm B ^ 2 := by
  rw [realFrobeniusNorm_sq]
  change (∑ i, ∑ j, ‖(B i j : ℂ)‖ ^ 2) = ∑ i, ∑ j, B i j ^ 2
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem complex_posSemidef_eigenvalue_le_norm (H : Matrix ι ι ℂ) (hH : H.PosSemidef)
    (hp : 0 < Fintype.card ι) (i : ι) : hH.isHermitian.eigenvalues i ≤ ‖H‖ := by
  let : Nonempty ι := Fintype.card_pos_iff.mp hp
  have h := spectrum.norm_le_norm_of_mem (hH.isHermitian.eigenvalues_mem_spectrum_real i)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hH.eigenvalues_nonneg i)] using h

end TournamentHamiltonian
