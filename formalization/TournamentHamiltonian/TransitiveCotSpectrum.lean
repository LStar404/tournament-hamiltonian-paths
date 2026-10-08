import TournamentHamiltonian.OperatorCap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Eigenspace.Matrix

open Module
open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

section Geometric

variable {K : Type*} [Field K]

private theorem finite_geometric_mul (r : K) (n : ℕ) :
    (1 - r) * (∑ i : Fin n, r ^ i.val) = 1 - r ^ n := by
  rw [Fin.sum_univ_eq_sum_range]
  exact mul_neg_geom_sum r n

/-- The actual transitive matrix applied to a geometric vector, without
any root or invertibility assumption. -/
theorem transitiveSkew_geometric_mul (r : K) (n : ℕ) (i : Fin n) :
    (1 - r) * ((transitiveSkew n : Matrix (Fin n) (Fin n) K) *ᵥ
      (fun j => r ^ j.val)) i =
      (1 + r) * r ^ i.val - (1 + r ^ n) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · have hfirst (j : Fin n) : transitiveSkew (n + 1) (0 : Fin (n + 1)) j.succ = (1 : K) := by
        simp [transitiveSkew, Fin.lt_def]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hfirst, Fin.val_zero,
        Fin.val_succ, pow_zero, one_mul]
      have hdiag : (transitiveSkew (n + 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) 0 0 = 0 := by
        simp [transitiveSkew]
      rw [hdiag, zero_mul, zero_add]
      simp_rw [pow_succ]
      rw [← Finset.sum_mul]
      have hg := finite_geometric_mul r n
      linear_combination r * hg
    · have hzero : (transitiveSkew (n + 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) i.succ 0 = -1 := by
        simp [transitiveSkew, Fin.lt_def]
      have hsucc (j : Fin n) :
          (transitiveSkew (n + 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) i.succ j.succ =
            transitiveSkew n i j := by simp [transitiveSkew]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hzero, hsucc,
        Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
      simp_rw [pow_succ, ← mul_assoc]
      rw [← Finset.sum_mul]
      have hi := ih i
      simp only [Matrix.mulVec, dotProduct] at hi
      linear_combination r * hi

/-- Every n-th root of minus one gives an actual nonzero transitive
eigenvector. This identity includes n=0 vacuously. -/
theorem transitiveSkew_geometric_eigenvector (r : K) (n : ℕ)
    (hr : r ^ n = -1) (hne : r ≠ 1) :
    (transitiveSkew n : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => r ^ j.val) =
      ((1 + r) / (1 - r)) • (fun j : Fin n => r ^ j.val) := by
  ext i
  have hi := transitiveSkew_geometric_mul r n i
  rw [hr, add_neg_cancel, sub_zero] at hi
  have hd : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  change _ = ((1 + r) / (1 - r)) * r ^ i.val
  apply (mul_left_cancel₀ hd)
  rw [hi]
  field_simp

end Geometric

noncomputable def transitiveCotAngle (n : ℕ) (j : Fin n) : ℝ :=
  (2 * (j.val : ℝ) + 1) * Real.pi / (2 * n)

noncomputable def transitiveCotRoot (n : ℕ) (j : Fin n) : ℂ :=
  Complex.exp (2 * Complex.I * (transitiveCotAngle n j : ℂ))

private theorem cot_exp_ratio (z : ℂ) :
    Complex.cot z = (Complex.exp (2 * Complex.I * z) + 1) /
      (Complex.I * (1 - Complex.exp (2 * Complex.I * z))) := by
  rw [Complex.cot, Complex.sin, Complex.cos]
  have h₁ : Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I) =
      Complex.exp (-(z * Complex.I)) * (Complex.exp (2 * Complex.I * z) + 1) := by
    rw [mul_add, ← Complex.exp_add]
    ring_nf
  have h₂ : Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I) =
      Complex.exp (-(z * Complex.I)) * (1 - Complex.exp (2 * Complex.I * z)) := by
    ring_nf
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [h₁, h₂]
  field

theorem transitiveCotRoot_pow (n : ℕ) (j : Fin n) :
    transitiveCotRoot n j ^ n = -1 := by
  have hn : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt j.isLt)
  have he : (n : ℂ) * (2 * Complex.I * (transitiveCotAngle n j : ℂ)) =
      (j.val : ℂ) * (2 * Real.pi * Complex.I) + Real.pi * Complex.I := by
    unfold transitiveCotAngle
    push_cast
    field_simp
  rw [transitiveCotRoot, ← Complex.exp_nat_mul, he, Complex.exp_add,
    Complex.exp_nat_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

theorem transitiveCotRoot_ne_one (n : ℕ) (j : Fin n) : transitiveCotRoot n j ≠ 1 := by
  intro h
  have hp := transitiveCotRoot_pow n j
  rw [h, one_pow] at hp
  norm_num at hp

theorem transitiveCotRoot_eigenvalue (n : ℕ) (j : Fin n) :
    (1 + transitiveCotRoot n j) / (1 - transitiveCotRoot n j) =
      Complex.I * (Real.cot (transitiveCotAngle n j) : ℂ) := by
  rw [Complex.ofReal_cot, cot_exp_ratio]
  change (1 + transitiveCotRoot n j) / (1 - transitiveCotRoot n j) =
    Complex.I * ((transitiveCotRoot n j + 1) / (Complex.I * (1 - transitiveCotRoot n j)))
  have hd : 1 - transitiveCotRoot n j ≠ 0 := sub_ne_zero.mpr (Ne.symm (transitiveCotRoot_ne_one n j))
  field_simp
  ring

/-- The manuscript's cotangent is an eigenvalue of the actual ordered
transitive symbol matrix, with its geometric eigenvector explicitly given. -/
theorem transitiveSkew_cot_eigenvector (n : ℕ) (j : Fin n) :
    (transitiveSkew n : Matrix (Fin n) (Fin n) ℂ) *ᵥ
      (fun i => transitiveCotRoot n j ^ i.val) =
    (Complex.I * (Real.cot (transitiveCotAngle n j) : ℂ)) •
      (fun i : Fin n => transitiveCotRoot n j ^ i.val) := by
  rw [← transitiveCotRoot_eigenvalue]
  exact transitiveSkew_geometric_eigenvector _ n
    (transitiveCotRoot_pow n j) (transitiveCotRoot_ne_one n j)

theorem transitiveCotAngle_mem (n : ℕ) (j : Fin n) :
    transitiveCotAngle n j ∈ Set.Ioo 0 Real.pi := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.ne_zero_of_lt j.isLt |> Nat.pos_of_ne_zero)
  have hj : (j.val : ℝ) < n := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  constructor
  · unfold transitiveCotAngle
    positivity
  · unfold transitiveCotAngle
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    have hnat : 2 * j.val + 1 < 2 * n := by omega
    have hreal : 2 * (j.val : ℝ) + 1 < 2 * n := by exact_mod_cast hnat
    nlinarith [mul_lt_mul_of_pos_right hreal Real.pi_pos]

private theorem cot_strictAntiOn : StrictAntiOn Real.cot (Set.Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  have hsx := Real.sin_pos_of_mem_Ioo hx
  have hsy := Real.sin_pos_of_mem_Ioo hy
  have hsd := Real.sin_pos_of_mem_Ioo (show y - x ∈ Set.Ioo 0 Real.pi by
    constructor <;> linarith [hx.1, hy.2])
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    div_lt_div_iff₀ hsy hsx]
  rw [Real.sin_sub] at hsd
  nlinarith

theorem transitiveCotAngle_strictMono (n : ℕ) : StrictMono (transitiveCotAngle n) := by
  intro i j hij
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.ne_zero_of_lt j.isLt |> Nat.pos_of_ne_zero)
  have hijR : (i.val : ℝ) < j.val := by exact_mod_cast hij
  unfold transitiveCotAngle
  apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * n)).mpr
  exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos

theorem transitiveCot_eigenvalues_injective (n : ℕ) :
    Function.Injective (fun j : Fin n => Complex.I * (Real.cot (transitiveCotAngle n j) : ℂ)) := by
  have ha : StrictAnti (fun j : Fin n => Real.cot (transitiveCotAngle n j)) := by
    intro i j hij
    exact cot_strictAntiOn (transitiveCotAngle_mem n i) (transitiveCotAngle_mem n j)
      (transitiveCotAngle_strictMono n hij)
  intro i j hij
  apply ha.injective
  have h := mul_left_cancel₀ Complex.I_ne_zero hij
  exact_mod_cast h

noncomputable def transitiveCotVector (n : ℕ) (j : Fin n) : Fin n → ℂ :=
  fun i => transitiveCotRoot n j ^ i.val

theorem transitiveCotVector_hasEigenvector (n : ℕ) (j : Fin n) :
    Module.End.HasEigenvector (transitiveSkew n : Matrix (Fin n) (Fin n) ℂ).toLin'
      (Complex.I * (Real.cot (transitiveCotAngle n j) : ℂ)) (transitiveCotVector n j) := by
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    exact transitiveSkew_cot_eigenvector n j
  · intro hz
    let i : Fin n := ⟨0, Nat.ne_zero_of_lt j.isLt |> Nat.pos_of_ne_zero⟩
    have hh := congrFun hz i
    simp [transitiveCotVector, i] at hh

theorem transitiveCotVector_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (transitiveCotVector n) :=
  Module.End.eigenvectors_linearIndependent' _ _ (transitiveCot_eigenvalues_injective n) _
    (transitiveCotVector_hasEigenvector n)

/-- The n explicit cotangent vectors form a basis, including the empty
basis in dimension zero. Hence no transitive eigenvalues are omitted. -/
noncomputable def transitiveCotBasis (n : ℕ) : Basis (Fin n) ℂ (Fin n → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank' (transitiveCotVector n)
    (transitiveCotVector_linearIndependent n) (by simp)

@[simp] theorem transitiveCotBasis_apply (n : ℕ) (j : Fin n) :
    transitiveCotBasis n j = transitiveCotVector n j := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) j

theorem transitiveCotBasis_toMatrix (n : ℕ) :
    LinearMap.toMatrix (transitiveCotBasis n) (transitiveCotBasis n)
      (transitiveSkew n : Matrix (Fin n) (Fin n) ℂ).toLin' =
    Matrix.diagonal (fun j => Complex.I * (Real.cot (transitiveCotAngle n j) : ℂ)) := by
  ext i j
  rw [LinearMap.toMatrix_apply, transitiveCotBasis_apply,
    (transitiveCotVector_hasEigenvector n j).apply_eq_smul]
  rw [← transitiveCotBasis_apply]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Basis.repr_self,
    Finsupp.single_apply, Matrix.diagonal_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij, Ne.symm hij]

theorem transitiveSkew_spectrum_cot (n : ℕ) :
    spectrum ℂ (transitiveSkew n : Matrix (Fin n) (Fin n) ℂ) =
      Set.range (fun j : Fin n => Complex.I * (Real.cot (transitiveCotAngle n j) : ℂ)) := by
  calc
    _ = spectrum ℂ (transitiveSkew n : Matrix (Fin n) (Fin n) ℂ).toLin' :=
      (Matrix.spectrum_toLin' _).symm
    _ = spectrum ℂ (LinearMap.toMatrix (transitiveCotBasis n) (transitiveCotBasis n)
        (transitiveSkew n : Matrix (Fin n) (Fin n) ℂ).toLin') :=
      (LinearMap.spectrum_toMatrix _ _).symm
    _ = _ := by rw [transitiveCotBasis_toMatrix, spectrum_diagonal]

private theorem transitiveHermitian_cot_mulVec (n : ℕ) (j : Fin n) :
    skewHermitian (transitiveTournament n) *ᵥ transitiveCotVector n j =
      (-(Real.cot (transitiveCotAngle n j) : ℂ)) • transitiveCotVector n j := by
  rw [skewHermitian, complexSignMatrix_transitiveTournament, Matrix.smul_mulVec]
  change Complex.I • ((transitiveSkew n : Matrix (Fin n) (Fin n) ℂ) *ᵥ
    (fun i => transitiveCotRoot n j ^ i.val)) = _
  rw [transitiveSkew_cot_eigenvector, smul_smul]
  congr 1
  simp [← mul_assoc]

theorem transitiveHermitian_cotBasis_toMatrix (n : ℕ) :
    LinearMap.toMatrix (transitiveCotBasis n) (transitiveCotBasis n)
      (skewHermitian (transitiveTournament n)).toLin' =
    Matrix.diagonal (fun j => -(Real.cot (transitiveCotAngle n j) : ℂ)) := by
  ext i j
  rw [LinearMap.toMatrix_apply, transitiveCotBasis_apply]
  change (transitiveCotBasis n).repr
    (skewHermitian (transitiveTournament n) *ᵥ transitiveCotVector n j) i = _
  rw [transitiveHermitian_cot_mulVec, ← transitiveCotBasis_apply]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Basis.repr_self,
    Finsupp.single_apply, Matrix.diagonal_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij, Ne.symm hij]

theorem transitiveHermitian_spectrum_cot (n : ℕ) :
    spectrum ℂ (skewHermitian (transitiveTournament n)) =
      Set.range (fun j : Fin n => -(Real.cot (transitiveCotAngle n j) : ℂ)) := by
  calc
    _ = spectrum ℂ (skewHermitian (transitiveTournament n)).toLin' :=
      (Matrix.spectrum_toLin' _).symm
    _ = spectrum ℂ (LinearMap.toMatrix (transitiveCotBasis n) (transitiveCotBasis n)
        (skewHermitian (transitiveTournament n)).toLin') :=
      (LinearMap.spectrum_toMatrix _ _).symm
    _ = _ := by rw [transitiveHermitian_cotBasis_toMatrix, spectrum_diagonal]

theorem transitive_skewFrequency_eq_neg_cot (n : ℕ) (i : Fin n) :
    ∃ j : Fin n, skewFrequency (transitiveTournament n) i =
      -Real.cot (transitiveCotAngle n j) := by
  have hi : (skewFrequency (transitiveTournament n) i : ℂ) ∈
      spectrum ℂ (skewHermitian (transitiveTournament n)) := by
    rw [(skewHermitian_isHermitian (transitiveTournament n)).spectrum_eq_image_range]
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [transitiveHermitian_spectrum_cot] at hi
  obtain ⟨j, hj⟩ := hi
  refine ⟨j, ?_⟩
  change -(Real.cot (transitiveCotAngle n j) : ℂ) =
    (skewFrequency (transitiveTournament n) i : ℂ) at hj
  exact_mod_cast hj.symm

theorem transitiveCotAngle_last (n : ℕ) (hn : 0 < n) :
    transitiveCotAngle n ⟨n - 1, by omega⟩ = Real.pi - Real.pi / (2 * n) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  unfold transitiveCotAngle
  simp only [hc]
  field_simp
  ring

theorem transitiveCot_abs_le_first (n : ℕ) (hn : 0 < n) (j : Fin n) :
    |Real.cot (transitiveCotAngle n j)| ≤ Real.cot (Real.pi / (2 * n)) := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hfirst : transitiveCotAngle n first = Real.pi / (2 * n) := by
    simp [transitiveCotAngle, first]
  have hlast := transitiveCotAngle_last n hn
  have hlo : transitiveCotAngle n first ≤ transitiveCotAngle n j :=
    (transitiveCotAngle_strictMono n).monotone (by change (0 : ℕ) ≤ j.val; omega)
  have hhi : transitiveCotAngle n j ≤ transitiveCotAngle n last :=
    (transitiveCotAngle_strictMono n).monotone (by change j.val ≤ n - 1; omega)
  have hu := cot_strictAntiOn.antitoneOn
    (transitiveCotAngle_mem n first) (transitiveCotAngle_mem n j) hlo
  have hl := cot_strictAntiOn.antitoneOn
    (transitiveCotAngle_mem n j) (transitiveCotAngle_mem n last) hhi
  rw [hfirst] at hu
  change Real.cot (transitiveCotAngle n ⟨n - 1, by omega⟩) ≤ _ at hl
  rw [hlast, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub,
    neg_div, ← Real.cot_eq_cos_div_sin] at hl
  exact abs_le.mpr ⟨hl, hu⟩

/-- Exact Euclidean operator norm of the actual transitive skew matrix. -/
theorem transitive_signMatrix_opNorm_eq_cot (n : ℕ) (hn : 0 < n) :
    ‖complexSignMatrix (transitiveTournament n)‖ = Real.cot (Real.pi / (2 * n)) := by
  let first : Fin n := ⟨0, hn⟩
  let : Nonempty (Fin n) := ⟨first⟩
  have hfirst : transitiveCotAngle n first = Real.pi / (2 * n) := by
    simp [transitiveCotAngle, first]
  have hnonneg : 0 ≤ Real.cot (Real.pi / (2 * n)) :=
    (abs_nonneg _).trans (transitiveCot_abs_le_first n hn first)
  apply le_antisymm
  · rw [complexSignMatrix_unitary_diagonalization, Unitary.conjStarAlgAut_apply,
      ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
    intro i
    obtain ⟨j, hj⟩ := transitive_skewFrequency_eq_neg_cot n i
    simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, hj, abs_neg] using transitiveCot_abs_le_first n hn j
  · have hm : Complex.I * (Real.cot (Real.pi / (2 * n)) : ℂ) ∈
        spectrum ℂ (complexSignMatrix (transitiveTournament n)) := by
      rw [complexSignMatrix_transitiveTournament, transitiveSkew_spectrum_cot]
      exact ⟨first, by change Complex.I * (Real.cot (transitiveCotAngle n first) : ℂ) = _; rw [hfirst]⟩
    have hh := spectrum.norm_le_norm_of_mem hm
    simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hnonneg] using hh

/-- The full cotangent operator cap in Section 2.1, for an actual tournament. -/
theorem signMatrix_complex_opNorm_le_cot {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    ‖complexSignMatrix T‖ ≤ Real.cot (Real.pi / (2 * n)) := by
  rw [← transitive_signMatrix_opNorm_eq_cot n hn]
  exact signMatrix_opNorm_le_transitive T

theorem transitive_cot_lt_two_mul_div_pi (n : ℕ) (hn : 0 < n) :
    Real.cot (Real.pi / (2 * n)) < 2 * n / Real.pi := by
  rw [← transitive_signMatrix_opNorm_eq_cot n hn]
  exact transitive_signMatrix_opNorm_lt n hn

end TournamentHamiltonian
