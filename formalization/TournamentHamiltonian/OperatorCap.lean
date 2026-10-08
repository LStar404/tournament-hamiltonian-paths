import TournamentHamiltonian.SkewOperatorNorm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

private theorem exists_sorted_permutation {n : ℕ} (f : Fin n → ℝ) :
    ∃ p : Equiv.Perm (Fin n), Monotone (fun i => f (p i)) := by
  classical
  let emb : Fin n ↪ (ℝ ×ₗ Fin n) :=
    ⟨fun i => toLex (f i, i), by intro i j h; exact congrArg (fun x => (ofLex x).2) h⟩
  let s := Finset.univ.map emb
  have hs : s.card = n := by simp [s]
  let e : Fin n ≃ s := (s.orderIsoOfFin hs).toEquiv
  let back : s → Fin n := fun x => (ofLex x.val).2
  have hb : ∀ x : s, emb (back x) = x.val := by
    intro x
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp x.property
    change emb i = x.val at hi
    change emb ((ofLex x.val).2) = x.val
    rw [← hi]
    rfl
  have hbb : Function.Bijective back := by
    constructor
    · intro x y h
      apply Subtype.ext
      rw [← hb x, ← hb y, h]
    · intro i
      exact ⟨⟨emb i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩, rfl⟩
  let p : Equiv.Perm (Fin n) := e.trans (Equiv.ofBijective back hbb)
  refine ⟨p, ?_⟩
  intro i j hij
  have horder := (s.orderIsoOfFin hs).monotone hij
  have hfirst := Prod.Lex.monotone_fst _ _ horder
  change (ofLex (e i).val).1 ≤ (ofLex (e j).val).1 at hfirst
  have he : ∀ k, (ofLex (e k).val).1 = f (p k) := by
    intro k
    have hbk := hb (e k)
    change toLex (f (p k), p k) = (e k).val at hbk
    exact congrArg (fun x => (ofLex x).1) hbk.symm
  simpa [← he] using hfirst

private theorem one_add_imaginary_eq_exp (t : ℝ) :
    (1 : ℂ) + Complex.I * t =
      ((Real.cos (Real.arctan t))⁻¹ : ℝ) * Complex.exp ((Real.arctan t : ℂ) * Complex.I) := by
  have hc := (Real.cos_arctan_pos t).ne'
  have ht := Real.tan_arctan t
  rw [Real.tan_eq_sin_div_cos] at ht
  apply Complex.ext
  · simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.exp_ofReal_mul_I_re]
    simp [hc]
  · simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      zero_add, add_zero, Complex.exp_ofReal_mul_I_im]
    simpa [div_eq_mul_inv, mul_comm] using ht.symm

/-- The transitive determinant has no imaginary zero up to the universal
2 n / pi barrier. This includes the boundary, using arctan(t) < t. -/
theorem transitiveKernel_imaginary_det_re_pos (n : ℕ) (t : ℝ)
    (h : (n : ℝ) * |t| ≤ Real.pi / 2) :
    0 < ((transitiveKernel n (Complex.I * t)).det).re := by
  by_cases ht : t = 0
  · simp [ht, transitiveKernel]
  have hθ : |(n : ℝ) * Real.arctan t| < Real.pi / 2 := by
    by_cases hn : n = 0
    · simp [hn, Real.pi_pos]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [abs_mul, abs_of_pos hnR]
    exact (mul_lt_mul_of_pos_left (Real.abs_arctan_lt_abs ht) hnR).trans_le h
  have hcθ : 0 < Real.cos ((n : ℝ) * Real.arctan t) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hp : 0 < (((1 : ℂ) + Complex.I * t) ^ n).re := by
    rw [one_add_imaginary_eq_exp, mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul]
    have heq : (n : ℂ) * ((Real.arctan t : ℂ) * Complex.I) =
        ((n : ℝ) * Real.arctan t : ℝ) * Complex.I := by push_cast; ring
    rw [heq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, zero_mul, sub_zero]
    exact mul_pos (pow_pos (inv_pos.mpr (Real.cos_arctan_pos t)) n) hcθ
  rw [transitiveKernel_det]
  have hconj : ((1 : ℂ) - Complex.I * t) ^ n =
      star (((1 : ℂ) + Complex.I * t) ^ n) := by
    simp [star_add, star_mul, sub_eq_add_neg, mul_comm]
  rw [hconj]
  have hre (z : ℂ) : ((z + star z) / 2).re = z.re := by
    norm_num [Complex.star_def, Complex.div_re, Complex.normSq_apply]
  rw [hre]
  exact hp

theorem complexSignMatrix_transitiveTournament (n : ℕ) :
    complexSignMatrix (transitiveTournament n) = transitiveSkew n := by
  ext i j
  simp only [complexSignMatrix, signMatrix_transitiveTournament]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [transitiveSkew, hij]
  · simp [transitiveSkew]
  · simp [transitiveSkew, hji, not_lt_of_ge hji.le]

/-- All transitive frequencies satisfy the strict bound needed for the
spectral relaxation. -/
theorem transitive_skewFrequency_lt (n : ℕ) (i : Fin n) :
    |skewFrequency (transitiveTournament n) i| < 2 * n / Real.pi := by
  let freq := skewFrequency (transitiveTournament n) i
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : 0 < 2 * (n : ℝ) / Real.pi := by positivity
  by_contra h
  have hf : 2 * (n : ℝ) / Real.pi ≤ |freq| := le_of_not_gt h
  have hf0 : freq ≠ 0 := by intro he; simp [he] at hf; linarith
  have hbound : (n : ℝ) * |-(1 / freq)| ≤ Real.pi / 2 := by
    rw [abs_neg, abs_div, abs_one]
    have hlp : 0 < |freq| := abs_pos.mpr hf0
    have hineq : 2 * (n : ℝ) ≤ Real.pi * |freq| :=
      by simpa [mul_comm] using (div_le_iff₀ Real.pi_pos).mp hf
    apply (le_div_iff₀ (by norm_num : 0 < (2 : ℝ))).mpr
    field_simp
    nlinarith
  have hp := transitiveKernel_imaginary_det_re_pos n (-(1 / freq)) hbound
  have heq : transitiveKernel n (Complex.I * (-(1 / freq) : ℝ)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) + ((-(1 / freq) : ℝ) : ℂ) • skewHermitian (transitiveTournament n) := by
    rw [transitiveKernel, skewHermitian, complexSignMatrix_transitiveTournament]
    simp [smul_smul, mul_comm]
  rw [heq, hermitian_kernel_det _ (skewHermitian_isHermitian _)] at hp
  have hz : (∏ j : Fin n, (1 + ((-(1 / freq) : ℝ) : ℂ) * (skewFrequency (transitiveTournament n) j : ℂ))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change 1 + ((-(1 / freq) : ℝ) : ℂ) * (freq : ℂ) = 0
    push_cast
    have hfc : (freq : ℂ) ≠ 0 := by exact_mod_cast hf0
    field_simp
    ring
  change 0 < (∏ j : Fin n, (1 + ((-(1 / freq) : ℝ) : ℂ) *
    (skewFrequency (transitiveTournament n) j : ℂ))).re at hp
  rw [hz] at hp
  norm_num at hp

private noncomputable def upperHalfRepresentative (z : ℂ) : ℂ := if 0 ≤ z.im then z else -z

private theorem upperHalfRepresentative_im_nonneg (z : ℂ) :
    0 ≤ (upperHalfRepresentative z).im := by
  unfold upperHalfRepresentative
  split_ifs with h
  · exact h
  · simp only [Complex.neg_im]
    linarith

private theorem upperHalfRepresentative_norm (z : ℂ) :
    ‖upperHalfRepresentative z‖ = ‖z‖ := by
  unfold upperHalfRepresentative
  split_ifs <;> simp

private theorem upperHalfRepresentative_abs_im (z w : ℂ) :
    |(star (upperHalfRepresentative z) * upperHalfRepresentative w).im| =
      |(star z * w).im| := by
  unfold upperHalfRepresentative
  split_ifs <;> simp only [star_neg, neg_mul, mul_neg, neg_neg, Complex.neg_im, abs_neg]

private theorem conjugate_mul_im_polar (z w : ℂ) :
    (star z * w).im = ‖z‖ * ‖w‖ * Real.sin (w.arg - z.arg) := by
  simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  calc
    z.re * w.im + -z.im * w.re =
        (‖z‖ * Real.cos z.arg) * (‖w‖ * Real.sin w.arg) -
          (‖z‖ * Real.sin z.arg) * (‖w‖ * Real.cos w.arg) := by
      rw [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg,
        Complex.norm_mul_sin_arg, Complex.norm_mul_cos_arg]
      ring
    _ = _ := by rw [Real.sin_sub]; ring

/-- Coordinate signs and a permutation suffice to put every pairwise
imaginary product in the orientation of a transitive tournament. -/
theorem exists_phase_ordered_vector {n : ℕ} (z : Fin n → ℂ) :
    ∃ p : Equiv.Perm (Fin n), ∃ w : Fin n → ℂ,
      (∀ i, ‖w i‖ = ‖z (p i)‖) ∧
      (∀ i j, |(star (w i) * w j).im| = |(star (z (p i)) * z (p j)).im|) ∧
      (∀ i j, i ≤ j → 0 ≤ (star (w i) * w j).im) := by
  obtain ⟨p, hp⟩ := exists_sorted_permutation (fun i => (upperHalfRepresentative (z i)).arg)
  let w := fun i => upperHalfRepresentative (z (p i))
  refine ⟨p, w, fun i => upperHalfRepresentative_norm _,
    fun i j => upperHalfRepresentative_abs_im _ _, ?_⟩
  intro i j hij
  have hlo : 0 ≤ (w j).arg - (w i).arg := sub_nonneg.mpr (hp hij)
  have hhi : (w j).arg - (w i).arg ≤ Real.pi := by
    have hi : 0 ≤ (w i).arg :=
      Complex.arg_nonneg_iff.mpr (upperHalfRepresentative_im_nonneg _)
    have hj := Complex.arg_le_pi (w j)
    linarith
  rw [conjugate_mul_im_polar]
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (Real.sin_nonneg_of_mem_Icc ⟨hlo, hhi⟩)

theorem transitive_signMatrix_opNorm_le (n : ℕ) :
    ‖complexSignMatrix (transitiveTournament n)‖ ≤ 2 * n / Real.pi := by
  rw [complexSignMatrix_unitary_diagonalization, Unitary.conjStarAlgAut_apply,
    ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * (n : ℝ) / Real.pi)).mpr
  intro i
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    (transitive_skewFrequency_lt n i).le

private theorem matrix_quadratic_le_opNorm {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) :
    (dotProduct (star z) (M *ᵥ z)).re ≤ ‖M‖ * (∑ i, ‖z i‖ ^ 2) := by
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 z
  let F := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) M
  have hinner : inner ℂ v (F v) = dotProduct (star z) (M *ᵥ z) := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, F, v, Matrix.toEuclideanCLM_toLp,
      dotProduct_comm]
  rw [← hinner]
  calc
    _ ≤ ‖inner ℂ v (F v)‖ := Complex.re_le_norm _
    _ ≤ ‖v‖ * ‖F v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖F‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = _ := by
      dsimp only [F]
      rw [← Matrix.cstar_norm_def, mul_left_comm, ← pow_two, EuclideanSpace.norm_sq_eq]

private theorem hermitian_quadratic_eq_sum {n : ℕ} (T : Tournament n) (z : Fin n → ℂ) :
    (dotProduct (star z) (skewHermitian T *ᵥ z)).re =
      ∑ i, ∑ j, -signMatrix T i j * (star (z i) * z j).im := by
  simp only [dotProduct, Matrix.mulVec, skewHermitian, complexSignMatrix,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Complex.re_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, Complex.mul_im]
  ring

private theorem signMatrix_abs_le_one {n : ℕ} (T : Tournament n) (i j : Fin n) :
    |signMatrix T i j| ≤ 1 := by
  by_cases hij : i = j
  · simp [signMatrix, hij]
  · cases h : T.val i j <;> simp [signMatrix, hij, h]

private theorem hermitian_quadratic_le_abs_im_sum {n : ℕ}
    (T : Tournament n) (z : Fin n → ℂ) :
    (dotProduct (star z) (skewHermitian T *ᵥ z)).re ≤
      ∑ i, ∑ j, |(star (z i) * z j).im| := by
  rw [hermitian_quadratic_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ |-signMatrix T i j * (star (z i) * z j).im| := le_abs_self _
    _ = |signMatrix T i j| * |(star (z i) * z j).im| := by rw [abs_mul, abs_neg]
    _ ≤ 1 * |(star (z i) * z j).im| :=
      mul_le_mul_of_nonneg_right (signMatrix_abs_le_one T i j) (abs_nonneg _)
    _ = _ := one_mul _

private theorem abs_im_sum_eq_transitive_quadratic {n : ℕ} (w : Fin n → ℂ)
    (hw : ∀ i j, i ≤ j → 0 ≤ (star (w i) * w j).im) :
    (∑ i, ∑ j, |(star (w i) * w j).im|) =
      (dotProduct (star w) ((-skewHermitian (transitiveTournament n)) *ᵥ w)).re := by
  rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re, hermitian_quadratic_eq_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hswap : (star (w j) * w i).im = -(star (w i) * w j).im := by
    simp [Complex.mul_im]
    ring
  rw [signMatrix_transitiveTournament]
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [abs_of_nonneg (hw i j hij.le)]
    simp only [transitiveSkew, hij, ite_true, neg_one_mul, neg_neg]
  · have hzero : (star (w i) * w i).im = 0 := by
      simp [Complex.mul_im]
      ring
    simp only [hzero, abs_zero, mul_zero, neg_zero]
  · have hc : (star (w i) * w j).im ≤ 0 := by
      have h := hw j i hji.le
      rw [hswap] at h
      linarith
    rw [abs_of_nonpos hc]
    simp only [transitiveSkew, hji, not_lt_of_ge hji.le, ite_true, ite_false,
      neg_neg, one_mul]

/-- Rayleigh comparison with the transitive symbol matrix, including all
coordinate signs, phase ordering and multiplicities. -/
theorem skewHermitian_quadratic_le_transitive_norm {n : ℕ}
    (T : Tournament n) (z : Fin n → ℂ) :
    (dotProduct (star z) (skewHermitian T *ᵥ z)).re ≤
      ‖complexSignMatrix (transitiveTournament n)‖ * (∑ i, ‖z i‖ ^ 2) := by
  obtain ⟨p, w, hn, ha, hw⟩ := exists_phase_ordered_vector z
  have hsum : (∑ i, ∑ j, |(star (w i) * w j).im|) =
      ∑ i, ∑ j, |(star (z i) * z j).im| := by
    simp_rw [ha]
    calc
      _ = ∑ i, ∑ j, |(star (z (p i)) * z j).im| := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp p (fun j => |(star (z (p i)) * z j).im|)
      _ = _ := Equiv.sum_comp p (fun i => ∑ j, |(star (z i) * z j).im|)
  have hnorm : (∑ i, ‖w i‖ ^ 2) = ∑ i, ‖z i‖ ^ 2 := by
    simp_rw [hn]
    exact Equiv.sum_comp p (fun i => ‖z i‖ ^ 2)
  have hM : ‖-skewHermitian (transitiveTournament n)‖ =
      ‖complexSignMatrix (transitiveTournament n)‖ := by
    rw [norm_neg, skewHermitian, norm_smul, Complex.norm_I, one_mul]
  calc
    _ ≤ ∑ i, ∑ j, |(star (z i) * z j).im| := hermitian_quadratic_le_abs_im_sum T z
    _ = ∑ i, ∑ j, |(star (w i) * w j).im| := hsum.symm
    _ = _ := abs_im_sum_eq_transitive_quadratic w hw
    _ ≤ ‖-skewHermitian (transitiveTournament n)‖ * (∑ i, ‖w i‖ ^ 2) :=
      matrix_quadratic_le_opNorm _ _
    _ = _ := by rw [hM, hnorm]

theorem skewFrequency_le_transitive_norm {n : ℕ} (T : Tournament n) (i : Fin n) :
    skewFrequency T i ≤ ‖complexSignMatrix (transitiveTournament n)‖ := by
  let v := (skewHermitian_isHermitian T).eigenvectorBasis i
  have hnorm : (∑ j, ‖v j‖ ^ 2) = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, (skewHermitian_isHermitian T).eigenvectorBasis.orthonormal.1 i]
    norm_num
  have h := skewHermitian_quadratic_le_transitive_norm T (fun j => v j)
  rw [hnorm, mul_one] at h
  exact ((skewHermitian_isHermitian T).eigenvalues_eq i).trans_le h

theorem skewFrequency_abs_le_transitive_norm {n : ℕ} (T : Tournament n) (i : Fin n) :
    |skewFrequency T i| ≤ ‖complexSignMatrix (transitiveTournament n)‖ := by
  classical
  have hmem : -skewFrequency T i ∈ Finset.univ.val.map (skewFrequency T) := by
    rw [skewFrequency_multiset_neg T]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hmem
  have hneg := skewFrequency_le_transitive_norm T j
  rw [hj] at hneg
  exact abs_le.mpr ⟨by linarith, skewFrequency_le_transitive_norm T i⟩

/-- The cap uses the actual spectrum of an arbitrary tournament, rather
than an assumed list of admissible frequencies. -/
theorem skewFrequency_abs_le_two_mul_div_pi {n : ℕ} (T : Tournament n) (i : Fin n) :
    |skewFrequency T i| ≤ 2 * n / Real.pi :=
  (skewFrequency_abs_le_transitive_norm T i).trans (transitive_signMatrix_opNorm_le n)

theorem pairedMasses_le_spectralCap {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    ∀ x ∈ pairedMasses T, x ≤ spectralCap := by
  intro x hx
  simp only [pairedMasses, Multiset.mem_toList, Multiset.mem_map] at hx
  obtain ⟨freq, hf, rfl⟩ := hx
  obtain ⟨_, i, rfl⟩ := positiveSkewFrequencies_mem T freq hf
  have hi := skewFrequency_abs_le_two_mul_div_pi T i
  have hs : skewFrequency T i ^ 2 ≤ (2 * (n : ℝ) / Real.pi) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (skewFrequency T i)) hi 2
    simpa only [sq_abs] using h
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    _ ≤ (2 * (n : ℝ) / Real.pi) ^ 2 / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hs (sq_nonneg _)
    _ = spectralCap := by unfold spectralCap; field_simp; ring

theorem spectralRatio_le_upperConstant {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    spectralRatio T ≤ upperConstant :=
  spectralRatio_le_upperConstant_of_cap T hn (pairedMasses_le_spectralCap T hn)

theorem transitive_signMatrix_opNorm_lt (n : ℕ) (hn : 0 < n) :
    ‖complexSignMatrix (transitiveTournament n)‖ < 2 * n / Real.pi := by
  rw [complexSignMatrix_unitary_diagonalization, Unitary.conjStarAlgAut_apply,
    ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  have hc : 0 < 2 * (n : ℝ) / Real.pi := by positivity
  apply (pi_norm_lt_iff hc).mpr
  intro i
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    transitive_skewFrequency_lt n i

theorem signMatrix_opNorm_le_transitive {n : ℕ} (T : Tournament n) :
    ‖complexSignMatrix T‖ ≤ ‖complexSignMatrix (transitiveTournament n)‖ := by
  rw [complexSignMatrix_unitary_diagonalization, Unitary.conjStarAlgAut_apply,
    ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    skewFrequency_abs_le_transitive_norm T i

theorem signMatrix_complex_opNorm_lt {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    ‖complexSignMatrix T‖ < 2 * n / Real.pi :=
  (signMatrix_opNorm_le_transitive T).trans_lt (transitive_signMatrix_opNorm_lt n hn)

theorem normalizedSkewOpNorm_lt_two_div_pi {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    normalizedSkewOpNorm T < 2 / Real.pi := by
  have h := signMatrix_complex_opNorm_lt T hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [normalizedSkewOpNorm, norm_smul, Complex.norm_div, norm_one, Complex.norm_natCast]
  calc
    _ < ((1 : ℝ) / n) * (2 * n / Real.pi) :=
      mul_lt_mul_of_pos_left h (by positivity)
    _ = _ := by field_simp

theorem normalizedRealSkewOpNorm_lt_two_div_pi {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    normalizedRealSkewOpNorm T < 2 / Real.pi :=
  (normalizedRealSkewOpNorm_le_complex T).trans_lt (normalizedSkewOpNorm_lt_two_div_pi T hn)

end TournamentHamiltonian
