import TournamentHamiltonian.Carousel
import TournamentHamiltonian.PositiveDeterminant
import Mathlib.Analysis.Matrix.Spectrum

open scoped Matrix

namespace TournamentHamiltonian

def skewHermitian {n : ℕ} (T : Tournament n) : Matrix (Fin n) (Fin n) ℂ :=
  Complex.I • complexSignMatrix T

theorem skewHermitian_transpose {n : ℕ} (T : Tournament n) :
    (skewHermitian T).transpose = -skewHermitian T := by
  ext i j
  simp only [skewHermitian, complexSignMatrix, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply]
  rw [signMatrix_skew T j i, Complex.ofReal_neg]
  ring

theorem skewHermitian_isHermitian {n : ℕ} (T : Tournament n) :
    (skewHermitian T).IsHermitian := by
  ext i j
  simp only [skewHermitian, complexSignMatrix, Matrix.conjTranspose_apply,
    Matrix.smul_apply, smul_eq_mul, star_mul, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal]
  rw [signMatrix_skew T j i, Complex.ofReal_neg]
  ring

noncomputable def skewFrequency {n : ℕ} (T : Tournament n) : Fin n → ℝ :=
  (skewHermitian_isHermitian T).eigenvalues

theorem complexSignMatrix_unitary_diagonalization {n : ℕ} (T : Tournament n) :
    complexSignMatrix T = Unitary.conjStarAlgAut ℂ _
      (skewHermitian_isHermitian T).eigenvectorUnitary
        (Matrix.diagonal (fun i => -Complex.I * (skewFrequency T i : ℂ))) := by
  have heq : complexSignMatrix T = (-Complex.I) • skewHermitian T := by
    simp [skewHermitian, smul_smul]
  conv_lhs => rw [heq, (skewHermitian_isHermitian T).spectral_theorem, ← map_smul]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal, skewFrequency, hij]

/-- The same unitary basis diagonalizes the Gram matrix with eigenvalues
lambda^2; together with the multiset pairing this gives paired singular values. -/
theorem complexSignMatrix_gram_diagonalization {n : ℕ} (T : Tournament n) :
    (complexSignMatrix T).conjTranspose * complexSignMatrix T =
      Unitary.conjStarAlgAut ℂ _ (skewHermitian_isHermitian T).eigenvectorUnitary
        (Matrix.diagonal (fun i => (skewFrequency T i : ℂ) ^ 2)) := by
  rw [complexSignMatrix_unitary_diagonalization]
  change star (Unitary.conjStarAlgAut ℂ _ _ _) * Unitary.conjStarAlgAut ℂ _ _ _ = _
  rw [← map_star, ← map_mul]
  congr 1
  change ((Matrix.diagonal (fun i => -Complex.I * (skewFrequency T i : ℂ))).conjTranspose *
    Matrix.diagonal (fun i => -Complex.I * (skewFrequency T i : ℂ))) = _
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp [mul_comm, mul_left_comm, pow_two]
  rw [← mul_assoc, Complex.I_mul_I]
  simp

private theorem det_unitary_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U M).det = M.det := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul_right_comm,
    ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul]

private theorem charpoly_unitary_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U M).charpoly = M.charpoly := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm,
    ← Matrix.mul_assoc, Unitary.coe_star_mul_self, one_mul]

private theorem trace_unitary_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U M).trace = M.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, Unitary.coe_star_mul_self, one_mul]

theorem hermitian_kernel_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (z : ℂ) :
    ((1 : Matrix ι ι ℂ) + z • M).det = ∏ i, (1 + z * (hM.eigenvalues i : ℂ)) := by
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ))
  have hdiag : M = Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary D := hM.spectral_theorem
  have heq : (1 : Matrix ι ι ℂ) + z • M =
      Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary (1 + z • D) := by
    rw [map_add, map_one, map_smul, ← hdiag]
  rw [heq, det_unitary_conjugation]
  have hd : (1 : Matrix ι ι ℂ) + z • D = Matrix.diagonal (fun i => 1 + z * (hM.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [D, Matrix.diagonal, hij]
  rw [hd, Matrix.det_diagonal]

/-- The characteristic polynomial records the positive/negative pairing
with multiplicity, rather than only equality of spectral sets. -/
theorem skewFrequency_multiset_neg {n : ℕ} (T : Tournament n) :
    Finset.univ.val.map (skewFrequency T) =
      Finset.univ.val.map (fun i => -skewFrequency T i) := by
  let hM := skewHermitian_isHermitian T
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => (skewFrequency T i : ℂ))
  have hdiag : skewHermitian T = Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary D :=
    hM.spectral_theorem
  have hneg : (-skewHermitian T).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (-(skewFrequency T i : ℂ))) := by
    have heq : -skewHermitian T = Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary (-D) := by
      rw [map_neg, ← hdiag]
    rw [heq, charpoly_unitary_conjugation]
    have hd : -D = Matrix.diagonal (fun i => -(skewFrequency T i : ℂ)) := by
      simp [D]
    rw [hd, Matrix.charpoly_diagonal]
  have hchar : (skewHermitian T).charpoly = (-skewHermitian T).charpoly := by
    rw [← skewHermitian_transpose, Matrix.charpoly_transpose]
  have hroots : Finset.univ.val.map (fun i => (skewFrequency T i : ℂ)) =
      Finset.univ.val.map (fun i => -(skewFrequency T i : ℂ)) := by
    have hrM := hM.roots_charpoly_eq_eigenvalues
    change (skewHermitian T).charpoly.roots =
      Finset.univ.val.map (fun i => (skewFrequency T i : ℂ)) at hrM
    rw [← hrM, hchar, hneg, Polynomial.roots_prod]
    · simp
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)
  have hr := congrArg (Multiset.map Complex.re) hroots
  simpa only [Multiset.map_map, Function.comp_def, Complex.ofReal_re, Complex.neg_re] using hr

theorem skewFrequency_sum_sq {n : ℕ} (T : Tournament n) :
    (∑ i, skewFrequency T i ^ 2) = (n : ℝ) * (n - 1) := by
  let hM := skewHermitian_isHermitian T
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => (skewFrequency T i : ℂ))
  have hdiag : skewHermitian T = Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary D :=
    hM.spectral_theorem
  have heq : (skewHermitian T) ^ 2 =
      Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary (D ^ 2) := by
    rw [map_pow, ← hdiag]
  have htrace : ((skewHermitian T) ^ 2).trace = ∑ i, (skewFrequency T i : ℂ) ^ 2 := by
    rw [heq, trace_unitary_conjugation]
    simp [D, Matrix.diagonal_pow, Matrix.trace_diagonal]
  have hentry : ∀ i j, skewHermitian T i j * skewHermitian T j i = (signMatrix T i j ^ 2 : ℝ) := by
    intro i j
    simp only [skewHermitian, complexSignMatrix, Matrix.smul_apply, smul_eq_mul]
    rw [signMatrix_skew T j i, Complex.ofReal_neg]
    calc
      _ = -(Complex.I * Complex.I) * (signMatrix T i j : ℂ) ^ 2 := by ring
      _ = _ := by simp
  have htrace' : ((skewHermitian T) ^ 2).trace = ((n : ℝ) * (n - 1) : ℝ) := by
    simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    simp_rw [hentry]
    exact_mod_cast signMatrix_total_sq T
  have h := htrace.symm.trans htrace'
  exact_mod_cast h

noncomputable def positiveSkewFrequencies {n : ℕ} (T : Tournament n) : Multiset ℝ := by
  classical
  exact (Finset.univ.val.map (skewFrequency T)).filter (fun x => 0 < x)

private theorem real_multiset_split (M : Multiset ℝ) :
    M = M.filter (fun x => 0 < x) + M.filter (fun x => x < 0) + M.filter (fun x => x = 0) := by
  classical
  ext a
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · simp [ha, not_lt_of_ge ha.le, ne_of_lt ha]
  · simp
  · simp [ha, not_lt_of_ge ha.le, ne_of_gt ha]

theorem skewFrequency_multiset_decomposition {n : ℕ} (T : Tournament n) :
    Finset.univ.val.map (skewFrequency T) =
      positiveSkewFrequencies T + (positiveSkewFrequencies T).map (fun x => -x) +
        (Finset.univ.val.map (skewFrequency T)).filter (fun x => x = 0) := by
  classical
  let M := Finset.univ.val.map (skewFrequency T)
  have hsym : M.map (fun x => -x) = M := by
    simpa only [M, Multiset.map_map, Function.comp_def] using (skewFrequency_multiset_neg T).symm
  have hneg : M.filter (fun x => x < 0) = (positiveSkewFrequencies T).map (fun x => -x) := by
    rw [← hsym, Multiset.filter_map]
    simp only [Function.comp_def, neg_lt_zero]
    rfl
  change M = _
  rw [real_multiset_split M, hneg]
  rfl

theorem positiveSkewFrequencies_sum_sq {n : ℕ} (T : Tournament n) :
    ((positiveSkewFrequencies T).map (fun x => x ^ 2)).sum = (n : ℝ) * (n - 1) / 2 := by
  classical
  let M := Finset.univ.val.map (skewFrequency T)
  have hz : ((M.filter (fun x => x = 0)).map (fun x => x ^ 2)).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    simp only [Multiset.mem_filter] at hx
    simp [hx.2]
  have hneg : (((positiveSkewFrequencies T).map (fun x => -x)).map (fun x => x ^ 2)).sum =
      ((positiveSkewFrequencies T).map (fun x => x ^ 2)).sum := by
    simp [Multiset.map_map]
  have hsum : (M.map (fun x => x ^ 2)).sum = (n : ℝ) * (n - 1) := by
    simpa only [M, Multiset.map_map, Function.comp_def, Finset.sum_map_val] using skewFrequency_sum_sq T
  have h := skewFrequency_multiset_decomposition T
  change M = _ at h
  rw [h, Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add, hneg, hz] at hsum
  linarith

theorem positiveSkewFrequencies_mem {n : ℕ} (T : Tournament n) (x : ℝ)
    (hx : x ∈ positiveSkewFrequencies T) : 0 < x ∧ ∃ i, skewFrequency T i = x := by
  classical
  simp only [positiveSkewFrequencies, Multiset.mem_filter, Multiset.mem_map,
    Finset.mem_val, Finset.mem_univ, true_and] at hx
  exact ⟨hx.2, hx.1⟩

noncomputable def pairedMasses {n : ℕ} (T : Tournament n) : List ℝ :=
  ((positiveSkewFrequencies T).map (fun x => x ^ 2 / (n : ℝ) ^ 2)).toList

theorem pairedMasses_sum {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    (pairedMasses T).sum = (n - 1 : ℝ) / (2 * n) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold pairedMasses
  rw [← Multiset.sum_coe, Multiset.coe_toList]
  have hdiv : ((positiveSkewFrequencies T).map (fun x => x ^ 2 / (n : ℝ) ^ 2)).sum =
      ((positiveSkewFrequencies T).map (fun x => x ^ 2)).sum / (n : ℝ) ^ 2 := by
    induction positiveSkewFrequencies T using Multiset.induction_on with
    | empty => simp
    | cons a M ih => simp [ih, add_div]
  rw [hdiv, positiveSkewFrequencies_sum_sq]
  field_simp

theorem pairedMasses_nonneg {n : ℕ} (T : Tournament n) : ∀ x ∈ pairedMasses T, 0 ≤ x := by
  intro x hx
  simp only [pairedMasses, Multiset.mem_toList, Multiset.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  positivity

theorem pairedMasses_lt_half {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    ∀ x ∈ pairedMasses T, x < 1 / 2 := by
  intro x hx
  have hxsum : x ≤ (pairedMasses T).sum := List.single_le_sum (pairedMasses_nonneg T) x hx
  rw [pairedMasses_sum T hn] at hxsum
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  apply hxsum.trans_lt
  apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) * n)).mpr
  linarith

/-- Each squared frequency is at most the total mass of the positive pairs. -/
theorem skewFrequency_normalized_sq_le_pairedSum {n : ℕ} (T : Tournament n) (i : Fin n) :
    skewFrequency T i ^ 2 / (n : ℝ) ^ 2 ≤ (pairedMasses T).sum := by
  classical
  by_cases hz : skewFrequency T i = 0
  · simp only [hz, zero_pow (by omega : 2 ≠ 0), zero_div]
    exact List.sum_nonneg (pairedMasses_nonneg T)
  rcases lt_or_gt_of_ne hz with hi | hi
  · have hmem : -skewFrequency T i ∈ Finset.univ.val.map (skewFrequency T) := by
      rw [skewFrequency_multiset_neg T]
      exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
    have hp : -skewFrequency T i ∈ positiveSkewFrequencies T := by
      change -skewFrequency T i ∈ (Finset.univ.val.map (skewFrequency T)).filter (fun x => 0 < x)
      exact Multiset.mem_filter.mpr ⟨hmem, by linarith⟩
    have hmass : (-skewFrequency T i) ^ 2 / (n : ℝ) ^ 2 ∈ pairedMasses T := by
      simp only [pairedMasses, Multiset.mem_toList, Multiset.mem_map]
      exact ⟨-skewFrequency T i, hp, rfl⟩
    simpa only [neg_sq] using List.single_le_sum (pairedMasses_nonneg T) _ hmass
  · have hp : skewFrequency T i ∈ positiveSkewFrequencies T := by
      change skewFrequency T i ∈ (Finset.univ.val.map (skewFrequency T)).filter (fun x => 0 < x)
      exact Multiset.mem_filter.mpr ⟨Multiset.mem_map.mpr ⟨i, by simp, rfl⟩, hi⟩
    have hmass : skewFrequency T i ^ 2 / (n : ℝ) ^ 2 ∈ pairedMasses T := by
      simp only [pairedMasses, Multiset.mem_toList, Multiset.mem_map]
      exact ⟨skewFrequency T i, hp, rfl⟩
    exact List.single_le_sum (pairedMasses_nonneg T) _ hmass

/-- Every normalized squared singular frequency has a fixed gap below 1/2. -/
theorem skewFrequency_normalized_sq_lt_half {n : ℕ} (T : Tournament n) (i : Fin n) :
    skewFrequency T i ^ 2 / (n : ℝ) ^ 2 < 1 / 2 := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hs : (pairedMasses T).sum < 1 / 2 := by
    rw [pairedMasses_sum T hn]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) * n)).mpr
    linarith
  exact (skewFrequency_normalized_sq_le_pairedSum T i).trans_lt hs

private theorem skewFrequency_prod_pairs {n : ℕ} (T : Tournament n) (f : ℝ → ℂ)
    (hf : f 0 = 1) :
    ((Finset.univ.val.map (skewFrequency T)).map f).prod =
      ((positiveSkewFrequencies T).map (fun x => f x * f (-x))).prod := by
  classical
  let M := Finset.univ.val.map (skewFrequency T)
  have hz : ((M.filter (fun x => x = 0)).map f).prod = 1 := by
    apply Multiset.prod_eq_one
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    simp only [Multiset.mem_filter] at hx
    simpa only [hx.2] using hf
  have h := skewFrequency_multiset_decomposition T
  change M = _ at h
  change (M.map f).prod = _
  rw [h, Multiset.map_add, Multiset.map_add, Multiset.prod_add, Multiset.prod_add,
    hz, mul_one, Multiset.map_map]
  simp only [Function.comp_def]
  rw [← Multiset.prod_map_mul]

/-- The all-order paired determinant formula for the actual skew matrix. -/
theorem complexSignMatrix_kernel_det {n : ℕ} (T : Tournament n) (z : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + z • complexSignMatrix T).det =
      ((positiveSkewFrequencies T).map (fun x : ℝ => 1 + z ^ 2 * (x : ℂ) ^ 2)).prod := by
  have heq : (1 : Matrix (Fin n) (Fin n) ℂ) + z • complexSignMatrix T =
      1 + (-z * Complex.I) • skewHermitian T := by
    simp [skewHermitian, smul_smul, mul_assoc]
  rw [heq, hermitian_kernel_det _ (skewHermitian_isHermitian T)]
  change (∏ i, (1 + (-z * Complex.I) * (skewFrequency T i : ℂ))) = _
  have hprod : (∏ i, (1 + (-z * Complex.I) * (skewFrequency T i : ℂ))) =
      ((Finset.univ.val.map (skewFrequency T)).map
        (fun x : ℝ => 1 + (-z * Complex.I) * (x : ℂ))).prod := by
    simp only [Multiset.map_map, Function.comp_def, Finset.prod_map_val]
  rw [hprod, skewFrequency_prod_pairs T _ (by simp)]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp only [Complex.ofReal_neg]
  calc
    (1 + (-z * Complex.I) * (x : ℂ)) * (1 + (-z * Complex.I) * -(x : ℂ)) =
        1 - z ^ 2 * Complex.I ^ 2 * (x : ℂ) ^ 2 := by ring
    _ = _ := by simp

theorem complexSignMatrix_normalized_kernel_det {n : ℕ} (T : Tournament n) (z : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + (z / n) • complexSignMatrix T).det =
      ((pairedMasses T).map (fun x : ℝ => 1 + z ^ 2 * (x : ℂ))).prod := by
  rw [complexSignMatrix_kernel_det]
  rw [← Multiset.prod_coe, ← Multiset.map_coe]
  simp only [pairedMasses, Multiset.coe_toList, Multiset.map_map, Function.comp_def]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, div_pow]
  ring

theorem signMatrix_normalized_kernel_det {n : ℕ} (T : Tournament n) (z : ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + (z / n) • signMatrix T).det =
      ((pairedMasses T).map (fun x => 1 + z ^ 2 * x)).prod := by
  have hM : Complex.ofRealHom.mapMatrix
      ((1 : Matrix (Fin n) (Fin n) ℝ) + (z / n) • signMatrix T) =
        1 + ((z : ℂ) / n) • complexSignMatrix T := by
    ext i j
    by_cases hij : i = j <;>
      simp [RingHom.mapMatrix_apply, complexSignMatrix, hij]
  have hc := Complex.ofRealHom.map_det
    ((1 : Matrix (Fin n) (Fin n) ℝ) + (z / n) • signMatrix T)
  rw [hM, complexSignMatrix_normalized_kernel_det] at hc
  have hp := map_list_prod Complex.ofRealHom ((pairedMasses T).map (fun x => 1 + z ^ 2 * x))
  simp only [List.map_map, Function.comp_def, Complex.ofRealHom_eq_coe,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_pow] at hp
  apply Complex.ofReal_injective
  exact hc.trans hp.symm

theorem complexSignMatrix_imaginary_det {n : ℕ} (T : Tournament n) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I / n) • complexSignMatrix T).det =
      (((pairedMasses T).map (fun x => 1 - x)).prod : ℝ) := by
  rw [complexSignMatrix_normalized_kernel_det]
  have hp := map_list_prod Complex.ofRealHom ((pairedMasses T).map (fun x => 1 - x))
  simp only [List.map_map, Function.comp_def, Complex.ofRealHom_eq_coe,
    Complex.ofReal_sub, Complex.ofReal_one] at hp
  rw [hp]
  congr 1
  apply List.map_congr_left
  intro x _
  simp
  ring

theorem complexSignMatrix_imaginary_det_pos {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    0 < (((pairedMasses T).map (fun x => 1 - x)).prod : ℝ) := by
  apply List.prod_pos
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  have hyhalf := pairedMasses_lt_half T hn y hy
  linarith

theorem complexSignMatrix_imaginary_det_ne_zero {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I / n) • complexSignMatrix T).det ≠ 0 := by
  rw [complexSignMatrix_imaginary_det]
  exact_mod_cast (complexSignMatrix_imaginary_det_pos T hn).ne'

theorem determinantRatio_eq_paired_product {n : ℕ} (T : Tournament n) :
    determinantRatio T = (((pairedMasses T).map ratio).prod : ℝ) := by
  rw [determinantRatio, complexSignMatrix_normalized_kernel_det, complexSignMatrix_imaginary_det]
  have hp := map_list_prod Complex.ofRealHom ((pairedMasses T).map (fun x => 1 + x))
  simp only [List.map_map, Function.comp_def, Complex.ofRealHom_eq_coe,
    Complex.ofReal_add, Complex.ofReal_one] at hp
  simp only [one_pow, one_mul]
  rw [← hp, ← Complex.ofReal_div]
  congr 1
  induction pairedMasses T with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← ih]
    simp [ratio, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

noncomputable def skewGram {n : ℕ} (T : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  1 - ((1 : ℝ) / (n : ℝ) ^ 2) • ((signMatrix T).transpose * signMatrix T)

noncomputable def gaussianFactor {n : ℕ} (T : Tournament n) : ℝ :=
  (Real.sqrt (skewGram T).det)⁻¹

noncomputable def spectralRatio {n : ℕ} (T : Tournament n) : ℝ :=
  gaussianFactor T * ((1 : Matrix (Fin n) (Fin n) ℝ) + ((1 : ℝ) / n) • signMatrix T).det

theorem signMatrix_transpose {n : ℕ} (T : Tournament n) :
    (signMatrix T).transpose = -signMatrix T := by
  ext i j
  exact signMatrix_skew T j i

private theorem skewGram_complex_map {n : ℕ} (T : Tournament n) :
    Complex.ofRealHom.mapMatrix (skewGram T) =
      (1 : Matrix (Fin n) (Fin n) ℂ) +
        ((1 : ℂ) / (n : ℂ) ^ 2) • (complexSignMatrix T * complexSignMatrix T) := by
  unfold skewGram
  rw [signMatrix_transpose, neg_mul, smul_neg, sub_neg_eq_add]
  ext i j
  by_cases hij : i = j <;>
    simp [RingHom.mapMatrix_apply, complexSignMatrix, Matrix.mul_apply, hij]

private theorem skewGram_complex_product {n : ℕ} (T : Tournament n) :
    Complex.ofRealHom.mapMatrix (skewGram T) =
      ((1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I / n) • complexSignMatrix T) *
        ((1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I / n) • complexSignMatrix T) := by
  rw [skewGram_complex_map]
  have hcoeff : -((Complex.I / n) * (Complex.I / n)) = (1 : ℂ) / (n : ℂ) ^ 2 := by
    rw [div_mul_div_comm, Complex.I_mul_I]
    simp [pow_two, div_eq_mul_inv, mul_inv_rev]
  rw [← hcoeff, neg_smul, ← sub_eq_add_neg]
  simp only [mul_sub, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_smul]
  abel

theorem skewGram_det {n : ℕ} (T : Tournament n) :
    (skewGram T).det = ((pairedMasses T).map (fun x => 1 - x)).prod ^ 2 := by
  have hneg : (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I / n) • complexSignMatrix T =
      1 + (-Complex.I / n) • complexSignMatrix T := by
    simp [neg_div, neg_smul, sub_eq_add_neg]
  have hm := Complex.ofRealHom.map_det (skewGram T)
  rw [skewGram_complex_product, Matrix.det_mul, hneg,
    complexSignMatrix_normalized_kernel_det, complexSignMatrix_normalized_kernel_det] at hm
  have hp := map_list_prod Complex.ofRealHom ((pairedMasses T).map (fun x => 1 - x))
  simp only [List.map_map, Function.comp_def, Complex.ofRealHom_eq_coe,
    Complex.ofReal_sub, Complex.ofReal_one] at hp
  have heq : ((pairedMasses T).map (fun x : ℝ => 1 + Complex.I ^ 2 * (x : ℂ))).prod =
      ((((pairedMasses T).map (fun x => 1 - x)).prod : ℝ) : ℂ) := by
    rw [hp]
    congr 1
    apply List.map_congr_left
    intro x _
    simp
    ring
  simp only [neg_sq, heq, ← pow_two, ← Complex.ofReal_pow, Complex.ofRealHom_eq_coe] at hm
  exact Complex.ofReal_injective hm

theorem skewGram_det_pos {n : ℕ} (T : Tournament n) (hn : 0 < n) : 0 < (skewGram T).det := by
  rw [skewGram_det]
  exact pow_pos (complexSignMatrix_imaginary_det_pos T hn) 2

theorem gaussianFactor_eq_product {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    gaussianFactor T = ((pairedMasses T).map (fun x => 1 - x)).prod⁻¹ := by
  rw [gaussianFactor, skewGram_det, Real.sqrt_sq (complexSignMatrix_imaginary_det_pos T hn).le]

theorem gaussianFactor_eq_rpow {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    gaussianFactor T = (skewGram T).det ^ (-1 / 2 : ℝ) := by
  rw [gaussianFactor, Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by ring,
    Real.rpow_neg (skewGram_det_pos T hn).le]

theorem gaussianFactor_complex_eq_inverse_det {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    (gaussianFactor T : ℂ) =
      ((1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I / n) • complexSignMatrix T).det⁻¹ := by
  rw [gaussianFactor_eq_product T hn, complexSignMatrix_imaginary_det, Complex.ofReal_inv]

theorem spectralRatio_eq_paired_product {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    spectralRatio T = ((pairedMasses T).map ratio).prod := by
  rw [spectralRatio, gaussianFactor_eq_product T hn, signMatrix_normalized_kernel_det T 1]
  simp only [one_pow, one_mul]
  have h := determinantRatio_eq_paired_product T
  rw [determinantRatio, complexSignMatrix_normalized_kernel_det, complexSignMatrix_imaginary_det] at h
  simp only [one_pow, one_mul] at h
  have hp := map_list_prod Complex.ofRealHom ((pairedMasses T).map (fun x => 1 + x))
  simp only [List.map_map, Function.comp_def, Complex.ofRealHom_eq_coe,
    Complex.ofReal_add, Complex.ofReal_one] at hp
  rw [← hp, ← Complex.ofReal_div] at h
  have hr : ((pairedMasses T).map (fun x => 1 + x)).prod /
      ((pairedMasses T).map (fun x => 1 - x)).prod = ((pairedMasses T).map ratio).prod :=
    Complex.ofReal_injective h
  simpa only [div_eq_mul_inv, mul_comm] using hr

theorem determinantRatio_eq_spectralRatio {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    determinantRatio T = (spectralRatio T : ℂ) := by
  rw [determinantRatio_eq_paired_product, spectralRatio_eq_paired_product T hn]

theorem pairedMasses_sum_lt_half {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    (pairedMasses T).sum < 1 / 2 := by
  rw [pairedMasses_sum T hn]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) * n)).mpr
  linarith

private theorem ratio_product_le_ratio_sum (xs : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x) (hs : xs.sum < 1) :
    (xs.map ratio).prod ≤ ratio xs.sum := by
  induction xs with
  | nil => simp [ratio]
  | cons a xs ih =>
    have ha := hxs a (by simp)
    have ht : ∀ x ∈ xs, 0 ≤ x := fun x hx => hxs x (by simp [hx])
    have ht0 : 0 ≤ xs.sum := List.sum_nonneg ht
    have hs' : a + xs.sum < 1 := hs
    have hra : 0 ≤ ratio a := ratio_nonneg ha (by linarith)
    have hih := ih ht (by linarith)
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact (mul_le_mul_of_nonneg_left hih hra).trans (ratio_merge ha ht0 hs')

private theorem one_sub_sum_le_product (xs : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x) (hs : xs.sum ≤ 1) :
    1 - xs.sum ≤ (xs.map (fun x => 1 - x)).prod := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hxs a (by simp)
    have ht : ∀ x ∈ xs, 0 ≤ x := fun x hx => hxs x (by simp [hx])
    have ht0 : 0 ≤ xs.sum := List.sum_nonneg ht
    have hs' : a + xs.sum ≤ 1 := hs
    have hih := ih ht (by linarith)
    simp only [List.sum_cons, List.map_cons, List.prod_cons]
    calc
      1 - (a + xs.sum) ≤ (1 - a) * (1 - xs.sum) := by nlinarith [mul_nonneg ha ht0]
      _ ≤ (1 - a) * (xs.map (fun x => 1 - x)).prod :=
        mul_le_mul_of_nonneg_left hih (by linarith)

theorem gaussianFactor_bounds {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    0 < gaussianFactor T ∧ gaussianFactor T < 2 := by
  rw [gaussianFactor_eq_product T hn]
  have hp := complexSignMatrix_imaginary_det_pos T hn
  have hs := pairedMasses_sum_lt_half T hn
  have hl := one_sub_sum_le_product (pairedMasses T) (pairedMasses_nonneg T) (by linarith)
  constructor
  · positivity
  · rw [inv_eq_one_div]
    apply (div_lt_iff₀ hp).mpr
    linarith

theorem spectralRatio_bounds {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    0 < spectralRatio T ∧ spectralRatio T ≤ 3 := by
  rw [spectralRatio_eq_paired_product T hn]
  have hs := pairedMasses_sum_lt_half T hn
  constructor
  · apply List.prod_pos
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have hy0 := pairedMasses_nonneg T y hy
    have hyh := pairedMasses_lt_half T hn y hy
    unfold ratio
    apply div_pos <;> linarith
  · have h := ratio_product_le_ratio_sum (pairedMasses T) (pairedMasses_nonneg T) (by linarith)
    have hr : ratio (1 / 2) = (3 : ℝ) := by norm_num [ratio]
    rw [← hr]
    exact h.trans (ratio_mono hs.le (by norm_num))

/-- This now applies packing to the actual tournament spectral factor.
Only the stronger operator cap from Section 2.3 remains as an input. -/
theorem spectralRatio_le_upperConstant_of_cap {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (hcap : ∀ x ∈ pairedMasses T, x ≤ spectralCap) : spectralRatio T ≤ upperConstant := by
  rw [spectralRatio_eq_paired_product T hn]
  exact spectral_product_le_upperConstant (pairedMasses T)
    (fun x hx => ⟨pairedMasses_nonneg T x hx, hcap x hx⟩) (pairedMasses_sum_lt_half T hn).le

theorem carousel_spectralRatio_eq (m : ℕ) :
    (spectralRatio (carouselTournament m) : ℂ) = transitiveRatio (2 * m + 1) := by
  rw [← determinantRatio_eq_spectralRatio _ (by omega), carouselTournament_determinantRatio]

theorem evenCarousel_spectralRatio_eq (m : ℕ) (hm : 0 < m) :
    (spectralRatio (evenCarouselTournament m) : ℂ) = transitiveRatio (2 * m) := by
  rw [← determinantRatio_eq_spectralRatio _ (by omega), evenCarouselTournament_determinantRatio]

/-- The manuscript's actual real spectral factors, for both parities,
have the same absolute O(1/n) constants. -/
theorem carousel_spectralRatios_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ m : ℕ,
      (N ≤ 2 * m + 1 → |spectralRatio (carouselTournament m) - lowerConstant| ≤ C / (2 * m + 1)) ∧
      (N ≤ 2 * m → |spectralRatio (evenCarouselTournament m) - lowerConstant| ≤ C / (2 * m)) := by
  obtain ⟨C, hC, N, hN, hbound⟩ := carousel_determinantRatios_error_bound
  refine ⟨C, hC, N, hN, ?_⟩
  intro m
  constructor
  · intro hn
    have h := (hbound m).1 hn
    rw [determinantRatio_eq_spectralRatio _ (by omega)] at h
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h
  · intro hn
    have h := (hbound m).2 hn
    rw [determinantRatio_eq_spectralRatio _ (by omega)] at h
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

end TournamentHamiltonian
