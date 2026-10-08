import TournamentHamiltonian.GeneratingDeterminant
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators Matrix

namespace TournamentHamiltonian

section SkewInverse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The loss in the inverse skew quadratic form is controlled by the
actual skew image of the input vector. -/
theorem skew_inverse_quadratic_lower (S : Matrix ι ι ℝ)
    (hS : ∀ i j, S i j = -S j i) (x : ι → ℝ) :
    (∑ i, x i ^ 2) - (∑ i, (S *ᵥ x) i ^ 2) ≤
      dotProduct x (((1 : Matrix ι ι ℝ) + S)⁻¹ *ᵥ x) := by
  let M : Matrix ι ι ℝ := 1 + S
  let y := M⁻¹ *ᵥ x
  let z := x - y
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr (det_one_add_skew_pos S hS).ne'
  have hmy : M *ᵥ y = x := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hu, Matrix.one_mulVec]
  have hmz : M *ᵥ z = S *ᵥ x := by
    dsimp only [z]
    rw [Matrix.mulVec_sub, hmy]
    change ((1 : Matrix ι ι ℝ) + S) *ᵥ x - x = _
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    abel
  have hz : M⁻¹ *ᵥ (S *ᵥ x) = z := by
    rw [← hmz, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hu, Matrix.one_mulVec]
  have hxy : dotProduct x y = ∑ i, y i ^ 2 := by
    rw [dotProduct_comm, ← hmy]
    exact one_add_skew_quadratic S hS y
  have hzz : dotProduct (S *ᵥ x) z = ∑ i, z i ^ 2 := by
    rw [dotProduct_comm, ← hmz]
    exact one_add_skew_quadratic S hS z
  have hbound := skew_inverse_quadratic_le S hS (S *ᵥ x)
  change dotProduct (S *ᵥ x) (M⁻¹ *ᵥ (S *ᵥ x)) ≤ _ at hbound
  rw [hz, hzz] at hbound
  have henergy : (∑ i, z i ^ 2) = (∑ i, x i ^ 2) - ∑ i, y i ^ 2 := by
    calc
      _ = (∑ i, x i ^ 2) + (∑ i, y i ^ 2) - 2 * dotProduct x y := by
        simp only [z, Pi.sub_apply, dotProduct, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hxy]; ring
  rw [henergy] at hbound
  change _ ≤ dotProduct x y
  rw [hxy]
  linarith

theorem det_one_add_skew_add_ones_lower (S : Matrix ι ι ℝ)
    (hS : ∀ i j, S i j = -S j i) (c : ℝ) (hc : 0 ≤ c) :
    ((1 : Matrix ι ι ℝ) + S).det *
      (1 + c * (Fintype.card ι - ∑ i, (S *ᵥ (fun _ => (1 : ℝ))) i ^ 2)) ≤
    ((1 : Matrix ι ι ℝ) + S + c • Matrix.of (fun _ _ => (1 : ℝ))).det := by
  let M : Matrix ι ι ℝ := 1 + S
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr (det_one_add_skew_pos S hS).ne'
  have hrank : c • Matrix.of (fun _ _ : ι => (1 : ℝ)) =
      Matrix.replicateCol Unit (fun _ : ι => c) *
        Matrix.replicateRow Unit (fun _ : ι => (1 : ℝ)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hrank, Matrix.det_add_replicateCol_mul_replicateRow hu]
  have heq : (Matrix.replicateRow Unit (fun _ : ι => (1 : ℝ)) * M⁻¹ *
      Matrix.replicateCol Unit (fun _ : ι => c)) default default =
      c * dotProduct (fun _ : ι => (1 : ℝ)) (M⁻¹ *ᵥ (fun _ : ι => (1 : ℝ))) := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Matrix.det_unique (n := Unit)]
  simp only [Matrix.add_apply, Matrix.one_apply_eq]
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (det_one_add_skew_pos S hS).le
  apply add_le_add (le_refl 1)
  apply mul_le_mul_of_nonneg_left _ hc
  simpa using skew_inverse_quadratic_lower S hS (fun _ => 1)

end SkewInverse

theorem one_add_inv_pow_lower (n : ℕ) (hn : 0 < n) :
    Real.exp 1 - Real.exp 1 / n ≤ (1 + 1 / (n : ℝ)) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < 1 + 1 / (n : ℝ) := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos ha
  have ht : 1 - 1 / (n : ℝ) ≤ (n : ℝ) * Real.log (1 + 1 / (n : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hlog hnR.le
    have hscalar : 1 - 1 / (n : ℝ) ≤ (n : ℝ) * (1 - (1 + 1 / (n : ℝ))⁻¹) := by
      have heq : (n : ℝ) * (1 - (1 + 1 / (n : ℝ))⁻¹) = (n : ℝ) / (n + 1) := by
        field_simp
        ring
      rw [heq]
      have hl : 1 - 1 / (n : ℝ) = (n - 1 : ℝ) / n := by field_simp
      rw [hl]
      apply (div_le_div_iff₀ hnR (by positivity : (0 : ℝ) < n + 1)).mpr
      nlinarith
    exact hscalar.trans hh
  have hexp := Real.add_one_le_exp (-(1 / (n : ℝ)))
  calc
    _ = Real.exp 1 * (1 - 1 / (n : ℝ)) := by ring
    _ ≤ Real.exp 1 * Real.exp (-(1 / (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = Real.exp (1 - 1 / (n : ℝ)) := by rw [← Real.exp_add]; rfl
    _ ≤ Real.exp ((n : ℝ) * Real.log (1 + 1 / (n : ℝ))) := Real.exp_le_exp.mpr ht
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log ha]

private theorem multiset_sq_kernel_prod_nonneg (s : Multiset ℝ) (a : ℝ) :
    0 ≤ (s.map (fun x => 1 + a ^ 2 * x ^ 2)).prod := by
  apply Multiset.prod_nonneg
  intro x hx
  obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx
  positivity

private theorem multiset_sq_kernel_prod_mono (s : Multiset ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (s.map (fun x => 1 + a ^ 2 * x ^ 2)).prod ≤
      (s.map (fun x => 1 + b ^ 2 * x ^ 2)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    apply mul_le_mul
    · nlinarith [mul_nonneg (show 0 ≤ b ^ 2 - a ^ 2 by nlinarith) (sq_nonneg x)]
    · exact ih
    · exact multiset_sq_kernel_prod_nonneg s a
    · positivity

/-- A true product comparison, with the loss controlled by the sum of
actual squared frequencies. -/
theorem multiset_sq_kernel_prod_difference_le (s : Multiset ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (s.map (fun x => 1 + b ^ 2 * x ^ 2)).prod -
      (s.map (fun x => 1 + a ^ 2 * x ^ 2)).prod ≤
    (s.map (fun x => 1 + b ^ 2 * x ^ 2)).prod *
      ((b ^ 2 - a ^ 2) * (s.map (fun x => x ^ 2)).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    let U := (s.map (fun x => 1 + b ^ 2 * x ^ 2)).prod
    let V := (s.map (fun x => 1 + a ^ 2 * x ^ 2)).prod
    let A := 1 + b ^ 2 * x ^ 2
    let B := 1 + a ^ 2 * x ^ 2
    let E := (b ^ 2 - a ^ 2) * (s.map (fun x => x ^ 2)).sum
    let δ := (b ^ 2 - a ^ 2) * x ^ 2
    have hU : 0 ≤ U := multiset_sq_kernel_prod_nonneg s b
    have hV : V ≤ U := multiset_sq_kernel_prod_mono s a b ha hab
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hδ : 0 ≤ δ := by dsimp [δ]; exact mul_nonneg (by nlinarith) (sq_nonneg x)
    have hAB : A - B = δ := by dsimp [A, B, δ]; ring
    change U - V ≤ U * E at ih
    change A * U - B * V ≤ A * U * ((b ^ 2 - a ^ 2) * (x ^ 2 + _))
    calc
      _ = A * (U - V) + δ * V := by rw [← hAB]; ring
      _ ≤ A * (U * E) + δ * U := add_le_add
        (mul_le_mul_of_nonneg_left ih hA) (mul_le_mul_of_nonneg_left hV hδ)
      _ ≤ A * U * (E + δ) := by
        have hA1 : 0 ≤ A - 1 := by
          dsimp [A]
          nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg x)]
        nlinarith [mul_nonneg hA1 (mul_nonneg hδ hU)]
      _ = _ := by dsimp [E, δ]; ring

theorem signMatrix_kernel_det_difference_le {n : ℕ} (T : Tournament n) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + b • signMatrix T).det -
      ((1 : Matrix (Fin n) (Fin n) ℝ) + a • signMatrix T).det ≤
    ((1 : Matrix (Fin n) (Fin n) ℝ) + b • signMatrix T).det *
      ((b ^ 2 - a ^ 2) * ((n : ℝ) * (n - 1) / 2)) := by
  rw [signMatrix_real_kernel_det, signMatrix_real_kernel_det]
  simpa only [positiveSkewFrequencies_sum_sq] using
    multiset_sq_kernel_prod_difference_le (positiveSkewFrequencies T) a b ha hab

theorem signMatrix_kernel_det_successor_difference_le {n : ℕ} (T : Tournament n)
    (hn : 0 < n) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det -
      ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / ((n : ℝ) + 1)) • signMatrix T).det ≤
    ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  have hab : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hnR (by linarith)
  have hs : ((1 / (n : ℝ)) ^ 2 - (1 / ((n : ℝ) + 1)) ^ 2) *
      ((n : ℝ) * (n - 1) / 2) ≤ 1 / (n : ℝ) := by
    have heq : ((1 / (n : ℝ)) ^ 2 - (1 / ((n : ℝ) + 1)) ^ 2) *
        ((n : ℝ) * (n - 1) / 2) =
        (((2 * (n : ℝ) + 1) * (n - 1)) / (2 * (n + 1) ^ 2)) / n := by
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ hnR.le
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * (n + 1) ^ 2)).mpr
    nlinarith
  have hdet : 0 ≤ ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det :=
    (det_one_add_skew_pos _ (by
      intro i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [signMatrix_skew T i j]
      ring)).le
  exact (signMatrix_kernel_det_difference_le T _ _ ha hab).trans
    ((mul_le_mul_of_nonneg_left hs hdet).trans_eq (by ring))

theorem one_add_inv_pow_upper (n : ℕ) (hn : 0 < n) :
    (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + 1 / n)
    (by simpa only [add_comm] using Real.add_one_le_exp (1 / (n : ℝ))) n
  rw [← Real.exp_nat_mul] at hh
  simpa only [mul_one_div_cancel hnR.ne'] using hh

theorem tournament_score_image_square_sum_le {n : ℕ} (T : Tournament n)
    (b d : ℝ) (_hd : 0 ≤ d) (hscore : ∀ i, |score T i| ≤ d) :
    (∑ i, ((b • signMatrix T) *ᵥ (fun _ => (1 : ℝ))) i ^ 2) ≤
      b ^ 2 * (n : ℝ) * d ^ 2 := by
  have heq (i : Fin n) : ((b • signMatrix T) *ᵥ (fun _ => (1 : ℝ))) i = b * score T i := by
    simp [Matrix.mulVec, dotProduct, score, Finset.mul_sum]
  simp_rw [heq, mul_pow]
  rw [← Finset.mul_sum]
  have hh : (∑ i, score T i ^ 2) ≤ (n : ℝ) * d ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin n, d ^ 2 := Finset.sum_le_sum (fun i _ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (score T i)) (hscore i) 2)
      _ = _ := by simp
  exact (mul_le_mul_of_nonneg_left hh (sq_nonneg b)).trans_eq (by ring)

private theorem successor_rank_loss_le (n : ℕ) (hn : 0 < n) (d : ℝ) :
    1 - (1 / ((n : ℝ) + 1)) * n +
      (1 / ((n : ℝ) + 1)) ^ 3 * n * d ^ 2 ≤ (1 + d ^ 2) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let b : ℝ := 1 / ((n : ℝ) + 1)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; apply (div_le_one (by positivity)).mpr; linarith
  have hbn : b * n ≤ 1 := by
    dsimp [b]
    rw [one_div_mul_eq_div]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hbsmall : b ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hnR (by linarith)
  have hb3 : b ^ 3 * n ≤ 1 / (n : ℝ) := by
    calc
      _ = (b * n) * b ^ 2 := by ring
      _ ≤ 1 * b ^ 2 := mul_le_mul_of_nonneg_right hbn (sq_nonneg b)
      _ ≤ b := by nlinarith [mul_le_mul_of_nonneg_left hb1 hb]
      _ ≤ _ := hbsmall
  have heq : 1 - b * n = b := by dsimp [b]; field_simp; ring
  change 1 - b * n + b ^ 3 * n * d ^ 2 ≤ _
  rw [heq]
  exact (add_le_add hbsmall (mul_le_mul_of_nonneg_right hb3 (sq_nonneg d))).trans_eq (by ring)

/-- Actual principal-minor generating determinant with a relative error
controlled solely by the actual tournament scores. The bound holds in
every positive dimension. -/
theorem tournament_generating_det_lower_small_scores {n : ℕ} (T : Tournament n)
    (hn : 0 < n) (d : ℝ) (hd : 0 ≤ d) (hscore : ∀ i, |score T i| ≤ d) :
    (2 * Real.exp 1 - Real.exp 1 * (5 + d ^ 2) / n) *
      ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det ≤
    ((1 : Matrix (Fin n) (Fin n) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T)).det := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let a : ℝ := 1 + 1 / (n : ℝ)
  let b : ℝ := 1 / ((n : ℝ) + 1)
  let D := ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det
  let D₀ := ((1 : Matrix (Fin n) (Fin n) ℝ) + b • signMatrix T).det
  let H := (1 : Matrix (Fin n) (Fin n) ℝ) + b • signMatrix T +
    b • Matrix.of (fun _ _ => (1 : ℝ))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbsmall : b ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hnR (by linarith)
  have hS (i j : Fin n) : (b • signMatrix T) i j = -(b • signMatrix T) j i := by
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [signMatrix_skew T i j]
    ring
  have hD : 0 ≤ D := (det_one_add_skew_pos _ (by
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [signMatrix_skew T i j]
    ring)).le
  have hD₀ : 0 ≤ D₀ := (det_one_add_skew_pos (b • signMatrix T) hS).le
  have hDmono : D₀ ≤ D := signMatrix_kernel_det_mono T b _ hb hbsmall
  have hDdiff : D - D₀ ≤ D / n := signMatrix_kernel_det_successor_difference_le T hn
  have hscoreimage := tournament_score_image_square_sum_le T b d hd hscore
  have hrank : D₀ * (1 + b * (n - b ^ 2 * n * d ^ 2)) ≤ H.det := by
    apply le_trans _ (det_one_add_skew_add_ones_lower (b • signMatrix T) hS b hb)
    change D₀ * _ ≤ D₀ * _
    apply mul_le_mul_of_nonneg_left _ hD₀
    simpa only [Fintype.card_fin] using add_le_add (le_refl 1)
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hscoreimage (n : ℝ)) hb)
  let c : ℝ := 1 - b * n + b ^ 3 * n * d ^ 2
  have hc : 0 ≤ c := by
    have hbn : b * n ≤ 1 := by
      dsimp [b]
      rw [one_div_mul_eq_div]
      apply (div_le_one (by positivity)).mpr
      linarith
    dsimp [c]
    positivity
  have hcupper : c ≤ (1 + d ^ 2) / n := successor_rank_loss_le n hn d
  have hinner : 2 * D - H.det ≤ D * (3 + d ^ 2) / n := by
    calc
      _ ≤ 2 * (D - D₀) + D₀ * c := by dsimp [c]; nlinarith [hrank]
      _ ≤ 2 * (D / n) + D * c := add_le_add
        (mul_le_mul_of_nonneg_left hDdiff (by norm_num)) (mul_le_mul_of_nonneg_right hDmono hc)
      _ ≤ 2 * (D / n) + D * ((1 + d ^ 2) / n) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hcupper hD)
      _ = _ := by ring
  have hp : a ^ n ≤ Real.exp 1 := one_add_inv_pow_upper n hn
  have hpdiff : Real.exp 1 - a ^ n ≤ Real.exp 1 / n := by
    have hh := one_add_inv_pow_lower n hn
    change _ ≤ a ^ n at hh
    linarith
  have hfullerror : 2 * Real.exp 1 * D - a ^ n * H.det ≤
      Real.exp 1 * (5 + d ^ 2) / n * D := by
    calc
      _ = (Real.exp 1 - a ^ n) * (2 * D) + a ^ n * (2 * D - H.det) := by ring
      _ ≤ (Real.exp 1 / n) * (2 * D) + a ^ n * (D * (3 + d ^ 2) / n) := add_le_add
        (mul_le_mul_of_nonneg_right hpdiff (by positivity))
        (mul_le_mul_of_nonneg_left hinner (pow_nonneg ha _))
      _ ≤ (Real.exp 1 / n) * (2 * D) + Real.exp 1 * (D * (3 + d ^ 2) / n) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hp (by positivity))
      _ = _ := by ring
  have hab : a * b = 1 / (n : ℝ) := by dsimp [a, b]; field_simp
  have heq : (1 : Matrix (Fin n) (Fin n) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T) = a • H := by
    ext i j
    simp only [H, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    simp only [mul_add, ← mul_assoc, hab, mul_one]
    have hw := twice_adjacency T i j
    simp only [Matrix.one_apply]
    dsimp [a]
    linear_combination (1 / (n : ℝ)) * hw
  rw [heq, Matrix.det_smul, Fintype.card_fin]
  change (2 * Real.exp 1 - Real.exp 1 * (5 + d ^ 2) / n) * D ≤ _
  nlinarith [hfullerror]

theorem tournament_generating_det_lower_unit_scores {n : ℕ} (T : Tournament n)
    (hn : 0 < n) (hscore : ∀ i, |score T i| ≤ 1) :
    (2 * Real.exp 1 - 6 * Real.exp 1 / n) *
      ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det ≤
    ((1 : Matrix (Fin n) (Fin n) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T)).det := by
  convert tournament_generating_det_lower_small_scores T hn 1 (by norm_num) hscore using 1
  ring

end TournamentHamiltonian
