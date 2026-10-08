import TournamentHamiltonian.BregmanBound
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Quantitative discrete concavity of the Brégman degree factor. All
factorial and logarithmic estimates here are unconditional finite bounds. -/

namespace TournamentHamiltonian

open scoped Classical

noncomputable def logFactorialMean (k : ℕ) : ℝ := Real.log (k.factorial : ℝ) / (k : ℝ)

theorem sum_first_positive_integers (n : ℕ) :
    (∑ i : Fin n, ((i.val : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [ih]
    ring

theorem log_factorial_eq_sum_fin (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ i : Fin n, Real.log ((i.val : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Nat.factorial_succ]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [Real.log_mul (by positivity) (by positivity), ih]
    ring

/-- AM-GM in logarithmic form, proved directly using `log x ≤ x−1`. -/
theorem logFactorialMean_le_log_half_succ (n : ℕ) (hn : 0 < n) :
    logFactorialMean n ≤ Real.log (((n : ℝ) + 1) / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let a : ℝ := ((n : ℝ) + 1) / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hi (i : Fin n) : Real.log ((i.val : ℝ) + 1) - Real.log a ≤
      ((i.val : ℝ) + 1) / a - 1 := by
    simpa only [Real.log_div (by positivity : ((i.val : ℝ) + 1) ≠ 0) ha.ne'] using
      Real.log_le_sub_one_of_pos (by positivity : 0 < ((i.val : ℝ) + 1) / a)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin, ← Finset.sum_div,
    ← log_factorial_eq_sum_fin, sum_first_positive_integers, mul_one] at h
  have he : (n : ℝ) * ((n : ℝ) + 1) / 2 / a - n = 0 := by
    dsimp [a]
    field_simp
    ring
  rw [he] at h
  unfold logFactorialMean
  apply (div_le_iff₀ hnR).mpr
  linarith

/-- The AM-GM gap used in the second-difference estimate. -/
theorem logFactorialMean_gap (k : ℕ) (hk : 2 ≤ k) :
    Real.log (k : ℝ) - logFactorialMean (k - 1) ≥ Real.log 2 := by
  have h := logFactorialMean_le_log_half_succ (k - 1) (by omega)
  have hcast : ((k - 1 : ℕ) : ℝ) + 1 = k := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  rw [hcast, Real.log_div (by positivity : (k : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at h
  linarith

theorem log_factorial_pred (k : ℕ) (hk : 0 < k) :
    Real.log (k.factorial : ℝ) = Real.log (k : ℝ) + Real.log ((k - 1).factorial : ℝ) := by
  have he : k = (k - 1) + 1 := by omega
  conv_lhs => rw [he, Nat.factorial_succ]
  rw [← he, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]

/-- Exact second difference from the manuscript, with every denominator
nonzero justified by the integer degree domain. -/
theorem logFactorialMean_second_difference (k : ℕ) (hk : 2 ≤ k) :
    2 * logFactorialMean k - logFactorialMean (k - 1) - logFactorialMean (k + 1) =
      (2 * (Real.log (k : ℝ) - logFactorialMean (k - 1)) -
        (k : ℝ) * Real.log (1 + 1 / (k : ℝ))) / ((k : ℝ) * ((k : ℝ) + 1)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hmR : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hlog : Real.log ((k : ℝ) + 1) = Real.log (k : ℝ) +
      Real.log (1 + 1 / (k : ℝ)) := by
    rw [← Real.log_mul hkR.ne' (by positivity : 1 + 1 / (k : ℝ) ≠ 0)]
    congr 1
    field_simp
  unfold logFactorialMean
  rw [log_factorial_pred k (by omega), Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity), Nat.cast_add, Nat.cast_one,
    hlog, log_factorial_pred k (by omega), Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  field_simp
  ring

/-- Uniform strict discrete concavity: its curvature is at least the stated
reciprocal quadratic degree factor. -/
theorem logFactorialMean_second_difference_ge (k : ℕ) (hk : 2 ≤ k) :
    1 / (4 * (k : ℝ) * ((k : ℝ) + 1)) ≤
      2 * logFactorialMean k - logFactorialMean (k - 1) - logFactorialMean (k + 1) := by
  rw [logFactorialMean_second_difference k hk]
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hg := logFactorialMean_gap k hk
  have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (k : ℝ))
  have hl' : (k : ℝ) * Real.log (1 + 1 / (k : ℝ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hl hkR.le
    have he : (k : ℝ) * (1 + 1 / (k : ℝ) - 1) = 1 := by field_simp; ring
    rwa [he] at h
  have hnum : 1 / 4 ≤ 2 * (Real.log (k : ℝ) - logFactorialMean (k - 1)) -
      (k : ℝ) * Real.log (1 + 1 / (k : ℝ)) := by
    nlinarith [Real.log_two_gt_d9]
  calc
    _ = (1 / 4 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) := by
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hnum (by positivity)

theorem logFactorialMean_curvature_uniform (m k : ℕ) (hk : 2 ≤ k) (hkm : k < m) :
    1 / (4 * (m : ℝ) ^ 2) ≤
      2 * logFactorialMean k - logFactorialMean (k - 1) - logFactorialMean (k + 1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hmR : (k : ℝ) + 1 ≤ m := by exact_mod_cast (show k + 1 ≤ m by omega)
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hmR
  calc
    _ ≤ 1 / (4 * (k : ℝ) * ((k : ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    _ ≤ _ := logFactorialMean_second_difference_ge k hk

/-- The outgoing degree is the actual Boolean row-support cardinality. -/
theorem rowDegree_eq_adjacency_sum {n : ℕ} (T : Tournament n) (i : Fin n) :
    (rowDegree T.val i : ℝ) = ∑ j, adjacency T i j := by
  unfold rowDegree rowSupport
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  cases h : T.val i j <;> simp [adjacency, h]

theorem rowDegree_le_order_pred {n : ℕ} (T : Tournament n) (i : Fin n) :
    rowDegree T.val i ≤ n - 1 := by
  have hs : rowSupport T.val i ⊆ Finset.univ.erase i := by
    intro j hj
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    subst j
    have he := (Finset.mem_filter.mp hj).2
    simp [T.property.1] at he
  have hc := Finset.card_le_card hs
  simpa only [rowDegree, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin] using hc

theorem score_eq_twice_rowDegree {n : ℕ} (T : Tournament n) (i : Fin n) :
    score T i = 2 * (rowDegree T.val i : ℝ) - ((n : ℝ) - 1) := by
  have h : 2 * (∑ j, adjacency T i j) = (n : ℝ) - 1 + score T i := by
    calc
      _ = ∑ j, 2 * adjacency T i j := Finset.mul_sum _ _ _
      _ = ∑ j, (1 - (if i = j then 1 else 0) + signMatrix T i j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact twice_adjacency T i j
      _ = _ := by simp [score, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← rowDegree_eq_adjacency_sum T i] at h
  linarith

theorem rowDegree_sum {n : ℕ} (T : Tournament n) :
    (∑ i, (rowDegree T.val i : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  have h := score_sum_zero T
  simp_rw [score_eq_twice_rowDegree] at h
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin] at h
  linarith

/-- Discrete concavity yields monotonicity of successive slopes on an interval. -/
theorem discreteConcave_slopes {f : ℕ → ℝ} {lo hi : ℕ}
    (hc : ∀ k, lo < k → k < hi → f (k - 1) + f (k + 1) ≤ 2 * f k)
    {a b : ℕ} (ha : lo ≤ a) (hab : a ≤ b) (hb : b < hi) :
    f (b + 1) - f b ≤ f (a + 1) - f a := by
  have hs : ∀ b, a ≤ b → b < hi → f (b + 1) - f b ≤ f (a + 1) - f a := by
    intro b hab
    induction b, hab using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ b hab ih =>
      intro hb
      have hcurv := hc (b + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hcurv
      have hprev := ih (by omega)
      nlinarith
  exact hs b hab hb

/-- The line through neighboring integer values is a supporting line on
both sides of a discrete concave sequence. -/
theorem discreteConcave_supporting_line {f : ℕ → ℝ} {lo hi a : ℕ}
    (hc : ∀ k, lo < k → k < hi → f (k - 1) + f (k + 1) ≤ 2 * f k)
    (ha : lo ≤ a) (ha' : a < hi) {n : ℕ} (hn : lo ≤ n) (hn' : n ≤ hi) :
    f n ≤ f a + ((n : ℝ) - (a : ℝ)) * (f (a + 1) - f a) := by
  have hf : ∀ n, a ≤ n → n ≤ hi →
      f n ≤ f a + ((n : ℝ) - (a : ℝ)) * (f (a + 1) - f a) := by
    intro n han
    induction n, han using Nat.le_induction with
    | base => intro _; simp
    | succ n han ih =>
      intro hnhi
      have hs := discreteConcave_slopes hc ha han (by omega : n < hi)
      have hp := ih (by omega)
      push_cast
      nlinarith
  have hb : ∀ n, n ≤ a → lo ≤ n →
      f n ≤ f a + ((n : ℝ) - (a : ℝ)) * (f (a + 1) - f a) := by
    intro n hna
    induction hna using Nat.decreasingInduction with
    | self => intro _; simp
    | of_succ n hna ih =>
      intro hnlo
      have hs := discreteConcave_slopes hc hnlo (Nat.le_of_lt hna) ha'
      have hp := ih (by omega)
      push_cast at hp
      nlinarith
  by_cases han : a ≤ n
  · exact hf n han hn'
  · exact hb n (by omega) hn

end TournamentHamiltonian
