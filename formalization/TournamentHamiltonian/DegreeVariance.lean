import TournamentHamiltonian.DegreeBalancing

/-! Strong discrete Jensen bounds for the actual outgoing-degree variance.
The half-integer mean correction is controlled explicitly. -/

namespace TournamentHamiltonian

open scoped Classical

noncomputable def balancedLogFactorialMean (m : ℕ) : ℝ :=
  let a := (m - 1) / 2
  let η : ℝ := ((m : ℝ) - 1) / 2
  logFactorialMean a + (η - (a : ℝ)) * (logFactorialMean (a + 1) - logFactorialMean a)

noncomputable def degreeVariance {n : ℕ} (T : Tournament n) : ℝ :=
  ∑ i, ((rowDegree T.val i : ℝ) - ((n : ℝ) - 1) / 2) ^ 2

/-- Quantitative Jensen for integer degrees with the tournament mean. The
`1/(32m)` correction also covers the half-integer mean. -/
theorem logFactorialMean_degree_variance (m : ℕ) (hm : 3 ≤ m) (d : Fin m → ℕ)
    (hd : ∀ i, 1 ≤ d i ∧ d i ≤ m - 1)
    (hmean : (∑ i, (d i : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) / 2) :
    (∑ i, logFactorialMean (d i)) ≤ (m : ℝ) * balancedLogFactorialMean m -
      (∑ i, ((d i : ℝ) - ((m : ℝ) - 1) / 2) ^ 2) / (8 * (m : ℝ) ^ 2) +
        1 / (32 * (m : ℝ)) := by
  let a : ℕ := (m - 1) / 2
  let η : ℝ := ((m : ℝ) - 1) / 2
  let θ : ℝ := η - (a : ℝ)
  let V : ℝ := ∑ i, ((d i : ℝ) - η) ^ 2
  let g (k : ℕ) : ℝ := logFactorialMean k + (k : ℝ) ^ 2 / (8 * (m : ℝ) ^ 2)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have ha : 1 ≤ a := by dsimp [a]; omega
  have ha' : a < m - 1 := by dsimp [a]; omega
  have hc : ∀ k, 1 < k → k < m - 1 → g (k - 1) + g (k + 1) ≤ 2 * g k := by
    intro k hk hk'
    have hcurv := logFactorialMean_curvature_uniform m k (by omega) (by omega)
    have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have he : 2 * g k - g (k - 1) - g (k + 1) =
        (2 * logFactorialMean k - logFactorialMean (k - 1) - logFactorialMean (k + 1)) -
          1 / (4 * (m : ℝ) ^ 2) := by
      dsimp [g]
      rw [hkcast, Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    discreteConcave_supporting_line hc ha ha' (hd i).1 (hd i).2)
  simp only [g, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin] at hs
  have hmean' : (∑ i, (d i : ℝ)) = (m : ℝ) * η := by dsimp [η]; linarith
  rw [hmean'] at hs
  have hV : (∑ i, (d i : ℝ) ^ 2) = V + (m : ℝ) * η ^ 2 := by
    have he : V = ∑ i : Fin m, ((d i : ℝ) ^ 2 - 2 * η * (d i : ℝ) + η ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at he
    rw [hmean'] at he
    nlinarith
  have he :
      (m : ℝ) * (logFactorialMean a + (a : ℝ) ^ 2 / (8 * (m : ℝ) ^ 2)) +
        ((m : ℝ) * η - (m : ℝ) * (a : ℝ)) *
          (logFactorialMean (a + 1) + ((a + 1 : ℕ) : ℝ) ^ 2 / (8 * (m : ℝ) ^ 2) -
            (logFactorialMean a + (a : ℝ) ^ 2 / (8 * (m : ℝ) ^ 2))) -
          (V + (m : ℝ) * η ^ 2) / (8 * (m : ℝ) ^ 2) =
      (m : ℝ) * balancedLogFactorialMean m - V / (8 * (m : ℝ) ^ 2) +
        θ * (1 - θ) / (8 * (m : ℝ)) := by
    dsimp [balancedLogFactorialMean, θ, a, η]
    push_cast
    field_simp
    ring
  have hs' : (∑ i, logFactorialMean (d i)) ≤
      (m : ℝ) * balancedLogFactorialMean m - V / (8 * (m : ℝ) ^ 2) +
        θ * (1 - θ) / (8 * (m : ℝ)) := by
    rw [hV] at hs
    linear_combination hs + he
  have ht : θ * (1 - θ) ≤ 1 / 4 := by nlinarith [sq_nonneg (θ - 1 / 2)]
  have ht' : θ * (1 - θ) / (8 * (m : ℝ)) ≤ 1 / (32 * (m : ℝ)) := by
    calc
      _ ≤ (1 / 4 : ℝ) / (8 * (m : ℝ)) := div_le_div_of_nonneg_right ht (by positivity)
      _ = _ := by field_simp; norm_num
  change (∑ i, logFactorialMean (d i)) ≤
    (m : ℝ) * balancedLogFactorialMean m - V / (8 * (m : ℝ) ^ 2) + 1 / (32 * (m : ℝ))
  linarith

theorem degreeVariance_eq_score_sum {n : ℕ} (T : Tournament n) :
    degreeVariance T = (∑ i, score T i ^ 2) / 4 := by
  unfold degreeVariance
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [score_eq_twice_rowDegree]
  ring

/-- Applying the quantitative degree bound to the actual tournament
adjacency. No graph regularity assumption is made. -/
theorem adjacency_permanent_le_balanced_variance {n : ℕ} (T : Tournament n) (hn : 3 ≤ n) :
    (adjacency T).permanent ≤ Real.exp ((n : ℝ) * balancedLogFactorialMean n -
      degreeVariance T / (8 * (n : ℝ) ^ 2) + 1 / (32 * (n : ℝ))) := by
  by_cases hp : 0 < (adjacency T).permanent
  · have hd (i : Fin n) : 1 ≤ rowDegree T.val i ∧ rowDegree T.val i ≤ n - 1 := by
      constructor
      · by_contra h
        have hz : rowDegree T.val i = 0 := by omega
        have he := boolMatrix_permanent_eq_zero_of_rowDegree_zero T.val i hz
        change (adjacency T).permanent = 0 at he
        rw [he] at hp
        exact (lt_irrefl 0 hp)
      · exact rowDegree_le_order_pred T i
    have hlog := boolMatrix_permanent_log_le_bregman T.val hp
    have hv := logFactorialMean_degree_variance n hn (rowDegree T.val) hd (rowDegree_sum T)
    change Real.log (adjacency T).permanent ≤ ∑ i, logFactorialMean (rowDegree T.val i) at hlog
    rw [← Real.exp_log hp]
    exact Real.exp_le_exp.mpr (hlog.trans hv)
  · have hnonneg : 0 ≤ (adjacency T).permanent := by
      change 0 ≤ (boolMatrix T.val).permanent
      rw [← matching_card_eq_permanent T.val]
      positivity
    exact (by linarith : (adjacency T).permanent ≤ 0).trans (Real.exp_pos _).le

end TournamentHamiltonian
