import TournamentHamiltonian.PairedPermanentRestoration

namespace TournamentHamiltonian

theorem nonnegative_fraction_mul_le_abs (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x * y ≤ |y| := by
  exact (mul_le_mul_of_nonneg_left (le_abs_self y) hx0).trans
    (mul_le_of_le_one_left (abs_nonneg y) hx1)

theorem retained_mass_power_le (n m : ℕ) (M Q : ℝ)
    (hn : 1 < n) (hm : 0 < m) (hmn : m ≤ n) (hM : 0 < M) (hQ : 0 < Q) :
    (((n : ℝ) - 1) * M * Q / ((n : ℝ) ^ 2 * (m : ℝ))) ^ m ≤
      Real.exp (-(m : ℝ) / n + |M - n| + |Q - m|) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  let a := ((n : ℝ) - 1) / n
  let b := M / n
  let c := Q / m
  have ha : 0 < a := div_pos (by linarith) hn0
  have hb : 0 < b := div_pos hM hn0
  have hc : 0 < c := div_pos hQ hm0
  have hbase : ((n : ℝ) - 1) * M * Q / ((n : ℝ) ^ 2 * (m : ℝ)) = a * b * c := by
    dsimp [a, b, c]
    ring
  have hfrac : (m : ℝ) / n ≤ 1 := (div_le_one hn0).mpr hmnR
  have hla := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos ha) hm0.le
  have hlb := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hb) hm0.le
  have hlc := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hc) hm0.le
  have hea : (m : ℝ) * (a - 1) = -(m : ℝ) / n := by dsimp [a]; field_simp; ring
  have heb : (m : ℝ) * (b - 1) = ((m : ℝ) / n) * (M - n) := by dsimp [b]; field_simp
  have hec : (m : ℝ) * (c - 1) = Q - m := by dsimp [c]; field_simp
  rw [hea] at hla
  rw [heb] at hlb
  rw [hec] at hlc
  have hboundb := hlb.trans (nonnegative_fraction_mul_le_abs ((m : ℝ) / n) (M - n)
    (div_nonneg hm0.le hn0.le) hfrac)
  have hboundc := hlc.trans (le_abs_self (Q - m))
  have hlog : (m : ℝ) * Real.log (a * b * c) ≤ -(m : ℝ) / n + |M - n| + |Q - m| := by
    rw [Real.log_mul (mul_pos ha hb).ne' hc.ne', Real.log_mul ha.ne' hb.ne']
    linarith
  rw [hbase]
  calc
    _ = Real.exp ((m : ℝ) * Real.log (a * b * c)) := by
      rw [Real.exp_nat_mul, Real.exp_log (mul_pos (mul_pos ha hb) hc)]
    _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem preconditioning_mass_power_le {n t : ℕ} (T : Tournament n)
    (hn : 2 ≤ n) (ht : t < n) (I J : Finset (Fin n))
    (hM : 0 < matrixEntryMass (preconditionedTournamentDensity T))
    (hQ : 0 < matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J)) :
    ((n - 1 : ℝ) / ((n - t : ℝ) * preconditioningDeletionEta (t := t) T I J)) ^ (n - t) ≤
      Real.exp (-1 + (t : ℝ) / n + |matrixEntryMass (preconditionedTournamentDensity T) - n| +
        |matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) -
          (n - t : ℝ)|) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hc : ((n - t : ℕ) : ℝ) = (n - t : ℝ) := by rw [Nat.cast_sub ht.le]
  have hm0 : (n - t : ℝ) ≠ 0 := by
    have htn : (t : ℝ) < n := by exact_mod_cast ht
    linarith
  have heq : (n - 1 : ℝ) / ((n - t : ℝ) * preconditioningDeletionEta (t := t) T I J) =
      ((n : ℝ) - 1) * matrixEntryMass (preconditionedTournamentDensity T) *
        matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) /
          ((n : ℝ) ^ 2 * ((n - t : ℕ) : ℝ)) := by
    unfold preconditioningDeletionEta
    rw [hc]
    field_simp [hn0, hm0, hM.ne', hQ.ne']
  have h := retained_mass_power_le n (n - t) _ _ (by omega) (by omega) (Nat.sub_le _ _) hM hQ
  rw [heq]
  apply h.trans_eq
  rw [hc]
  congr 1
  field_simp [hn0]
  ring

end TournamentHamiltonian
