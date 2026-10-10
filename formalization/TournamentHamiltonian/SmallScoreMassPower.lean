import TournamentHamiltonian.SmallScoreLogBounds

namespace TournamentHamiltonian

theorem baseline_mass_power_log_error (n m : ℕ) (hn : 2 ≤ n) (hmn : m ≤ n) :
    |(m : ℝ)*Real.log (1-1/(n : ℝ))+1| ≤ ((n : ℝ)-m+2)/n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hu : (1 : ℝ)/n ≤ 1/2 := (div_le_iff₀ hn0).mpr (by linarith)
  have h : |(m : ℝ)*(Real.log (1-1/(n : ℝ))+1/n)| ≤ (m : ℝ)*(2*(1/(n : ℝ))^2) := by
    simpa only [abs_mul,abs_of_nonneg hm0] using
      mul_le_mul_of_nonneg_left (abs_log_one_sub_add_self_le (1/(n : ℝ)) (by positivity) hu) hm0
  have he : (m : ℝ)*Real.log (1-1/(n : ℝ))+1 =
      (m : ℝ)*(Real.log (1-1/(n : ℝ))+1/n)+((n : ℝ)-m)/n := by field_simp; ring
  rw [he]
  have hd : 0 ≤ ((n : ℝ)-m)/n := div_nonneg (by linarith) hn0.le
  calc
    _ ≤ |(m : ℝ)*(Real.log (1-1/(n : ℝ))+1/n)|+|((n : ℝ)-m)/n| := abs_add_le _ _
    _ ≤ (m : ℝ)*(2*(1/(n : ℝ))^2)+((n : ℝ)-m)/n :=
      add_le_add h (le_of_eq (abs_of_nonneg hd))
    _ ≤ 2/n+((n : ℝ)-m)/n := by
      apply add_le_add
      · calc
        (m : ℝ)*(2*(1/(n : ℝ))^2) ≤ (n : ℝ)*(2*(1/(n : ℝ))^2) :=
          mul_le_mul_of_nonneg_right hmnR (by positivity)
        _ = 2/n := by field_simp
      · exact le_rfl
    _ = _ := by ring

theorem retained_mass_power_log_error (n m : ℕ) (M Q : ℝ)
    (hn : 2 ≤ n) (hm : 0 < m) (hmn : m ≤ n)
    (hM : (n : ℝ)/2 ≤ M) (hQ : (m : ℝ)/2 ≤ Q) :
    |Real.log ((((n : ℝ)-1)*M*Q/((n : ℝ)^2*(m : ℝ)))^m)+1| ≤
      ((n : ℝ)-m+2)/n+2*|M-n|+2*|Q-m| := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hMp : 0 < M := by linarith
  have hQp : 0 < Q := by linarith
  let a := 1-1/(n : ℝ)
  let b := M/(n : ℝ)
  let c := Q/(m : ℝ)
  have ha : 0 < a := by dsimp [a]; have := (div_le_iff₀ hn0).mpr (by linarith : (1 : ℝ)≤1/2*n); linarith
  have hb : 0 < b := div_pos hMp hn0
  have hc : 0 < c := div_pos hQp hm0
  have hbhalf : 1/2 ≤ b := (le_div_iff₀ hn0).mpr (by dsimp [b] at *; linarith)
  have hchalf : 1/2 ≤ c := (le_div_iff₀ hm0).mpr (by dsimp [c] at *; linarith)
  have hbabs : |b-1| = |M-n|/n := by
    have he : b-1=(M-n)/n := by dsimp [b]; field_simp
    rw [he,abs_div,abs_of_pos hn0]
  have hcabs : |c-1| = |Q-m|/m := by
    have he : c-1=(Q-m)/m := by dsimp [c]; field_simp
    rw [he,abs_div,abs_of_pos hm0]
  have hla := baseline_mass_power_log_error n m hn hmn
  have hlb := mul_le_mul_of_nonneg_left (abs_log_le_twice_sub_one b hbhalf) hm0.le
  have hlc := mul_le_mul_of_nonneg_left (abs_log_le_twice_sub_one c hchalf) hm0.le
  rw [hbabs] at hlb
  rw [hcabs] at hlc
  have hbscale : (m : ℝ)*(2*(|M-n|/n)) ≤ 2*|M-n| := by
    calc
      _ ≤ (n : ℝ)*(2*(|M-n|/n)) := mul_le_mul_of_nonneg_right hmnR (by positivity)
      _ = _ := by field_simp
  have hcscale : (m : ℝ)*(2*(|Q-m|/m))=2*|Q-m| := by field_simp
  have he : ((n : ℝ)-1)*M*Q/((n : ℝ)^2*(m : ℝ))=a*b*c := by dsimp [a,b,c]; field_simp
  rw [he,Real.log_pow,Real.log_mul (mul_pos ha hb).ne' hc.ne',Real.log_mul ha.ne' hb.ne']
  have he2 : (m : ℝ)*(Real.log a+Real.log b+Real.log c)+1 =
      ((m : ℝ)*Real.log a+1)+(m : ℝ)*Real.log b+(m : ℝ)*Real.log c := by ring
  rw [he2]
  have htri := (abs_add_le (((m : ℝ)*Real.log a+1)+(m : ℝ)*Real.log b) ((m : ℝ)*Real.log c)).trans
    (add_le_add (abs_add_le ((m : ℝ)*Real.log a+1) ((m : ℝ)*Real.log b)) (le_refl _))
  rw [abs_mul,abs_mul,abs_of_pos hm0] at htri
  exact htri.trans (add_le_add (add_le_add hla (hlb.trans hbscale)) (hlc.trans_eq hcscale))

theorem preconditioning_mass_power_log_error {n t : ℕ} (T : Tournament n)
    (hn : 2≤n) (ht : t<n) (I J : Finset (Fin n))
    (hM : (n : ℝ)/2≤matrixEntryMass (preconditionedTournamentDensity T))
    (hQ : (n-t : ℝ)/2≤matrixEntryMass
      (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J)) :
    |Real.log (((n-1 : ℝ)/((n-t : ℝ)*preconditioningDeletionEta (t := t) T I J))^(n-t))+1| ≤
      ((t : ℝ)+2)/n+2*|matrixEntryMass (preconditionedTournamentDensity T)-n|+
        2*|matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J)-(n-t : ℝ)| := by
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0 : ℝ)<n := by linarith
  have htn : (t : ℝ)<n := by exact_mod_cast ht
  have hm0 : 0<(n-t : ℝ) := by linarith
  have hMp : 0<matrixEntryMass (preconditionedTournamentDensity T) := by linarith
  have hQp : 0<matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) := by linarith
  have hc : ((n-t : ℕ) : ℝ)=(n-t : ℝ) := Nat.cast_sub ht.le
  have he : (n-1 : ℝ)/((n-t : ℝ)*preconditioningDeletionEta (t := t) T I J) =
      ((n : ℝ)-1)*matrixEntryMass (preconditionedTournamentDensity T)*
        matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J)/
          ((n : ℝ)^2*((n-t : ℕ) : ℝ)) := by
    unfold preconditioningDeletionEta
    rw [hc]
    field_simp [hn0.ne',hm0.ne',hMp.ne',hQp.ne']
  have h := retained_mass_power_log_error n (n-t)
    (matrixEntryMass (preconditionedTournamentDensity T))
    (matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J))
    hn (by omega) (Nat.sub_le _ _) hM (by rwa [hc])
  rw [he]
  apply h.trans_eq
  rw [hc]
  congr 2
  ring

end TournamentHamiltonian
