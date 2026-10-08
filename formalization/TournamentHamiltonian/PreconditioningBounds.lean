import TournamentHamiltonian.PairedPreconditioning

namespace TournamentHamiltonian

theorem pairedW_nonneg (a : ℝ) (ha : -1 < a ∧ a < 1) : 0 ≤ pairedW a := by
  have habs : |a| < 1 := abs_lt.mpr ha
  have hs : a ^ 2 < 1 := by
    have h := (sq_lt_sq₀ (abs_nonneg a) (by norm_num : (0 : ℝ) ≤ 1)).mpr habs
    simpa only [sq_abs, one_pow] using h
  unfold pairedW
  exact div_nonneg (sq_nonneg _) (by linarith)

theorem pairedV_decomposition (a : ℝ) (ha : -1 < a ∧ a < 1) :
    pairedV a = a + a * pairedW a := by
  have hp : 1 + a ≠ 0 := by linarith [ha.1]
  have hm : 1 - a ≠ 0 := by linarith [ha.2]
  have hd : 1 - a ^ 2 ≠ 0 := by nlinarith [mul_ne_zero hp hm]
  unfold pairedV pairedW
  field_simp [hd]
  ring

theorem pairedW_le_score_sq (a a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : |a| ≤ a0) :
    pairedW a ≤ a ^ 2 / (1 - a0 ^ 2) := by
  have hsq : a0 ^ 2 < 1 := by
    simpa using ((sq_lt_sq₀ h0 (by norm_num : (0 : ℝ) ≤ 1)).mpr h1)
  have hgap : 0 < 1 - a0 ^ 2 := by linarith
  have hs := pow_le_pow_left₀ (abs_nonneg a) ha 2
  rw [sq_abs] at hs
  unfold pairedW
  exact div_le_div_of_nonneg_left (sq_nonneg a) hgap (by linarith)

theorem pairedV_sq_le_score_sq (a a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : |a| ≤ a0) :
    pairedV a ^ 2 ≤ a ^ 2 / (1 - a0 ^ 2) ^ 2 := by
  have hsq : a0 ^ 2 < 1 := by
    simpa using ((sq_lt_sq₀ h0 (by norm_num : (0 : ℝ) ≤ 1)).mpr h1)
  have hgap : 0 < 1 - a0 ^ 2 := by linarith
  have hs := pow_le_pow_left₀ (abs_nonneg a) ha 2
  rw [sq_abs] at hs
  have hga : 0 < 1 - a ^ 2 := by linarith
  have hden : (1 - a0 ^ 2) ^ 2 ≤ (1 - a ^ 2) ^ 2 := by nlinarith
  rw [pairedV, div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg a) (sq_pos_of_pos hgap) hden

theorem pairedV_sum_abs_le_W {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, -1 < a i ∧ a i < 1) (hsum : ∑ i, a i = 0) :
    |∑ i, pairedV (a i)| ≤ ∑ i, pairedW (a i) := by
  have hV : (∑ i, pairedV (a i)) = ∑ i, a i * pairedW (a i) := by
    simp only [pairedV_decomposition (a _) (ha _), Finset.sum_add_distrib, hsum, zero_add]
  rw [hV]
  calc
    _ ≤ ∑ i, |a i * pairedW (a i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (pairedW_nonneg (a i) (ha i))]
      exact mul_le_of_le_one_left (pairedW_nonneg (a i) (ha i)) (abs_lt.mpr (ha i)).le

noncomputable def scoreVariance {n : ℕ} (T : Tournament n) : ℝ :=
  ∑ i, tournamentScorePotential T i ^ 2

theorem tournamentScorePotential_sum {n : ℕ} (T : Tournament n) :
    (∑ i, tournamentScorePotential T i) = 0 := by
  simp only [tournamentScorePotential, ← Finset.sum_div, score_sum_zero, zero_div]

theorem preconditioned_W_le_variance {n : ℕ} (T : Tournament n) (a0 : ℝ)
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    (∑ i, pairedW (tournamentScorePotential T i)) ≤ scoreVariance T / (1 - a0 ^ 2) := by
  rw [scoreVariance, Finset.sum_div]
  exact Finset.sum_le_sum (fun i _ => pairedW_le_score_sq _ a0 h0 h1 (ha i))

theorem preconditioned_v_sq_le_variance {n : ℕ} (T : Tournament n) (a0 : ℝ)
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    (∑ i, pairedV (tournamentScorePotential T i) ^ 2) ≤ scoreVariance T / (1 - a0 ^ 2) ^ 2 := by
  rw [scoreVariance, Finset.sum_div]
  exact Finset.sum_le_sum (fun i _ => pairedV_sq_le_score_sq _ a0 h0 h1 (ha i))

theorem scoreVariance_nonneg {n : ℕ} (T : Tournament n) : 0 ≤ scoreVariance T :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem scoreVariance_eq_score_sq {n : ℕ} (T : Tournament n) :
    scoreVariance T = (∑ i, score T i ^ 2) / (n - 1 : ℝ) ^ 2 := by
  simp only [scoreVariance, tournamentScorePotential, div_pow, Finset.sum_div]

theorem preconditioned_V_abs_le_W {n : ℕ} (T : Tournament n)
    (ha : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1) :
    |∑ i, pairedV (tournamentScorePotential T i)| ≤ ∑ i, pairedW (tournamentScorePotential T i) :=
  pairedV_sum_abs_le_W _ ha (tournamentScorePotential_sum T)

theorem signMatrix_entry_abs_le_one {n : ℕ} (T : Tournament n) (i j : Fin n) :
    |signMatrix T i j| ≤ 1 := by
  by_cases hij : i = j
  · simp [signMatrix, hij]
  · cases h : T.val i j <;> simp [signMatrix, hij, h]

theorem signMatrix_mulVec_abs_le {n : ℕ} (T : Tournament n) (v : Fin n → ℝ) (i : Fin n) :
    |(signMatrix T).mulVec v i| ≤ ∑ j, |v j| := by
  unfold Matrix.mulVec dotProduct
  calc
    _ ≤ ∑ j, |signMatrix T i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (signMatrix_entry_abs_le_one T i j) (abs_nonneg (v j))

theorem nonneg_skew_bilinear_abs_le {n : ℕ} (T : Tournament n) (v w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    |dotProduct w ((signMatrix T).mulVec v)| ≤ (∑ i, w i) * ∑ j, |v j| := by
  unfold dotProduct
  calc
    _ ≤ ∑ i, |w i * (signMatrix T).mulVec v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i * ∑ j, |v j| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (signMatrix_mulVec_abs_le T v i) (hw i)
    _ = _ := by rw [Finset.sum_mul]

theorem preconditioned_mass_abs_le_W {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (ha : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1) :
    |matrixEntryMass (preconditionedTournamentDensity T) - n| ≤
      (2 * (∑ i, pairedW (tournamentScorePotential T i)) ^ 2 +
        (∑ i, pairedW (tournamentScorePotential T i)) +
        2 * (∑ i, pairedW (tournamentScorePotential T i)) *
          (∑ j, |pairedV (tournamentScorePotential T j)|)) / (n - 1 : ℝ) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hw : ∀ i, 0 ≤ pairedW (tournamentScorePotential T i) := fun i => pairedW_nonneg _ (ha i)
  have hW : 0 ≤ ∑ i, pairedW (tournamentScorePotential T i) :=
    Finset.sum_nonneg (fun i _ => hw i)
  have hV := preconditioned_V_abs_le_W T ha
  have hVsq := pow_le_pow_left₀ (abs_nonneg _) hV 2
  rw [sq_abs] at hVsq
  have hbil := nonneg_skew_bilinear_abs_le T
    (fun i => pairedV (tournamentScorePotential T i))
    (fun i => pairedW (tournamentScorePotential T i)) hw
  rw [preconditionedTournamentDensity_mass T hn ha, abs_div,
    abs_of_pos (by linarith : 0 < (n : ℝ) - 1)]
  apply div_le_div_of_nonneg_right _ (by linarith)
  apply abs_le.mpr
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbil
  constructor <;> nlinarith [sq_nonneg (∑ i, pairedV (tournamentScorePotential T i)),
    sq_nonneg (∑ i, pairedW (tournamentScorePotential T i))]

theorem preconditioned_v_l1_le_variance {n : ℕ} (T : Tournament n) (a0 : ℝ)
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    (∑ i, |pairedV (tournamentScorePotential T i)|) ≤
      Real.sqrt (n : ℝ) * Real.sqrt (scoreVariance T) / (1 - a0 ^ 2) := by
  have hsq : a0 ^ 2 < 1 := by
    simpa using ((sq_lt_sq₀ h0 (by norm_num : (0 : ℝ) ≤ 1)).mpr h1)
  have hgap : 0 < 1 - a0 ^ 2 := by linarith
  have hC := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n))
    (fun i => |pairedV (tournamentScorePotential T i)|) (fun _ => 1)
  simp only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hC
  calc
    _ ≤ Real.sqrt (∑ i, pairedV (tournamentScorePotential T i) ^ 2) * Real.sqrt (n : ℝ) := by
      simpa only [mul_one] using hC
    _ ≤ Real.sqrt (scoreVariance T / (1 - a0 ^ 2) ^ 2) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (preconditioned_v_sq_le_variance T a0 h0 h1 ha)) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_div (scoreVariance_nonneg T), Real.sqrt_sq hgap.le]
      ring

theorem preconditioned_mass_abs_le_variance {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    |matrixEntryMass (preconditionedTournamentDensity T) - n| ≤
      (2 * (scoreVariance T / (1 - a0 ^ 2)) ^ 2 + scoreVariance T / (1 - a0 ^ 2) +
        2 * (scoreVariance T / (1 - a0 ^ 2)) *
          (Real.sqrt (n : ℝ) * Real.sqrt (scoreVariance T) / (1 - a0 ^ 2))) / (n - 1 : ℝ) := by
  have ha' : ∀ i, -1 < tournamentScorePotential T i ∧ tournamentScorePotential T i < 1 :=
    fun i => abs_lt.mp ((ha i).trans_lt h1)
  have hW : 0 ≤ ∑ i, pairedW (tournamentScorePotential T i) :=
    Finset.sum_nonneg (fun i _ => pairedW_nonneg _ (ha' i))
  have hL : 0 ≤ ∑ i, |pairedV (tournamentScorePotential T i)| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hw := preconditioned_W_le_variance T a0 h0 h1 ha
  have hl := preconditioned_v_l1_le_variance T a0 h0 h1 ha
  have hwsq := pow_le_pow_left₀ hW hw 2
  have hprod := mul_le_mul hw hl hL (hW.trans hw)
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  exact (preconditioned_mass_abs_le_W T hn ha').trans
    (div_le_div_of_nonneg_right (by nlinarith) (by linarith))

private theorem mass_budget_algebra (n τ g : ℝ) (hn : 2 ≤ n) (hτ : 0 ≤ τ)
    (hg : 0 < g) (hg1 : g ≤ 1) :
    (2 * (τ / g) ^ 2 + τ / g + 2 * (τ / g) * (Real.sqrt n * Real.sqrt τ / g)) /
        (n - 1) ≤ (4 / g ^ 2) * ((τ + τ ^ 2) / n + τ * Real.sqrt (τ / n)) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hroot : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hden : (1 : ℝ) / (n - 1) ≤ 2 / n := by
    apply (div_le_div_iff₀ hn1 hn0).mpr
    linarith
  have hnum : 0 ≤ 2 * (τ / g) ^ 2 + τ / g + 2 * (τ / g) * (Real.sqrt n * Real.sqrt τ / g) := by
    positivity
  have heq : (2 * (τ / g) ^ 2 + τ / g + 2 * (τ / g) * (Real.sqrt n * Real.sqrt τ / g)) * (2 / n) =
      4 * τ ^ 2 / (g ^ 2 * n) + 2 * τ / (g * n) +
        (4 / g ^ 2) * τ * Real.sqrt (τ / n) := by
    rw [Real.sqrt_div hτ]
    field_simp [hg.ne', hn0.ne', hroot.ne']
    ring_nf
    rw [Real.sq_sqrt hn0.le]
    ring
  have hlinear : 2 * τ / (g * n) ≤ 4 * τ / (g ^ 2 * n) := by
    apply (div_le_div_iff₀ (by positivity : 0 < g * n) (by positivity : 0 < g ^ 2 * n)).mpr
    have hsmall : 2 * τ * g ≤ 4 * τ := by
      nlinarith [mul_nonneg hτ (sub_nonneg.mpr hg1)]
    have hscaled := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ g * n)
    nlinarith
  calc
    _ ≤ (2 * (τ / g) ^ 2 + τ / g + 2 * (τ / g) * (Real.sqrt n * Real.sqrt τ / g)) * (2 / n) := by
      simpa only [div_eq_mul_inv, one_div, one_mul] using mul_le_mul_of_nonneg_left hden hnum
    _ = _ := heq
    _ ≤ 4 * τ ^ 2 / (g ^ 2 * n) + 4 * τ / (g ^ 2 * n) +
        (4 / g ^ 2) * τ * Real.sqrt (τ / n) := by linarith
    _ = _ := by ring

/-- A finite, uniform version of the manuscript's paired full-mass error. -/
theorem preconditioned_mass_error_bound {n : ℕ} (T : Tournament n) (hn : 1 < n)
    (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0) :
    |matrixEntryMass (preconditionedTournamentDensity T) - n| ≤
      (4 / (1 - a0 ^ 2) ^ 2) *
        ((scoreVariance T + scoreVariance T ^ 2) / n +
          scoreVariance T * Real.sqrt (scoreVariance T / n)) := by
  have hsq : a0 ^ 2 < 1 := by
    simpa using ((sq_lt_sq₀ h0 (by norm_num : (0 : ℝ) ≤ 1)).mpr h1)
  exact (preconditioned_mass_abs_le_variance T hn a0 h0 h1 ha).trans
    (mass_budget_algebra n (scoreVariance T) (1 - a0 ^ 2)
      (by exact_mod_cast (Nat.succ_le_of_lt hn)) (scoreVariance_nonneg T)
      (by linarith) (by nlinarith [sq_nonneg a0]))

end TournamentHamiltonian
