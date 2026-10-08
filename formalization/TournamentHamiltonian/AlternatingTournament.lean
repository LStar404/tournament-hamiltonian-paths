import TournamentHamiltonian.PowerApproximation

namespace TournamentHamiltonian

/-- The ordered signed-transitive construction used for the carousel family.
The vertex order is the order before the manuscript's final relabelling. -/
def alternatingTournament (n : ℕ) : Tournament n :=
  ⟨fun i j => if i < j then decide (Even i.val ↔ Even j.val)
    else if j < i then !decide (Even i.val ↔ Even j.val) else false, by
    constructor
    · intro i
      simp
    · intro i j hne
      rcases lt_or_gt_of_ne hne with hij | hji
      · simp [hij, not_lt_of_ge hij.le, iff_comm]
      · simp [hji, not_lt_of_ge hji.le, iff_comm]⟩

section Field

variable {K : Type*} [Field K]

def alternatingSign (k : ℕ) : K := (-1) ^ k

theorem alternatingSign_sq (k : ℕ) : (alternatingSign k : K) ^ 2 = 1 := by
  rcases neg_one_pow_eq_or K k with h | h <;> simp [alternatingSign, h]

def alternatingSkew (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun i j => alternatingSign i.val * alternatingSign j.val * transitiveSkew n i j

def alternatingDiagonal (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal (fun i => alternatingSign i.val)

theorem alternatingDiagonal_mul_self (n : ℕ) :
    (alternatingDiagonal n : Matrix (Fin n) (Fin n) K) * alternatingDiagonal n = 1 := by
  rw [alternatingDiagonal, Matrix.diagonal_mul_diagonal]
  have hentry : (fun i : Fin n => (alternatingSign i.val : K) * alternatingSign i.val) =
      fun _ => 1 := by
    funext i
    exact (pow_two (alternatingSign i.val)).symm.trans (alternatingSign_sq i.val)
  rw [hentry, Matrix.diagonal_one]

theorem alternatingSkew_signed_conjugation (n : ℕ) :
    (alternatingSkew n : Matrix (Fin n) (Fin n) K) =
      alternatingDiagonal n * transitiveSkew n * alternatingDiagonal n := by
  ext i j
  simp only [alternatingDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, alternatingSkew]
  ring

theorem alternatingKernel_signed_conjugation (n : ℕ) (z : K) :
    (1 : Matrix (Fin n) (Fin n) K) + z • alternatingSkew n =
      alternatingDiagonal n * transitiveKernel n z * alternatingDiagonal n := by
  ext i j
  simp only [alternatingDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j
    have hi := alternatingSign_sq (K := K) i.val
    simp [alternatingSkew, transitiveKernel, transitiveSkew, pow_two] at hi ⊢
    exact hi.symm
  · simp [alternatingSkew, transitiveKernel, hij]
    ring

variable [CharZero K]

/-- Signed diagonal conjugation preserves the exact transitive determinant. -/
theorem alternatingSkew_det (n : ℕ) (z : K) :
    ((1 : Matrix (Fin n) (Fin n) K) + z • alternatingSkew n).det =
      ((1 + z) ^ n + (1 - z) ^ n) / 2 := by
  let D : Matrix (Fin n) (Fin n) K := alternatingDiagonal n
  have hp : D.det * D.det = 1 := by
    rw [← Matrix.det_mul, alternatingDiagonal_mul_self, Matrix.det_one]
  rw [alternatingKernel_signed_conjugation, Matrix.det_mul, Matrix.det_mul]
  change D.det * (transitiveKernel n z).det * D.det = _
  calc
    D.det * (transitiveKernel n z).det * D.det =
        (D.det * D.det) * (transitiveKernel n z).det := by ring
    _ = _ := by rw [hp, one_mul, transitiveKernel_det]

end Field

theorem signMatrix_alternatingTournament (n : ℕ) :
    signMatrix (alternatingTournament n) = alternatingSkew n := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · by_cases hi : Even i.val <;> by_cases hj : Even j.val <;>
      simp [signMatrix, alternatingTournament, alternatingSkew, alternatingSign,
        neg_one_pow_eq_ite, hi, hj, hij, ne_of_lt hij,
        transitiveSkew]
  · simp [signMatrix, alternatingSkew, transitiveSkew]
  · by_cases hi : Even i.val <;> by_cases hj : Even j.val <;>
      simp [signMatrix, alternatingTournament, alternatingSkew, alternatingSign,
        neg_one_pow_eq_ite, hi, hj, hji, ne_of_gt hji,
        transitiveSkew, not_lt_of_ge hji.le]

private theorem alternatingSign_sum (n : ℕ) :
    (∑ i : Fin n, (alternatingSign i.val : ℝ)) = (1 - alternatingSign n) / 2 := by
  induction n with
  | zero => simp [alternatingSign]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin n, (alternatingSign i.val : ℝ)) + alternatingSign n = _
    rw [ih]
    simp only [alternatingSign, pow_succ]
    ring

/-- Exact score at every order; odd orders have score zero, even orders ±1. -/
theorem alternatingSkew_row_sum (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, (alternatingSkew n : Matrix (Fin n) (Fin n) ℝ) i j) =
      -(1 + alternatingSign n) / 2 * alternatingSign i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    by_cases hi : i.val = n
    · have heq : i = Fin.last n := Fin.ext hi
      subst i
      rw [Fin.sum_univ_castSucc]
      have hterm : ∀ j : Fin n,
          (alternatingSkew (n + 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
            (Fin.last n) j.castSucc = -alternatingSign n * alternatingSign j.val := by
        intro j
        simp [alternatingSkew, transitiveSkew, Fin.lt_def, j.isLt]
      simp_rw [hterm]
      rw [← Finset.mul_sum, alternatingSign_sum]
      have hs := alternatingSign_sq (K := ℝ) n
      simp only [alternatingSkew, transitiveSkew, lt_self_iff_false, ite_false,
        mul_zero, add_zero, Fin.val_last, alternatingSign, pow_succ] at hs ⊢
      nlinarith
    · let i₀ : Fin n := ⟨i.val, by omega⟩
      have heq : i = i₀.castSucc := Fin.ext rfl
      rw [heq]
      rw [Fin.sum_univ_castSucc]
      have hterm : ∀ j : Fin n,
          (alternatingSkew (n + 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
            i₀.castSucc j.castSucc = alternatingSkew n i₀ j := by
        intro j
        simp only [alternatingSkew, transitiveSkew, Fin.val_castSucc,
          Fin.castSucc_lt_castSucc_iff]
      simp_rw [hterm]
      rw [ih]
      simp [alternatingSkew, transitiveSkew, Fin.lt_def, i₀.isLt,
        alternatingSign, pow_succ]
      ring

theorem score_alternatingTournament (n : ℕ) (i : Fin n) :
    score (alternatingTournament n) i =
      -(1 + alternatingSign n) / 2 * (alternatingSign i.val : ℝ) := by
  rw [score, signMatrix_alternatingTournament, alternatingSkew_row_sum]

theorem score_alternatingTournament_abs_le_one (n : ℕ) (i : Fin n) :
    |score (alternatingTournament n) i| ≤ 1 := by
  rw [score_alternatingTournament]
  rcases neg_one_pow_eq_or ℝ n with hn | hn <;>
    rcases neg_one_pow_eq_or ℝ i.val with hi | hi <;>
    norm_num [alternatingSign, hn, hi]

theorem score_alternatingTournament_odd {n : ℕ} (hn : Odd n) (i : Fin n) :
    score (alternatingTournament n) i = 0 := by
  rw [score_alternatingTournament]
  simp [alternatingSign, hn.neg_one_pow]

theorem score_alternatingTournament_even {n : ℕ} (hn : Even n) (i : Fin n) :
    |score (alternatingTournament n) i| = 1 := by
  rw [score_alternatingTournament]
  simp [alternatingSign, hn.neg_one_pow]

/-- The even-order construction is an actual one-vertex deletion from the
next odd-order construction, before either tournament is relabelled. -/
theorem alternatingTournament_deletion (n : ℕ) (i j : Fin n) :
    (alternatingTournament (n + 1)).val i.castSucc j.castSucc =
      (alternatingTournament n).val i j := by
  simp only [alternatingTournament, Fin.val_castSucc, Fin.castSucc_lt_castSucc_iff]

def complexSignMatrix {n : ℕ} (T : Tournament n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (signMatrix T i j : ℂ)

theorem complexSignMatrix_alternatingTournament (n : ℕ) :
    complexSignMatrix (alternatingTournament n) = alternatingSkew n := by
  ext i j
  rw [complexSignMatrix, signMatrix_alternatingTournament]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [alternatingSkew, alternatingSign, transitiveSkew, hij]
  · simp [alternatingSkew, transitiveSkew]
  · simp [alternatingSkew, alternatingSign, transitiveSkew, hji, not_lt_of_ge hji.le]

/-- The spectral determinant ratio evaluated on the actual tournament matrix. -/
noncomputable def determinantRatio {n : ℕ} (T : Tournament n) : ℂ :=
  ((1 : Matrix (Fin n) (Fin n) ℂ) + ((1 : ℂ) / n) • complexSignMatrix T).det /
    ((1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I / n) • complexSignMatrix T).det

theorem determinantRatio_alternatingTournament (n : ℕ) :
    determinantRatio (alternatingTournament n) = transitiveRatio n := by
  simp only [determinantRatio, complexSignMatrix_alternatingTournament,
    alternatingSkew_det, transitiveRatio, transitiveKernel_det]

theorem determinantRatio_alternatingTournament_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ‖determinantRatio (alternatingTournament n) - (lowerConstant : ℂ)‖ ≤ C / n := by
  simpa only [determinantRatio_alternatingTournament] using transitiveRatio_error_bound

end TournamentHamiltonian
