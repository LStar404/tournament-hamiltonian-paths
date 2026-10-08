import TournamentHamiltonian.AlternatingTournament

namespace TournamentHamiltonian

def relabelTournament {n : ℕ} (T : Tournament n) (e : Equiv.Perm (Fin n)) : Tournament n :=
  ⟨fun i j => T.val (e i) (e j), by
    constructor
    · intro i
      exact T.property.1 (e i)
    · intro i j hne
      exact T.property.2 (e i) (e j) (fun h => hne (e.injective h))⟩

theorem signMatrix_relabelTournament {n : ℕ} (T : Tournament n) (e : Equiv.Perm (Fin n)) :
    signMatrix (relabelTournament T e) = (signMatrix T).submatrix e e := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [signMatrix]
  · have he : e i ≠ e j := fun h => hij (e.injective h)
    simp [signMatrix, relabelTournament, hij, he, Matrix.submatrix_apply]
    rfl

theorem score_relabelTournament {n : ℕ} (T : Tournament n) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    score (relabelTournament T e) i = score T (e i) := by
  rw [score, signMatrix_relabelTournament]
  exact Equiv.sum_comp e (fun j => signMatrix T (e i) j)

theorem complexKernel_det_relabelTournament {n : ℕ} (T : Tournament n)
    (e : Equiv.Perm (Fin n)) (z : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + z • complexSignMatrix (relabelTournament T e)).det =
      ((1 : Matrix (Fin n) (Fin n) ℂ) + z • complexSignMatrix T).det := by
  have heq : (1 : Matrix (Fin n) (Fin n) ℂ) + z • complexSignMatrix (relabelTournament T e) =
      ((1 : Matrix (Fin n) (Fin n) ℂ) + z • complexSignMatrix T).submatrix e e := by
    ext i j
    simp [complexSignMatrix, signMatrix, relabelTournament, e.injective.eq_iff,
      Matrix.one_apply]
  rw [heq, Matrix.det_submatrix_equiv_self]

theorem determinantRatio_relabelTournament {n : ℕ} (T : Tournament n)
    (e : Equiv.Perm (Fin n)) :
    determinantRatio (relabelTournament T e) = determinantRatio T := by
  simp only [determinantRatio, complexKernel_det_relabelTournament]

theorem isHamiltonian_relabelTournament {n : ℕ} (T : Tournament n)
    (e σ : Equiv.Perm (Fin n)) :
    IsHamiltonian (relabelTournament T e) σ ↔ IsHamiltonian T (σ.trans e) := Iff.rfl

/-- Relabelling preserves path counts. This applies to the permutation part,
and does not assert invariance under the signed diagonal conjugation. -/
theorem pathCount_relabelTournament {n : ℕ} (T : Tournament n) (e : Equiv.Perm (Fin n)) :
    pathCount (relabelTournament T e) = pathCount T := by
  classical
  unfold pathCount
  apply Finset.card_bij (fun σ _ => σ.trans e)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact (isHamiltonian_relabelTournament T e σ).mp hσ
  · intro σ₁ _ σ₂ _ h
    apply Equiv.ext
    intro i
    apply e.injective
    exact congrArg (fun σ : Equiv.Perm (Fin n) => σ i) h
  · intro σ hσ
    refine ⟨σ.trans e.symm, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      apply (isHamiltonian_relabelTournament T e _).mpr
      have heq : (σ.trans e.symm).trans e = σ := by
        apply Equiv.ext
        intro i
        simp
      rw [heq]
      exact hσ
    · ext i
      simp

/-- On residues 0,...,2m, an arc points forward by 1,...,m steps modulo 2m+1.
The piecewise definition avoids a choice of representatives in modular arithmetic. -/
def carouselTournament (m : ℕ) : Tournament (2 * m + 1) :=
  ⟨fun i j => if i < j then decide (j.val - i.val ≤ m)
    else if j < i then decide (m < i.val - j.val) else false, by
    constructor
    · intro i
      simp
    · intro i j hne
      rcases lt_or_gt_of_ne hne with hij | hji
      · simp only [ite_eq_left hij, ite_eq_right (not_lt_of_ge hij.le),
          ← decide_not, not_lt]
      · simp only [ite_eq_left hji, ite_eq_right (not_lt_of_ge hji.le),
          ← decide_not, not_le]⟩

/-- The piecewise construction is exactly the forward-residue definition. -/
theorem carouselTournament_residue_arc (m : ℕ) (i j : Fin (2 * m + 1)) :
    (carouselTournament m).val i j =
      decide (0 < (j.val + (2 * m + 1) - i.val) % (2 * m + 1) ∧
        (j.val + (2 * m + 1) - i.val) % (2 * m + 1) ≤ m) := by
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hval : j.val + (2 * m + 1) - i.val = (2 * m + 1) + (j.val - i.val) := by
      have h : i.val < j.val := hij
      omega
    have hd : j.val - i.val < 2 * m + 1 := by omega
    have hdpos : 0 < j.val - i.val := by
      have h : i.val < j.val := hij
      omega
    simp [carouselTournament, hij, hval, Nat.mod_eq_of_lt hd, hdpos]
  · have hval : i.val + (2 * m + 1) - i.val = 2 * m + 1 := by omega
    simp [carouselTournament, hval]
  · have h : j.val < i.val := hji
    have hd : j.val + (2 * m + 1) - i.val < 2 * m + 1 := by omega
    have hdpos : 0 < j.val + (2 * m + 1) - i.val := by omega
    simp only [carouselTournament, ite_eq_right (not_lt_of_ge hji.le), ite_eq_left hji,
      Nat.mod_eq_of_lt hd, hdpos, true_and]
    have heq : (m < i.val - j.val) ↔ j.val + (2 * m + 1) - i.val ≤ m := by omega
    exact decide_eq_decide.mpr heq

/-- The manuscript's explicit ordering 0,2,...,2m,1,3,...,2m-1. -/
def carouselOrderMap (m : ℕ) (i : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  ⟨if i.val ≤ m then 2 * i.val else 2 * (i.val - m) - 1, by
    split_ifs with hi <;> omega⟩

theorem carouselOrderMap_even (m : ℕ) (i : Fin (2 * m + 1)) :
    Even (carouselOrderMap m i).val ↔ i.val ≤ m := by
  unfold carouselOrderMap
  dsimp
  split_ifs with hi
  · exact iff_of_true ⟨i.val, by omega⟩ hi
  · have ho : Odd (2 * (i.val - m) - 1) := ⟨i.val - m - 1, by omega⟩
    exact iff_of_false (Nat.not_even_iff_odd.mpr ho) hi

theorem carouselOrderMap_injective (m : ℕ) : Function.Injective (carouselOrderMap m) := by
  intro i j hij
  have he := congrArg (fun x : Fin (2 * m + 1) => x.val) hij
  have hpar : (i.val ≤ m) ↔ j.val ≤ m := by
    rw [← carouselOrderMap_even, ← carouselOrderMap_even, hij]
  apply Fin.ext
  dsimp [carouselOrderMap] at he
  by_cases hi : i.val ≤ m
  · have hj := hpar.mp hi
    simp only [ite_eq_left hi, ite_eq_left hj] at he
    omega
  · have hj : ¬j.val ≤ m := fun h => hi (hpar.mpr h)
    simp only [ite_eq_right hi, ite_eq_right hj] at he
    omega

noncomputable def carouselOrder (m : ℕ) : Equiv.Perm (Fin (2 * m + 1)) :=
  Equiv.ofBijective (carouselOrderMap m)
    ⟨carouselOrderMap_injective m, Finite.surjective_of_injective (carouselOrderMap_injective m)⟩

private theorem carousel_relabel_above (m : ℕ) (i j : Fin (2 * m + 1)) (hij : i < j) :
    (carouselTournament m).val i j =
      (alternatingTournament (2 * m + 1)).val (carouselOrderMap m i) (carouselOrderMap m j) := by
  have hiv := i.isLt
  have hjv := j.isLt
  have hijv : i.val < j.val := hij
  simp only [carouselTournament, ite_eq_left hij]
  simp only [alternatingTournament, carouselOrderMap_even]
  by_cases hi : i.val ≤ m <;> by_cases hj : j.val ≤ m
  · have hq : carouselOrderMap m i < carouselOrderMap m j := by
      simp only [carouselOrderMap, Fin.lt_def, ite_eq_left hi, ite_eq_left hj]
      omega
    have hd : j.val - i.val ≤ m := by omega
    simp [hi, hj, hq, hd]
  · have hpar : ¬(i.val ≤ m ↔ j.val ≤ m) := by simp [hi, hj]
    by_cases hd : j.val - i.val ≤ m
    · have hq : carouselOrderMap m j < carouselOrderMap m i := by
        simp only [carouselOrderMap, Fin.lt_def, ite_eq_left hi, ite_eq_right hj]
        omega
      simp [hpar, hq, not_lt_of_ge hq.le, hd]
    · have hq : carouselOrderMap m i < carouselOrderMap m j := by
        simp only [carouselOrderMap, Fin.lt_def, ite_eq_left hi, ite_eq_right hj]
        omega
      simp [hpar, hq, hd]
  · omega
  · have hq : carouselOrderMap m i < carouselOrderMap m j := by
      simp only [carouselOrderMap, Fin.lt_def, ite_eq_right hi, ite_eq_right hj]
      omega
    have hd : j.val - i.val ≤ m := by omega
    simp [hi, hj, hq, hd]

/-- Exact orientation check for the carousel relabelling, at every odd order. -/
theorem carousel_relabel (m : ℕ) (i j : Fin (2 * m + 1)) :
    (carouselTournament m).val i j =
      (alternatingTournament (2 * m + 1)).val (carouselOrder m i) (carouselOrder m j) := by
  change (carouselTournament m).val i j =
    (alternatingTournament (2 * m + 1)).val (carouselOrderMap m i) (carouselOrderMap m j)
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact carousel_relabel_above m i j hij
  · simp only [(carouselTournament m).property.1,
      (alternatingTournament (2 * m + 1)).property.1]
  · rw [(carouselTournament m).property.2 i j (ne_of_gt hji),
      (alternatingTournament (2 * m + 1)).property.2 _ _
        (fun h => (ne_of_gt hji) (carouselOrderMap_injective m h)),
      carousel_relabel_above m j i hji]

theorem carouselTournament_eq_relabel (m : ℕ) :
    carouselTournament m = relabelTournament (alternatingTournament (2 * m + 1))
      (carouselOrder m) := by
  apply Subtype.ext
  funext i j
  exact carousel_relabel m i j

theorem carouselTournament_score (m : ℕ) (i : Fin (2 * m + 1)) :
    score (carouselTournament m) i = 0 := by
  rw [carouselTournament_eq_relabel, score_relabelTournament]
  exact score_alternatingTournament_odd ⟨m, rfl⟩ _

theorem carouselTournament_determinantRatio (m : ℕ) :
    determinantRatio (carouselTournament m) = transitiveRatio (2 * m + 1) := by
  rw [carouselTournament_eq_relabel, determinantRatio_relabelTournament,
    determinantRatio_alternatingTournament]

noncomputable def carouselDeletionMap (m : ℕ) (i : Fin (2 * m)) : Fin (2 * m + 1) :=
  (carouselOrder m).symm i.castSucc

theorem carouselDeletionMap_injective (m : ℕ) : Function.Injective (carouselDeletionMap m) := by
  intro i j hij
  apply Fin.castSucc_injective
  exact (carouselOrder m).symm.injective hij

/-- A one-vertex deletion from the actual odd carousel, labelled in the
remaining signed-transitive order. -/
noncomputable def evenCarouselTournament (m : ℕ) : Tournament (2 * m) :=
  ⟨fun i j => (carouselTournament m).val (carouselDeletionMap m i) (carouselDeletionMap m j), by
    constructor
    · intro i
      exact (carouselTournament m).property.1 _
    · intro i j hne
      exact (carouselTournament m).property.2 _ _
        (fun h => hne (carouselDeletionMap_injective m h))⟩

theorem evenCarouselTournament_eq_alternating (m : ℕ) :
    evenCarouselTournament m = alternatingTournament (2 * m) := by
  apply Subtype.ext
  funext i j
  change (carouselTournament m).val (carouselDeletionMap m i) (carouselDeletionMap m j) = _
  rw [carousel_relabel]
  simp only [carouselDeletionMap, Equiv.apply_symm_apply, alternatingTournament_deletion]

theorem evenCarouselTournament_score (m : ℕ) (i : Fin (2 * m)) :
    |score (evenCarouselTournament m) i| = 1 := by
  rw [evenCarouselTournament_eq_alternating]
  exact score_alternatingTournament_even (n := 2 * m) ⟨m, by omega⟩ i

theorem evenCarouselTournament_determinantRatio (m : ℕ) :
    determinantRatio (evenCarouselTournament m) = transitiveRatio (2 * m) := by
  rw [evenCarouselTournament_eq_alternating, determinantRatio_alternatingTournament]

/-- The deletion embedding misses exactly one vertex of the odd carousel. -/
theorem carouselDeletionMap_range (m : ℕ) :
    Set.range (carouselDeletionMap m) =
      {v | v ≠ (carouselOrder m).symm (Fin.last (2 * m))} := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩ h
    have heq : i.castSucc = Fin.last (2 * m) := (carouselOrder m).symm.injective h
    have hval := congrArg (fun x : Fin (2 * m + 1) => x.val) heq
    have hi := i.isLt
    simp only [Fin.val_castSucc, Fin.val_last] at hval
    omega
  · intro hv
    have hn : carouselOrder m v ≠ Fin.last (2 * m) := by
      intro h
      apply hv
      rw [← h, Equiv.symm_apply_apply]
    have hlt : (carouselOrder m v).val < 2 * m := by
      have hb := (carouselOrder m v).isLt
      have hvn : (carouselOrder m v).val ≠ 2 * m := by
        intro h
        exact hn (Fin.ext h)
      omega
    let i : Fin (2 * m) := ⟨(carouselOrder m v).val, hlt⟩
    refine ⟨i, ?_⟩
    have hi : i.castSucc = carouselOrder m v := Fin.ext rfl
    simp only [carouselDeletionMap, hi, Equiv.symm_apply_apply]

theorem carouselTournament_kernel_det (m : ℕ) (z : ℂ) :
    ((1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℂ) +
      z • complexSignMatrix (carouselTournament m)).det =
      ((1 + z) ^ (2 * m + 1) + (1 - z) ^ (2 * m + 1)) / 2 := by
  rw [carouselTournament_eq_relabel, complexKernel_det_relabelTournament,
    complexSignMatrix_alternatingTournament, alternatingSkew_det]

theorem evenCarouselTournament_kernel_det (m : ℕ) (z : ℂ) :
    ((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ) +
      z • complexSignMatrix (evenCarouselTournament m)).det =
      ((1 + z) ^ (2 * m) + (1 - z) ^ (2 * m)) / 2 := by
  rw [evenCarouselTournament_eq_alternating, complexSignMatrix_alternatingTournament,
    alternatingSkew_det]

/-- One pair of absolute constants covers both actual carousel constructions. -/
theorem carousel_determinantRatios_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ m : ℕ,
      (N ≤ 2 * m + 1 → ‖determinantRatio (carouselTournament m) - (lowerConstant : ℂ)‖ ≤
        C / (2 * m + 1)) ∧
      (N ≤ 2 * m → ‖determinantRatio (evenCarouselTournament m) - (lowerConstant : ℂ)‖ ≤
        C / (2 * m)) := by
  obtain ⟨C, hC, N, hN, hbound⟩ := transitiveRatio_error_bound
  refine ⟨C, hC, N, hN, ?_⟩
  intro m
  constructor
  · intro hn
    rw [carouselTournament_determinantRatio]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hbound _ hn
  · intro hn
    rw [evenCarouselTournament_determinantRatio]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound _ hn

theorem carousel_imaginary_determinants_eventually_ne_zero :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ m : ℕ,
      (N ≤ 2 * m + 1 →
        ((1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℂ) +
          (Complex.I / (2 * m + 1)) • complexSignMatrix (carouselTournament m)).det ≠ 0) ∧
      (N ≤ 2 * m →
        ((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ) +
          (Complex.I / (2 * m)) • complexSignMatrix (evenCarouselTournament m)).det ≠ 0) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp transitiveKernel_imaginary_det_eventually_ne_zero
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro m
  constructor
  · intro hn
    rw [carouselTournament_kernel_det]
    have h := hN (2 * m + 1) ((le_max_left N 1).trans hn)
    simpa only [transitiveKernel_det, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h
  · intro hn
    rw [evenCarouselTournament_kernel_det]
    have h := hN (2 * m) ((le_max_left N 1).trans hn)
    simpa only [transitiveKernel_det, Nat.cast_mul, Nat.cast_ofNat] using h

end TournamentHamiltonian
