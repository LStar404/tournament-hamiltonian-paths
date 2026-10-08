import TournamentHamiltonian.BregmanRanks
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The actual unused-column counts and their exact row-order averages
for the Brégman permanent bound. -/

namespace TournamentHamiltonian

open scoped Classical

noncomputable def matchingOwnerSupport {n : ℕ} (M : Fin n → Fin n → Bool)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun x => M i (σ x) = true)

theorem matchingOwnerSupport_card {n : ℕ} (M : Fin n → Fin n → Bool)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (matchingOwnerSupport M σ i).card = rowDegree M i := by
  unfold rowDegree
  apply Finset.card_bij (fun x _ => σ x)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ h
    exact σ.injective h
  · intro y hy
    refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
    simp only [matchingOwnerSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.apply_symm_apply]
    exact (Finset.mem_filter.mp hy).2

theorem matchingOwnerSupport_self {n : ℕ} (M : Fin n → Fin n → Bool)
    (σ : SupportedMatchings M) (i : Fin n) : i ∈ matchingOwnerSupport M σ.val i :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.property i⟩

/-- The available columns of the actual matching are exactly the as-yet
unrevealed owners among this row's allowed neighbors. -/
theorem remainingSupport_card_eq_rowOrderRank {n : ℕ}
    (M : Fin n → Fin n → Bool) (τ σ : Equiv.Perm (Fin n)) (k : Fin n) :
    (remainingSupport (fun i => M (τ i)) Finset.univ (fun i => σ (τ i)) k).card =
      rowOrderRank (matchingOwnerSupport M σ (τ k)) τ (τ k) := by
  unfold rowOrderRank orderedSupportRank
  rw [τ.symm_apply_apply]
  apply Finset.card_bij (fun j _ => τ.symm (σ.symm j))
  · intro j hj
    obtain ⟨_, hjM, hj⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_map.mpr
      refine ⟨σ.symm j, ?_, rfl⟩
      simpa only [matchingOwnerSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.apply_symm_apply] using hjM
    · change k.val ≤ (τ.symm (σ.symm j)).val
      by_contra h
      have hh := hj (τ.symm (σ.symm j)) (by omega)
      exact hh (by simp)
  · intro j _ l _ h
    exact σ.symm.injective (τ.symm.injective h)
  · intro l hl
    obtain ⟨hlS, hkl⟩ := Finset.mem_filter.mp hl
    obtain ⟨x, hx, hxl⟩ := Finset.mem_map.mp hlS
    have hxM := (Finset.mem_filter.mp hx).2
    have hτ : τ l = x := by
      rw [← hxl]
      simp
    refine ⟨σ (τ l), ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa only [hτ] using hxM
    · intro a hak h
      have hal := τ.injective (σ.injective h)
      subst a
      change k.val ≤ l.val at hkl
      omega

/-- Exact code length expressed in terms of each row's owner support. -/
theorem matchingCodeWeight_neg_log_eq_ranks {n : ℕ}
    (M : Fin n → Fin n → Bool) (τ : Equiv.Perm (Fin n)) (σ : SupportedMatchings M) :
    -Real.log (matchingCodeWeight M τ σ) =
      ∑ i : Fin n, Real.log (rowOrderRank (matchingOwnerSupport M σ.val i) τ i : ℝ) := by
  unfold matchingCodeWeight
  rw [neg_log_greedyMatchingWeight (fun i => M (τ i)) Finset.univ
    (fun i => σ.val (τ i)) (σ.val.injective.comp τ.injective)
    (fun i => ⟨Finset.mem_univ _, σ.property (τ i)⟩)]
  simp_rw [remainingSupport_card_eq_rowOrderRank]
  exact τ.bijective.sum_comp (fun i : Fin n =>
    Real.log (rowOrderRank (matchingOwnerSupport M σ.val i) τ i : ℝ))

/-- The exact factorial average for each actual matching; every support
is nonempty because its selected column belongs to that support. -/
theorem sum_matchingCodeWeight_neg_log {n : ℕ}
    (M : Fin n → Fin n → Bool) (σ : SupportedMatchings M) :
    (∑ τ : Equiv.Perm (Fin n), -Real.log (matchingCodeWeight M τ σ)) =
      (n.factorial : ℝ) * ∑ i : Fin n,
        Real.log ((rowDegree M i).factorial : ℝ) / (rowDegree M i : ℝ) := by
  simp_rw [matchingCodeWeight_neg_log_eq_ranks]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := rowOrderRank_log_average (matchingOwnerSupport M σ.val i) i
    (matchingOwnerSupport_self M σ i)
  rw [matchingOwnerSupport_card, Fintype.card_fin] at h
  have hd : (0 : ℝ) < rowDegree M i := by
    exact_mod_cast (show 0 < rowDegree M i from by
      rw [← matchingOwnerSupport_card M σ.val i]
      exact Finset.card_pos.mpr ⟨i, matchingOwnerSupport_self M σ i⟩)
  apply (mul_left_cancel₀ hd.ne')
  rw [h]
  field_simp

/-- Brégman's logarithmic row-degree bound for an arbitrary Boolean matrix,
proved by averaging the actual random-greedy code over all row orders. -/
theorem boolMatrix_permanent_log_le_bregman {n : ℕ} (M : Fin n → Fin n → Bool)
    (hpos : 0 < (boolMatrix M).permanent) :
    Real.log (boolMatrix M).permanent ≤ ∑ i : Fin n,
      Real.log ((rowDegree M i).factorial : ℝ) / (rowDegree M i : ℝ) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (fun τ _ => permanent_log_le_greedy_code M τ)
  rw [Finset.sum_comm] at h
  simp_rw [sum_matchingCodeWeight_neg_log] at h
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin] at h
  rw [matching_card_eq_permanent] at h
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have he : (n.factorial : ℝ) * (boolMatrix M).permanent * Real.log (boolMatrix M).permanent ≤
      ((n.factorial : ℝ) * (boolMatrix M).permanent) *
        (∑ i : Fin n, Real.log ((rowDegree M i).factorial : ℝ) / (rowDegree M i : ℝ)) := by
    nlinarith [h]
  exact le_of_mul_le_mul_left he (mul_pos hf hpos)

noncomputable def bregmanRowFactor (d : ℕ) : ℝ :=
  if d = 0 then 0 else (d.factorial : ℝ) ^ (1 / (d : ℝ))

theorem bregmanRowFactor_nonneg (d : ℕ) : 0 ≤ bregmanRowFactor d := by
  unfold bregmanRowFactor
  split_ifs <;> positivity

/-- The full Brégman bound, including matrices with zero rows and the empty
matrix. Its factors are zero at degree zero. -/
theorem boolMatrix_permanent_le_bregman {n : ℕ} (M : Fin n → Fin n → Bool) :
    (boolMatrix M).permanent ≤ ∏ i : Fin n, bregmanRowFactor (rowDegree M i) := by
  have hpnonneg : 0 ≤ (boolMatrix M).permanent := by
    rw [← matching_card_eq_permanent]
    positivity
  by_cases hpos : 0 < (boolMatrix M).permanent
  · have hmatch : Nonempty (SupportedMatchings M) := Fintype.card_pos_iff.mp (by
      rw [← matching_card_eq_permanent] at hpos
      exact_mod_cast hpos)
    obtain ⟨σ⟩ := hmatch
    have hd (i : Fin n) : rowDegree M i ≠ 0 := by
      have h := Finset.card_pos.mpr ⟨i, matchingOwnerSupport_self M σ i⟩
      rw [matchingOwnerSupport_card] at h
      omega
    calc
      _ = Real.exp (Real.log (boolMatrix M).permanent) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (∑ i : Fin n,
          Real.log ((rowDegree M i).factorial : ℝ) / (rowDegree M i : ℝ)) :=
        Real.exp_le_exp.mpr (boolMatrix_permanent_log_le_bregman M hpos)
      _ = _ := by
        rw [Real.exp_sum]
        apply Finset.prod_congr rfl
        intro i _
        rw [bregmanRowFactor, ite_eq_right (hd i), Real.rpow_def_of_pos (by positivity)]
        congr 1
        ring
  · have hpzero : (boolMatrix M).permanent = 0 := by linarith
    rw [hpzero]
    exact Finset.prod_nonneg (fun i _ => bregmanRowFactor_nonneg _)

/-- The arbitrary-matrix inequality applied to the tournament's real
adjacency, with its actual outgoing degrees. -/
theorem adjacency_permanent_le_bregman {n : ℕ} (T : Tournament n) :
    (adjacency T).permanent ≤ ∏ i : Fin n, bregmanRowFactor (rowDegree T.val i) :=
  boolMatrix_permanent_le_bregman T.val

/-- The same inequality on every finite index type, without assuming a
particular vertex labeling. -/
theorem boolMatrix_permanent_le_bregman_fintype {α : Type*} [Fintype α] [DecidableEq α]
    (M : α → α → Bool) :
    (boolMatrix M).permanent ≤ ∏ i : α, bregmanRowFactor (rowDegree M i) := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let M' : Fin (Fintype.card α) → Fin (Fintype.card α) → Bool :=
    fun i j => M (e.symm i) (e.symm j)
  have hp : (boolMatrix M).permanent = (boolMatrix M').permanent := by
    unfold Matrix.permanent
    apply Fintype.sum_equiv (Equiv.permCongr e)
    intro σ
    apply Fintype.prod_equiv e
    intro i
    simp [boolMatrix, M', Equiv.permCongr_apply]
  have hd (i : α) : rowDegree M i = rowDegree M' (e i) := by
    unfold rowDegree rowSupport
    apply Finset.card_bij (fun j _ => e j)
    · intro j hj
      simpa [M'] using hj
    · intro j _ k _ h
      exact e.injective h
    · intro j hj
      refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
      simpa [M'] using hj
  calc
    _ = (boolMatrix M').permanent := hp
    _ ≤ ∏ j : Fin (Fintype.card α), bregmanRowFactor (rowDegree M' j) :=
      boolMatrix_permanent_le_bregman M'
    _ = _ := by
      symm
      apply Fintype.prod_equiv e
      intro i
      rw [hd]

/-- Brégman's inequality for an arbitrary real zero-one matrix. -/
theorem zeroOneMatrix_permanent_le_bregman {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (hA : ∀ i j, A i j = 0 ∨ A i j = 1) :
    A.permanent ≤ ∏ i : α,
      bregmanRowFactor ((Finset.univ.filter (fun j : α => A i j = 1)).card) := by
  let M : α → α → Bool := fun i j => decide (A i j = 1)
  have he : boolMatrix M = A := by
    ext i j
    rcases hA i j with h | h <;> simp [boolMatrix, M, h]
  have hd (i : α) : rowDegree M i =
      (Finset.univ.filter (fun j : α => A i j = 1)).card := by
    simp [rowDegree, rowSupport, M]
  simpa only [he, hd] using boolMatrix_permanent_le_bregman_fintype M

/-- Direct Brégman bounds for every actual principal adjacency submatrix. -/
theorem adjacency_principal_permanent_le_bregman {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) :
    ((adjacency T).submatrix (Subtype.val : U → Fin n) Subtype.val).permanent ≤
      ∏ i : U, bregmanRowFactor
        ((Finset.univ.filter (fun j : U => T.val i.val j.val = true)).card) := by
  change (boolMatrix (fun i j : U => T.val i.val j.val)).permanent ≤ _
  exact boolMatrix_permanent_le_bregman_fintype (fun i j : U => T.val i.val j.val)

end TournamentHamiltonian
