import TournamentHamiltonian.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Finite counting and subprobability coding for the Brégman row-degree
bound. The random greedy assignment is defined on actual Boolean matrices;
its total mass and coding inequality are proved without assuming Brégman. -/

namespace TournamentHamiltonian

open scoped Classical

noncomputable def boolMatrix {α : Type*} (M : α → α → Bool) : Matrix α α ℝ :=
  fun i j => if M i j then 1 else 0

def SupportedPermutation {α : Type*} (M : α → α → Bool) (σ : Equiv.Perm α) : Prop :=
  ∀ i, M i (σ i) = true

noncomputable def supportedPermutations {α : Type*} [Fintype α] [DecidableEq α]
    (M : α → α → Bool) : Finset (Equiv.Perm α) :=
  Finset.univ.filter (SupportedPermutation M)

noncomputable def rowSupport {α β : Type*} [Fintype β] (M : α → β → Bool) (i : α) : Finset β :=
  Finset.univ.filter (fun j => M i j = true)

noncomputable def rowDegree {α β : Type*} [Fintype β] (M : α → β → Bool) (i : α) : ℕ :=
  (rowSupport M i).card

theorem boolMatrix_permanent_eq_supported_card {α : Type*} [Fintype α] [DecidableEq α]
    (M : α → α → Bool) :
    (boolMatrix M).permanent = ((supportedPermutations M).card : ℝ) := by
  rw [← Matrix.permanent_transpose]
  unfold Matrix.permanent supportedPermutations
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hs : SupportedPermutation M σ
  · simp only [hs, ite_true, Nat.cast_one]
    apply Finset.prod_eq_one
    intro i _
    simp [Matrix.transpose_apply, boolMatrix, hs i]
  · simp only [hs, ite_false]
    obtain ⟨i, hi⟩ := not_forall.mp hs
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [boolMatrix, hi])

theorem boolMatrix_permanent_eq_zero_of_rowDegree_zero {α : Type*}
    [Fintype α] [DecidableEq α] (M : α → α → Bool) (i : α)
    (hi : rowDegree M i = 0) : (boolMatrix M).permanent = 0 := by
  rw [boolMatrix_permanent_eq_supported_card]
  have he : rowSupport M i = ∅ := Finset.card_eq_zero.mp hi
  have hm (j : α) : M i j ≠ true := by
    intro h
    have : j ∈ rowSupport M i := by simp [rowSupport, h]
    simp [he] at this
  have hs : supportedPermutations M = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro σ hσ
    exact hm (σ i) ((Finset.mem_filter.mp hσ).2 i)
  simp [hs]

noncomputable def uniformChoice {β : Type*} [Fintype β] [DecidableEq β]
    (S : Finset β) (j : β) : ℝ := if j ∈ S then 1 / (S.card : ℝ) else 0

theorem uniformChoice_nonneg {β : Type*} [Fintype β] [DecidableEq β]
    (S : Finset β) (j : β) : 0 ≤ uniformChoice S j := by
  unfold uniformChoice
  split_ifs <;> positivity

theorem uniformChoice_sum {β : Type*} [Fintype β] [DecidableEq β] (S : Finset β) :
    (∑ j, uniformChoice S j) = if S.card = 0 then 0 else 1 := by
  unfold uniformChoice
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul]
  by_cases h : S.card = 0
  · simp [h]
  · simp [h, Nat.cast_ne_zero.mpr h]

theorem uniformChoice_sum_le_one {β : Type*} [Fintype β] [DecidableEq β]
    (S : Finset β) : (∑ j, uniformChoice S j) ≤ 1 := by
  rw [uniformChoice_sum]
  split_ifs <;> norm_num

theorem uniformChoice_pos {β : Type*} [Fintype β] [DecidableEq β]
    (S : Finset β) {j : β} (hj : j ∈ S) : 0 < uniformChoice S j := by
  have hc : 0 < S.card := Finset.card_pos.mpr ⟨j, hj⟩
  simp only [uniformChoice, ite_eq_left hj]
  positivity

/-- The probability of a prescribed injective matching under the random
row-by-row greedy process, with failures contributing zero. -/
noncomputable def greedyMatchingWeight {β : Type*} [Fintype β] [DecidableEq β] :
    {n : ℕ} → (Fin n → β → Bool) → Finset β → (Fin n → β) → ℝ
  | 0, _, _, _ => 1
  | _n + 1, M, S, p =>
      uniformChoice (S.filter (fun j => M 0 j = true)) (p 0) *
        greedyMatchingWeight (fun i => M i.succ) (S.erase (p 0)) (fun i => p i.succ)

theorem greedyMatchingWeight_nonneg {β : Type*} [Fintype β] [DecidableEq β]
    {n : ℕ} (M : Fin n → β → Bool) (S : Finset β) (p : Fin n → β) :
    0 ≤ greedyMatchingWeight M S p := by
  induction n generalizing S with
  | zero => simp [greedyMatchingWeight]
  | succ n ih => exact mul_nonneg (uniformChoice_nonneg _ _) (ih _ _ _)

theorem greedyMatchingWeight_pos {β : Type*} [Fintype β] [DecidableEq β]
    {n : ℕ} (M : Fin n → β → Bool) (S : Finset β) (p : Fin n → β)
    (hp : Function.Injective p) (hm : ∀ i, p i ∈ S ∧ M i (p i) = true) :
    0 < greedyMatchingWeight M S p := by
  induction n generalizing S with
  | zero => simp [greedyMatchingWeight]
  | succ n ih =>
    apply mul_pos
    · exact uniformChoice_pos _ (Finset.mem_filter.mpr (hm 0))
    · apply ih _ _ _
      · exact hp.comp (Fin.succ_injective n)
      · intro i
        exact ⟨Finset.mem_erase.mpr ⟨fun h => Fin.succ_ne_zero i (hp h), (hm i.succ).1⟩,
          (hm i.succ).2⟩

/-- The entire greedy assignment tree has mass at most one, even if some
prefix has no available column. -/
theorem sum_greedyMatchingWeight_le_one {β : Type*} [Fintype β] [DecidableEq β]
    {n : ℕ} (M : Fin n → β → Bool) (S : Finset β) :
    (∑ p : Fin n → β, greedyMatchingWeight M S p) ≤ 1 := by
  induction n generalizing S with
  | zero => simp [greedyMatchingWeight]
  | succ n ih =>
    calc
      _ = ∑ p : β × (Fin n → β),
          uniformChoice (S.filter (fun j => M 0 j = true)) p.1 *
            greedyMatchingWeight (fun i => M i.succ) (S.erase p.1) p.2 := by
        apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => β)).symm
        intro p
        rfl
      _ = ∑ j : β, uniformChoice (S.filter (fun j => M 0 j = true)) j *
          ∑ p : Fin n → β,
            greedyMatchingWeight (fun i => M i.succ) (S.erase j) p := by
        rw [Fintype.sum_prod_type]
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ j : β, uniformChoice (S.filter (fun j => M 0 j = true)) j := by
        apply Finset.sum_le_sum
        intro j _
        exact (mul_le_mul_of_nonneg_left (ih _ _) (uniformChoice_nonneg _ _)).trans_eq (mul_one _)
      _ ≤ 1 := uniformChoice_sum_le_one _

/-- The elementary coding bound used in the entropy proof. No probability
measure or entropy axiom is required: `log x ≤ x−1` suffices. -/
theorem cardinal_log_le_neg_log_sum {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (q : Ω → ℝ) (hq : ∀ x, 0 < q x) (hmass : (∑ x, q x) ≤ 1) :
    (Fintype.card Ω : ℝ) * Real.log (Fintype.card Ω) ≤ ∑ x, -Real.log (q x) := by
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hi (x : Ω) : Real.log (Fintype.card Ω) + Real.log (q x) ≤
      (Fintype.card Ω : ℝ) * q x - 1 := by
    simpa only [Real.log_mul hc.ne' (hq x).ne'] using
      Real.log_le_sub_one_of_pos (mul_pos hc (hq x))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hi x)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.card_univ] at hs
  have hm := mul_le_mul_of_nonneg_left hmass hc.le
  rw [Finset.sum_neg_distrib]
  linarith

/-- Restricting a nonnegative finite sum to an injectively encoded collection
cannot increase its total mass. -/
theorem finite_code_mass_le {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (hf : Function.Injective f) (q : Λ → ℝ) (hq : ∀ y, 0 ≤ q y) :
    (∑ x : Ω, q (f x)) ≤ ∑ y : Λ, q y := by
  calc
    _ = ∑ y ∈ Finset.univ.image f, q y := by
      rw [Finset.sum_image]
      exact fun x _ y _ h => hf h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => hq y)

abbrev SupportedMatchings {α : Type*} (M : α → α → Bool) :=
  {σ : Equiv.Perm α // SupportedPermutation M σ}

/-- The actual random-greedy code mass of a supported permutation with an
arbitrary row-revelation order. -/
noncomputable def matchingCodeWeight {n : ℕ} (M : Fin n → Fin n → Bool)
    (τ : Equiv.Perm (Fin n)) (σ : SupportedMatchings M) : ℝ :=
  greedyMatchingWeight (fun i => M (τ i)) Finset.univ (fun i => σ.val (τ i))

theorem matchingCodeWeight_pos {n : ℕ} (M : Fin n → Fin n → Bool)
    (τ : Equiv.Perm (Fin n)) (σ : SupportedMatchings M) :
    0 < matchingCodeWeight M τ σ := by
  apply greedyMatchingWeight_pos
  · exact σ.val.injective.comp τ.injective
  · intro i
    exact ⟨Finset.mem_univ _, σ.property (τ i)⟩

theorem sum_matchingCodeWeight_le_one {n : ℕ} (M : Fin n → Fin n → Bool)
    (τ : Equiv.Perm (Fin n)) : (∑ σ : SupportedMatchings M, matchingCodeWeight M τ σ) ≤ 1 := by
  let code : SupportedMatchings M → (Fin n → Fin n) := fun σ i => σ.val (τ i)
  have hcode : Function.Injective code := by
    intro σ ρ h
    apply Subtype.ext
    apply Equiv.ext
    intro j
    obtain ⟨i, rfl⟩ := τ.surjective j
    exact congrFun h i
  exact (finite_code_mass_le code hcode
    (greedyMatchingWeight (fun i => M (τ i)) Finset.univ)
    (greedyMatchingWeight_nonneg _ _)).trans (sum_greedyMatchingWeight_le_one _ _)

theorem matching_card_eq_permanent {α : Type*} [Fintype α] [DecidableEq α]
    (M : α → α → Bool) :
    (Fintype.card (SupportedMatchings M) : ℝ) = (boolMatrix M).permanent := by
  rw [boolMatrix_permanent_eq_supported_card]
  congr 1
  exact Fintype.card_subtype _

/-- Entropy's counting step for actual supported permutations: its code
length bounds `permanent * log permanent`. The remaining Brégman step is
the exact averaging of available-column ranks over all row orderings. -/
theorem permanent_log_le_greedy_code {n : ℕ} (M : Fin n → Fin n → Bool)
    (τ : Equiv.Perm (Fin n)) :
    (boolMatrix M).permanent * Real.log (boolMatrix M).permanent ≤
      ∑ σ : SupportedMatchings M, -Real.log (matchingCodeWeight M τ σ) := by
  by_cases h : Nonempty (SupportedMatchings M)
  · have := h
    simpa only [matching_card_eq_permanent] using
      cardinal_log_le_neg_log_sum (matchingCodeWeight M τ)
        (matchingCodeWeight_pos M τ) (sum_matchingCodeWeight_le_one M τ)
  · have : IsEmpty (SupportedMatchings M) := not_nonempty_iff.mp h
    rw [← matching_card_eq_permanent]
    simp

/-- The actual unused allowed columns before row `i` is revealed. -/
noncomputable def remainingSupport {β : Type*} [Fintype β] [DecidableEq β]
    {n : ℕ} (M : Fin n → β → Bool) (S : Finset β) (p : Fin n → β) (i : Fin n) : Finset β :=
  S.filter (fun j => M i j = true ∧ ∀ k : Fin n, k.val < i.val → p k ≠ j)

theorem remainingSupport_zero {β : Type*} [Fintype β] [DecidableEq β]
    {n : ℕ} (M : Fin (n + 1) → β → Bool) (S : Finset β) (p : Fin (n + 1) → β) :
    remainingSupport M S p 0 = S.filter (fun j => M 0 j = true) := by
  ext j
  simp [remainingSupport]

theorem remainingSupport_succ {β : Type*} [Fintype β] [DecidableEq β]
    {n : ℕ} (M : Fin (n + 1) → β → Bool) (S : Finset β) (p : Fin (n + 1) → β)
    (i : Fin n) :
    remainingSupport (fun k => M k.succ) (S.erase (p 0)) (fun k => p k.succ) i =
      remainingSupport M S p i.succ := by
  ext j
  simp only [remainingSupport, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hj0, hjS⟩, hjM, hj⟩
    refine ⟨hjS, hjM, ?_⟩
    intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · intro _ h
      exact hj0 h.symm
    · intro hl
      exact hj l (by simp only [Fin.val_succ] at hl; omega)
  · rintro ⟨hjS, hjM, hj⟩
    refine ⟨⟨?_, hjS⟩, hjM, ?_⟩
    · exact fun h => hj 0 (by simp) h.symm
    · intro k hk
      exact hj k.succ (by simp only [Fin.val_succ]; omega)

theorem remainingSupport_contains_assignment {β : Type*} [Fintype β] [DecidableEq β]
    {n : ℕ} (M : Fin n → β → Bool) (S : Finset β) (p : Fin n → β)
    (hp : Function.Injective p) (hm : ∀ i, p i ∈ S ∧ M i (p i) = true)
    (i : Fin n) : p i ∈ remainingSupport M S p i := by
  apply Finset.mem_filter.mpr
  refine ⟨(hm i).1, (hm i).2, ?_⟩
  intro k hk h
  have heq := hp h
  subst k
  exact (Nat.lt_irrefl _ hk)

/-- The greedy code length is exactly the sum of log available-column counts. -/
theorem neg_log_greedyMatchingWeight {β : Type*} [Fintype β] [DecidableEq β]
    {n : ℕ} (M : Fin n → β → Bool) (S : Finset β) (p : Fin n → β)
    (hp : Function.Injective p) (hm : ∀ i, p i ∈ S ∧ M i (p i) = true) :
    -Real.log (greedyMatchingWeight M S p) =
      ∑ i : Fin n, Real.log ((remainingSupport M S p i).card : ℝ) := by
  induction n generalizing S with
  | zero => simp [greedyMatchingWeight]
  | succ n ih =>
    have hhead : p 0 ∈ S.filter (fun j => M 0 j = true) := Finset.mem_filter.mpr (hm 0)
    have htail : ∀ i : Fin n, p i.succ ∈ S.erase (p 0) ∧ M i.succ (p i.succ) = true := by
      intro i
      exact ⟨Finset.mem_erase.mpr ⟨fun h => Fin.succ_ne_zero i (hp h), (hm i.succ).1⟩,
        (hm i.succ).2⟩
    have hptail : Function.Injective (fun i : Fin n => p i.succ) := hp.comp (Fin.succ_injective n)
    have htpos := greedyMatchingWeight_pos (fun i => M i.succ) (S.erase (p 0)) _ hptail htail
    have hcpos : (0 : ℝ) < (S.filter (fun j => M 0 j = true)).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨p 0, hhead⟩
    rw [greedyMatchingWeight, Real.log_mul (uniformChoice_pos _ hhead).ne' htpos.ne',
      neg_add_rev, Fin.sum_univ_succ, remainingSupport_zero]
    rw [ih _ _ _ hptail htail]
    simp only [uniformChoice, ite_eq_left hhead,
      Real.log_div one_ne_zero hcpos.ne', Real.log_one, zero_sub, neg_neg]
    simp_rw [remainingSupport_succ]
    ring

end TournamentHamiltonian
