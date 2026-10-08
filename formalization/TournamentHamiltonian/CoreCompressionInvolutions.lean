import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Dynamics.PeriodicPts.Lemmas
import TournamentHamiltonian.PairingCardinality

/-! Finite paths encoded by two involutions. A fixed-point-free edge involution and
an involution at internal degree-two vertices pair their terminal half-edges. -/

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq

variable {α : Type*}

private theorem involutive_perm_square (s : Equiv.Perm α) (hs : Function.Involutive s) :
    s * s = 1 := by
  ext x
  exact hs x

private theorem involutive_perm_inv (s : Equiv.Perm α) (hs : Function.Involutive s) :
    s⁻¹ = s := by
  apply inv_eq_of_mul_eq_one_left
  exact involutive_perm_square s hs

theorem terminal_reflection_conj (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s) :
    s * (a * s) * s⁻¹ = (a * s)⁻¹ := by
  rw [mul_inv_rev, involutive_perm_inv a ha, involutive_perm_inv s hs]
  simp only [mul_assoc, involutive_perm_square s hs, mul_one]

theorem terminal_reflection_pow (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s) (x : α) (hx : s x = x)
    (k : ℕ) :
    s (((a * s) ^ k) x) = (((a * s) ^ k)⁻¹) x := by
  have h : s * (a * s) ^ k * s⁻¹ = ((a * s) ^ k)⁻¹ := by
    rw [← conj_pow, terminal_reflection_conj a s ha hs, inv_pow]
  have he := congrArg (fun p : Equiv.Perm α => p x) h
  simpa only [Equiv.Perm.mul_apply, involutive_perm_inv s hs, hx] using he

theorem terminal_reflection_fixed_iff (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s) (x : α) (hx : s x = x)
    (k : ℕ) :
    s (((a * s) ^ k) x) = ((a * s) ^ k) x ↔ ((a * s) ^ (2 * k)) x = x := by
  rw [terminal_reflection_pow a s ha hs x hx]
  constructor
  · intro hf
    have hh := congrArg ((a * s) ^ k) hf
    simpa only [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply,
      ← pow_add, ← two_mul] using hh.symm
  · intro hf
    apply ((a * s) ^ k).injective
    simpa only [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply,
      ← pow_add, ← two_mul] using hf.symm

variable [Fintype α]

noncomputable def involutionPathPeriod (a s : Equiv.Perm α) (x : α) : ℕ :=
  Function.minimalPeriod (a * s) x

theorem involutionPathPeriod_pos (a s : Equiv.Perm α) (x : α) :
    0 < involutionPathPeriod a s x :=
  Function.minimalPeriod_pos_of_mem_periodicPts ((a * s).injective.mem_periodicPts x)

omit [Fintype α] in
theorem involutionPathPeriod_pow (a s : Equiv.Perm α) (x : α) :
    ((a * s) ^ involutionPathPeriod a s x) x = x := by
  exact (Equiv.Perm.coe_pow _ _ ▸ Function.iterate_minimalPeriod)

theorem involutionPathPeriod_at_pow (a s : Equiv.Perm α) (x : α) (k : ℕ) :
    involutionPathPeriod a s (((a * s) ^ k) x) = involutionPathPeriod a s x := by
  simpa only [involutionPathPeriod, Equiv.Perm.coe_pow] using
    Function.minimalPeriod_apply_iterate ((a * s).injective.mem_periodicPts x) k

omit [Fintype α] in
/-- Every path orbit with a terminal has even length. Fixed-point-free edge
reversal rules out an odd reflection orbit. -/
theorem terminal_involutionPathPeriod_even (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s)
    (hfree : ∀ x, a x ≠ x) (x : α) (hx : s x = x) :
    Even (involutionPathPeriod a s x) := by
  let p := a * s
  let m := involutionPathPeriod a s x
  by_contra hn
  have hr : m % 2 = 1 := by
    have hn' : ¬ m % 2 = 0 := by simpa only [Nat.even_iff] using hn
    omega
  let k := m / 2 + 1
  have hk : 2 * k = m + 1 := by omega
  have hp : (p ^ (2 * k)) x = p x := by
    rw [hk, pow_succ', Equiv.Perm.mul_apply]
    exact congrArg p (involutionPathPeriod_pow a s x)
  have hf : a ((p ^ k) x) = (p ^ k) x := by
    apply (p ^ k).injective
    calc
      (p ^ k) (a ((p ^ k) x)) = (p ^ k) (p (s ((p ^ k) x))) := by
        change (p ^ k) (a ((p ^ k) x)) = (p ^ k) (a (s (s ((p ^ k) x))))
        rw [hs]
      _ = (p ^ k * p * (p ^ k)⁻¹) x := by
        rw [terminal_reflection_pow a s ha hs x hx]
        rfl
      _ = p x := by rw [← pow_succ, pow_succ', mul_assoc, mul_inv_cancel, mul_one]
      _ = (p ^ k) ((p ^ k) x) := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, ← two_mul]
        exact hp.symm
  exact hfree _ hf

noncomputable def pathTerminalPartner (a s : Equiv.Perm α) (x : α) : α :=
  ((a * s) ^ (involutionPathPeriod a s x / 2)) x

omit [Fintype α] in
theorem pathTerminalPartner_fixed (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s)
    (hfree : ∀ x, a x ≠ x) (x : α) (hx : s x = x) :
    s (pathTerminalPartner a s x) = pathTerminalPartner a s x := by
  apply (terminal_reflection_fixed_iff a s ha hs x hx _).mpr
  have he := terminal_involutionPathPeriod_even a s ha hs hfree x hx
  have hd := Nat.mod_add_div (involutionPathPeriod a s x) 2
  rw [Nat.even_iff.mp he, zero_add] at hd
  rw [hd, involutionPathPeriod_pow]

theorem pathTerminalPartner_ne (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s)
    (hfree : ∀ x, a x ≠ x) (x : α) (hx : s x = x) :
    pathTerminalPartner a s x ≠ x := by
  have he := Nat.even_iff.mp (terminal_involutionPathPeriod_even a s ha hs hfree x hx)
  have hp := involutionPathPeriod_pos a s x
  have hd := Nat.mod_add_div (involutionPathPeriod a s x) 2
  have hk : involutionPathPeriod a s x / 2 < involutionPathPeriod a s x := by omega
  intro hn
  have hz : 0 < involutionPathPeriod a s x := hp
  have hh : involutionPathPeriod a s x / 2 = 0 := by
    apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hk hz).mp
    simpa only [pathTerminalPartner, ← Equiv.Perm.coe_pow, pow_zero, Equiv.Perm.one_apply] using hn
  omega

theorem pathTerminalPartner_involutive (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s)
    (hfree : ∀ x, a x ≠ x) (x : α) (hx : s x = x) :
    pathTerminalPartner a s (pathTerminalPartner a s x) = x := by
  unfold pathTerminalPartner
  rw [involutionPathPeriod_at_pow]
  rw [← Equiv.Perm.mul_apply, ← pow_add, ← two_mul]
  have he := terminal_involutionPathPeriod_even a s ha hs hfree x hx
  have hd := Nat.mod_add_div (involutionPathPeriod a s x) 2
  rw [Nat.even_iff.mp he, zero_add] at hd
  rw [hd, involutionPathPeriod_pow]

omit [Fintype α] in
theorem terminal_on_path_iff (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s)
    (hfree : ∀ x, a x ≠ x) (x : α) (hx : s x = x) {k : ℕ}
    (hk : k < involutionPathPeriod a s x) :
    s (((a * s) ^ k) x) = ((a * s) ^ k) x ↔
      k = 0 ∨ k = involutionPathPeriod a s x / 2 := by
  rw [terminal_reflection_fixed_iff a s ha hs x hx]
  have he := Nat.even_iff.mp (terminal_involutionPathPeriod_even a s ha hs hfree x hx)
  have hd := Nat.mod_add_div (involutionPathPeriod a s x) 2
  constructor
  · intro hf
    by_cases hz : k = 0
    · exact Or.inl hz
    · have hdvd : involutionPathPeriod a s x ∣ 2 * k := by
        apply Function.isPeriodicPt_iff_minimalPeriod_dvd.mp
        simpa only [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow] using hf
      have heq := Nat.eq_of_dvd_of_lt_two_mul (by omega : 2 * k ≠ 0) hdvd (by omega)
      right
      omega
  · rintro (rfl | rfl)
    · simp
    · have hmul : 2 * (involutionPathPeriod a s x / 2) = involutionPathPeriod a s x := by omega
      rw [hmul, involutionPathPeriod_pow]

abbrev TerminalHalfEdges (s : Equiv.Perm α) := {x : α // s x = x}

/-- The terminal pairing is constructed from the actual finite path orbit. -/
noncomputable def terminalPairingMap (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s)
    (hfree : ∀ x, a x ≠ x) : PairingMap (TerminalHalfEdges s) :=
  ⟨fun x => ⟨pathTerminalPartner a s x.val, pathTerminalPartner_fixed a s ha hs hfree x.val x.property⟩,
    (fun x => Subtype.ext (pathTerminalPartner_involutive a s ha hs hfree x.val x.property)),
    (fun x h => pathTerminalPartner_ne a s ha hs hfree x.val x.property (congrArg Subtype.val h))⟩

theorem terminalPairingMap_apply (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s)
    (hfree : ∀ x, a x ≠ x) (x : TerminalHalfEdges s) :
    ((terminalPairingMap a s ha hs hfree).val x).val = pathTerminalPartner a s x.val := rfl

end TournamentHamiltonian
