import TournamentHamiltonian.CoreCompressionCoverage

/-! The actual original edges are the disjoint positive-length compressed path positions. -/

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {α : Type*} [Fintype α]

omit [Fintype α] in
theorem terminal_edge_reflection_succ (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s) (x : α) (hx : s x = x) (k : ℕ) :
    a (((a * s) ^ (k + 1)) x) = (((a * s) ^ k)⁻¹) x := by
  rw [pow_succ', Equiv.Perm.mul_apply]
  change a (a (s (((a * s) ^ k) x))) = _
  rw [ha]
  exact terminal_reflection_pow a s ha hs x hx k

theorem terminal_path_length_pos (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s)
    (hfree : ∀ x, a x ≠ x) (x : α) (hx : s x = x) :
    0 < involutionPathPeriod a s x / 2 := by
  have hp := involutionPathPeriod_pos a s x
  have he := Nat.even_iff.mp (terminal_involutionPathPeriod_even a s ha hs hfree x hx)
  have hd := Nat.mod_add_div (involutionPathPeriod a s x) 2
  omega

theorem terminal_path_arrival_injective (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s)
    (hfree : ∀ x, a x ≠ x) (x : α) (hx : s x = x) :
    Function.Injective (fun i : Fin (involutionPathPeriod a s x / 2) => ((a * s) ^ (i.val + 1)) x) := by
  intro i j hij
  have hp := involutionPathPeriod_pos a s x
  have he := Nat.even_iff.mp (terminal_involutionPathPeriod_even a s ha hs hfree x hx)
  have hd := Nat.mod_add_div (involutionPathPeriod a s x) 2
  have hi : i.val + 1 < involutionPathPeriod a s x := by have h := i.isLt; omega
  have hj : j.val + 1 < involutionPathPeriod a s x := by have h := j.isLt; omega
  have heq : i.val + 1 = j.val + 1 :=
    (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp
      (by simpa only [← Equiv.Perm.coe_pow] using hij)
  exact Fin.ext (by omega)

theorem terminal_path_arrival_no_flip (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s)
    (hfree : ∀ x, a x ≠ x) (x : α) (hx : s x = x)
    (i j : Fin (involutionPathPeriod a s x / 2)) :
    a (((a * s) ^ (i.val + 1)) x) ≠ ((a * s) ^ (j.val + 1)) x := by
  have hp := involutionPathPeriod_pos a s x
  have he := Nat.even_iff.mp (terminal_involutionPathPeriod_even a s ha hs hfree x hx)
  have hd := Nat.mod_add_div (involutionPathPeriod a s x) 2
  have hk : i.val + (j.val + 1) < involutionPathPeriod a s x := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  intro hflip
  rw [terminal_edge_reflection_succ a s ha hs x hx i.val] at hflip
  have hh := congrArg ((a * s) ^ i.val) hflip
  have hreturn : ((a * s) ^ (i.val + (j.val + 1))) x = x := by
    simpa only [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply, ← pow_add] using hh.symm
  have hz : i.val + (j.val + 1) = 0 :=
    (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hk hp).mp
      (by simpa only [← Equiv.Perm.coe_pow, pow_zero, Equiv.Perm.one_apply] using hreturn)
  omega

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

abbrev ActualCompressedPaths (P Q : Setoid κ) := Quotient (actualCompressedPairPartition P Q)

noncomputable def compressedPathTerminal (P Q : Setoid κ) (c : ActualCompressedPaths P Q) :
    TerminalHalfEdges (partitionHalfEdgeSplice P Q) := Quotient.out c

noncomputable def compressedPathLength (P Q : Setoid κ) (c : ActualCompressedPaths P Q) : ℕ :=
  involutionPathPeriod partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q) (compressedPathTerminal P Q c).val / 2

noncomputable def compressedPathArrival (P Q : Setoid κ) (c : ActualCompressedPaths P Q)
    (i : Fin (compressedPathLength P Q c)) : PartitionHalfEdges (κ := κ) :=
  let p : Equiv.Perm (PartitionHalfEdges (κ := κ)) := partitionHalfEdgeFlip * partitionHalfEdgeSplice P Q
  (p ^ (i.val + 1)) (compressedPathTerminal P Q c).val

noncomputable def compressedPathOriginalEdge (P Q : Setoid κ) :
    (Σ c : ActualCompressedPaths P Q, Fin (compressedPathLength P Q c)) → κ :=
  fun x => Sum.elim id id (compressedPathArrival P Q x.1 x.2)

theorem compressedPathLength_pos (P Q : Setoid κ) (c : ActualCompressedPaths P Q) :
    0 < compressedPathLength P Q c :=
  terminal_path_length_pos partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q)
    partitionHalfEdgeFlip_involutive (partitionHalfEdgeSplice_involutive P Q) partitionHalfEdgeFlip_ne
    (compressedPathTerminal P Q c).val (compressedPathTerminal P Q c).property

omit [Fintype α] [Fintype κ] [DecidableEq κ] in
theorem partitionHalfEdge_original_eq_iff (x y : PartitionHalfEdges (κ := κ)) :
    Sum.elim id id x = Sum.elim id id y ↔ x = y ∨ partitionHalfEdgeFlip x = y := by
  cases x <;> cases y <;> simp [partitionHalfEdgeFlip, eq_comm]

theorem compressedPathOriginalEdge_injective (P Q : Setoid κ) :
    Function.Injective (compressedPathOriginalEdge P Q) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ hEdge
  let p : Equiv.Perm (PartitionHalfEdges (κ := κ)) := partitionHalfEdgeFlip * partitionHalfEdgeSplice P Q
  have hc : p.SameCycle (compressedPathTerminal P Q c).val (compressedPathArrival P Q c i) :=
    (Equiv.Perm.SameCycle.refl _ _).pow_right
  have hd : p.SameCycle (compressedPathTerminal P Q d).val (compressedPathArrival P Q d j) :=
    (Equiv.Perm.SameCycle.refl _ _).pow_right
  have hArrival := partitionHalfEdge_original_eq_iff _ _ |>.mp hEdge
  have hcd : p.SameCycle (compressedPathTerminal P Q c).val (compressedPathTerminal P Q d).val := by
    rcases hArrival with hArrival | hArrival
    · exact (hArrival ▸ hc).trans hd.symm
    · have hf := terminal_sameCycle_flip partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q)
        partitionHalfEdgeFlip_involutive (partitionHalfEdgeSplice_involutive P Q)
        (compressedPathTerminal P Q c).property hc
      exact (hArrival ▸ hf).trans hd.symm
  have hclasses : c = d := by
    have hq := Quotient.sound ((actualCompressedPairPartition_sameCycle P Q _ _).mpr hcd)
    change Quotient.mk _ (Quotient.out c) = Quotient.mk _ (Quotient.out d) at hq
    simpa only [Quotient.out_eq] using hq
  subst d
  have hij : i = j := by
    rcases (partitionHalfEdge_original_eq_iff _ _).mp hEdge with hh | hh
    · exact terminal_path_arrival_injective partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q)
        partitionHalfEdgeFlip_involutive (partitionHalfEdgeSplice_involutive P Q) partitionHalfEdgeFlip_ne
        (compressedPathTerminal P Q c).val (compressedPathTerminal P Q c).property hh
    · exact (terminal_path_arrival_no_flip partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q)
        partitionHalfEdgeFlip_involutive (partitionHalfEdgeSplice_involutive P Q) partitionHalfEdgeFlip_ne
        (compressedPathTerminal P Q c).val (compressedPathTerminal P Q c).property i j hh).elim
  exact Sigma.ext rfl (heq_of_eq hij)

variable [DecidableEq α]

omit [Fintype κ] [DecidableEq κ] [DecidableEq α] in
theorem cyclePow_bijective (p : Equiv.Perm α) (x : α) :
    Function.Bijective (fun i : Fin (Function.minimalPeriod p x) =>
      (⟨(p ^ i.val) x, (Equiv.Perm.SameCycle.refl p x).pow_right⟩ : {y : α // p.SameCycle x y})) := by
  constructor
  · intro i j hij
    apply Fin.ext
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp
      (by simpa only [← Equiv.Perm.coe_pow] using congrArg Subtype.val hij)
  · intro y
    obtain ⟨k, hk⟩ := y.property.exists_nat_pow_eq
    have hp := Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts x)
    refine ⟨⟨k % Function.minimalPeriod p x, Nat.mod_lt _ hp⟩, ?_⟩
    apply Subtype.ext
    simpa only [Equiv.Perm.coe_pow, Function.iterate_mod_minimalPeriod_eq] using hk

omit [Fintype κ] [DecidableEq κ] in
theorem cycleMember_card (p : Equiv.Perm α) (x : α) :
    Fintype.card {y : α // p.SameCycle x y} = Function.minimalPeriod p x := by
  rw [← Fintype.card_congr (Equiv.ofBijective _ (cyclePow_bijective p x)), Fintype.card_fin]

abbrev CompressedPathOrbit (P Q : Setoid κ) (c : ActualCompressedPaths P Q) :=
  {x : PartitionHalfEdges (κ := κ) //
    (partitionHalfEdgeFlip * partitionHalfEdgeSplice P Q).SameCycle (compressedPathTerminal P Q c).val x}

def compressedPathOrbitHalfEdge (P Q : Setoid κ) :
    (Σ c : ActualCompressedPaths P Q, CompressedPathOrbit P Q c) → PartitionHalfEdges (κ := κ) :=
  fun x => x.2.val

theorem compressedPathOrbitHalfEdge_bijective (P Q : Setoid κ)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    Function.Bijective (compressedPathOrbitHalfEdge P Q) := by
  constructor
  · rintro ⟨c, x⟩ ⟨d, y⟩ hxy
    change x.val = y.val at hxy
    have hcd : c = d := by
      have hpath := x.property.trans (hxy ▸ y.property.symm)
      have hq := Quotient.sound ((actualCompressedPairPartition_sameCycle P Q _ _).mpr hpath)
      change Quotient.mk _ (Quotient.out c) = Quotient.mk _ (Quotient.out d) at hq
      simpa only [Quotient.out_eq] using hq
    subst d
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hxy))
  · intro x
    obtain ⟨z, hz⟩ := pureFreeCore_halfEdge_path_coverage P Q hc x
    let c : ActualCompressedPaths P Q := Quotient.mk _ z
    have hterminal : actualCompressedPairPartition P Q (compressedPathTerminal P Q c) z := by
      apply Quotient.exact
      exact Quotient.out_eq c
    have hpath := (actualCompressedPairPartition_sameCycle P Q _ _).mp hterminal |>.trans hz
    exact ⟨⟨c, ⟨x, hpath⟩⟩, rfl⟩

theorem compressedPathPosition_card (P Q : Setoid κ)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    Fintype.card (Σ c : ActualCompressedPaths P Q, Fin (compressedPathLength P Q c)) = Fintype.card κ := by
  have hcard := Fintype.card_congr
    (Equiv.ofBijective (compressedPathOrbitHalfEdge P Q) (compressedPathOrbitHalfEdge_bijective P Q hc))
  rw [Fintype.card_sigma, Fintype.card_sum] at hcard
  have hsum : (∑ c : ActualCompressedPaths P Q,
      Fintype.card (CompressedPathOrbit P Q c)) = 2 *
      (∑ c : ActualCompressedPaths P Q, compressedPathLength P Q c) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    unfold CompressedPathOrbit
    rw [cycleMember_card]
    have he := Nat.even_iff.mp (terminal_involutionPathPeriod_even partitionHalfEdgeFlip
      (partitionHalfEdgeSplice P Q) partitionHalfEdgeFlip_involutive
      (partitionHalfEdgeSplice_involutive P Q) partitionHalfEdgeFlip_ne
      (compressedPathTerminal P Q c).val (compressedPathTerminal P Q c).property)
    have hd := Nat.mod_add_div (involutionPathPeriod partitionHalfEdgeFlip
      (partitionHalfEdgeSplice P Q) (compressedPathTerminal P Q c).val) 2
    change involutionPathPeriod _ _ _ = 2 * compressedPathLength P Q c
    unfold compressedPathLength
    omega
  rw [hsum] at hcard
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  omega

theorem compressedPathOriginalEdge_bijective (P Q : Setoid κ)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    Function.Bijective (compressedPathOriginalEdge P Q) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨compressedPathOriginalEdge_injective P Q, compressedPathPosition_card P Q hc⟩

/-- Genuine edge-labelled core compression, including empty and disconnected graphs. -/
noncomputable def compressedPathEdgeEquiv (P Q : Setoid κ)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    (Σ c : ActualCompressedPaths P Q, Fin (compressedPathLength P Q c)) ≃ κ :=
  Equiv.ofBijective (compressedPathOriginalEdge P Q) (compressedPathOriginalEdge_bijective P Q hc)

end TournamentHamiltonian
