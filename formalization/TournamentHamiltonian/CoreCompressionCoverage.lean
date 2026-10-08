import TournamentHamiltonian.PartitionHalfEdges

/-! Every edge of an actual pure-free core belongs to a path with high-degree terminals. -/

namespace TournamentHamiltonian

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {α κ : Type*} [Fintype κ] [DecidableEq κ]

def involutionWalkSetoid (a s : Equiv.Perm α) : Setoid α :=
  Relation.EqvGen.setoid (fun x y => y = a x ∨ y = s x)

omit [Fintype κ] [DecidableEq κ] in
theorem involutionWalk_flip (a s : Equiv.Perm α) (x : α) :
    involutionWalkSetoid a s x (a x) := Relation.EqvGen.rel _ _ (Or.inl rfl)

omit [Fintype κ] [DecidableEq κ] in
theorem involutionWalk_splice (a s : Equiv.Perm α) (x : α) :
    involutionWalkSetoid a s x (s x) := Relation.EqvGen.rel _ _ (Or.inr rfl)

theorem degreeTwoSplice_class_partner (P : Setoid κ) (x y : κ)
    (hxy : P x y) (hn : degreeTwoSplice P x ≠ x) :
    y = x ∨ y = degreeTwoSplice P x := by
  have hd : (partitionClass P x).card = 2 := by
    by_contra hd
    exact hn ((degreeTwoSplice_fixed_iff P x).mpr hd)
  have hp := (degreeTwoPartner_spec P x hd).2.2 y hxy
  simpa only [degreeTwoSplice, dite_eq_left hd] using hp

noncomputable abbrev partitionHalfEdgeWalk (P Q : Setoid κ) :=
  involutionWalkSetoid partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q)

theorem pureFreeCore_edge_has_terminal (P Q : Setoid κ)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) (e : κ) :
    ∃ x : PartitionHalfEdges (κ := κ), partitionHalfEdgeWalk P Q (.inl e) x ∧
      partitionHalfEdgeSplice P Q x = x := by
  by_contra hn
  have hnone : ∀ x, partitionHalfEdgeWalk P Q (.inl e) x → partitionHalfEdgeSplice P Q x ≠ x := by
    intro x hx hs
    exact hn ⟨x, hx, hs⟩
  let W := partitionHalfEdgeWalk P Q
  let p : κ → Prop := fun f => W (.inl e) (.inl f)
  have hflip : ∀ f, W (.inl e) (.inl f) ↔ W (.inl e) (.inr f) := by
    intro f
    have hf := involutionWalk_flip partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q) (.inl f)
    exact ⟨fun h => W.trans h hf, fun h => W.trans h (W.symm hf)⟩
  have hleft : ∀ u v, P u v → p u → p v := by
    intro u v huv hu
    have hn := hnone (.inl u) hu
    have hz := degreeTwoSplice_class_partner (sumPartition P Q) (.inl u) (.inl v) huv hn
    rcases hz with hz | hz
    · have hvu : v = u := Sum.inl.inj hz
      simpa [p, hvu] using hu
    · change W (.inl e) (.inl v)
      rw [hz]
      exact W.trans hu (involutionWalk_splice _ _ _)
  have hright : ∀ u v, Q u v → p u → p v := by
    intro u v huv hu
    have hu' := (hflip u).mp hu
    have hn := hnone (.inr u) hu'
    have hz := degreeTwoSplice_class_partner (sumPartition P Q) (.inr u) (.inr v) huv hn
    apply (hflip v).mpr
    rcases hz with hz | hz
    · have hvu : v = u := Sum.inr.inj hz
      simpa [hvu] using hu'
    · rw [hz]
      exact W.trans hu' (involutionWalk_splice _ _ _)
  have hP : P ≤ Setoid.ker p := by
    intro u v huv
    exact propext ⟨hleft u v huv, hleft v u (P.symm huv)⟩
  have hQ : Q ≤ Setoid.ker p := by
    intro u v huv
    exact propext ⟨hright u v huv, hright v u (Q.symm huv)⟩
  have hjoin : P ⊔ Q ≤ Setoid.ker p := sup_le hP hQ
  apply hc e
  intro f hfe
  have hpf : p f := by
    have hpEq : p f = p e := hjoin hfe
    rw [hpEq]
  have hl : (partitionClass (sumPartition P Q) (.inl f)).card = 2 := by
    by_contra hn
    exact hnone (.inl f) hpf ((degreeTwoSplice_fixed_iff _ _).mpr hn)
  have hr : (partitionClass (sumPartition P Q) (.inr f)).card = 2 := by
    by_contra hn
    exact hnone (.inr f) ((hflip f).mp hpf) ((degreeTwoSplice_fixed_iff _ _).mpr hn)
  rw [partitionHalfEdge_class_card] at hl hr
  exact ⟨hl, hr⟩

omit [Fintype κ] [DecidableEq κ] in
theorem terminal_reflection_zpow (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s) (x : α) (hx : s x = x)
    (k : ℤ) : s (((a * s) ^ k) x) = (((a * s) ^ k)⁻¹) x := by
  have h : s * (a * s) ^ k * s⁻¹ = ((a * s) ^ k)⁻¹ := by
    rw [← conj_zpow, terminal_reflection_conj a s ha hs, inv_zpow]
  have hi : s⁻¹ x = x := (Equiv.symm_apply_eq s).mpr hx.symm
  have he := congrArg (fun p : Equiv.Perm α => p x) h
  simpa only [Equiv.Perm.mul_apply, hi] using he

omit [Fintype κ] [DecidableEq κ] in
theorem terminal_sameCycle_splice (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s) {x y : α}
    (hx : s x = x) (hxy : (a * s).SameCycle x y) : (a * s).SameCycle x (s y) := by
  rcases hxy with ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  rw [zpow_neg]
  rw [← terminal_reflection_zpow a s ha hs x hx k, hk]

omit [Fintype κ] [DecidableEq κ] in
theorem terminal_sameCycle_flip (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s) {x y : α}
    (hx : s x = x) (hxy : (a * s).SameCycle x y) : (a * s).SameCycle x (a y) := by
  rcases hxy with ⟨k, hk⟩
  refine ⟨1 - k, ?_⟩
  rw [sub_eq_add_neg, zpow_add, zpow_one, zpow_neg, Equiv.Perm.mul_apply]
  rw [← terminal_reflection_zpow a s ha hs x hx k]
  change a (s (s (((a * s) ^ k) x))) = a y
  rw [hs, hk]

omit [Fintype κ] [DecidableEq κ] in
/-- A finite or infinite walk component containing a terminal is a single path orbit. -/
theorem terminal_walk_sameCycle (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s) {x y : α}
    (hx : s x = x) (hxy : involutionWalkSetoid a s x y) : (a * s).SameCycle x y := by
  let p : α → Prop := fun y => (a * s).SameCycle x y
  have hstepA : ∀ y, p y → p (a y) := fun y h => terminal_sameCycle_flip a s ha hs hx h
  have hstepS : ∀ y, p y → p (s y) := fun y h => terminal_sameCycle_splice a s ha hs hx h
  have hker : involutionWalkSetoid a s ≤ Setoid.ker p := by
    apply Setoid.eqvGen_le
    intro u v hv
    rcases hv with rfl | rfl
    · exact propext ⟨hstepA u, fun h => by simpa only [ha u] using hstepA (a u) h⟩
    · exact propext ⟨hstepS u, fun h => by simpa only [hs u] using hstepS (s u) h⟩
  have he : p x = p y := hker hxy
  change p y
  rw [← he]

theorem pureFreeCore_halfEdge_path_coverage (P Q : Setoid κ)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) (x : PartitionHalfEdges (κ := κ)) :
    ∃ z : TerminalHalfEdges (partitionHalfEdgeSplice P Q),
      (partitionHalfEdgeFlip * partitionHalfEdgeSplice P Q).SameCycle z.val x := by
  let e : κ := Sum.elim id id x
  obtain ⟨z, hz, hs⟩ := pureFreeCore_edge_has_terminal P Q hc e
  refine ⟨⟨z, hs⟩, terminal_walk_sameCycle _ _ partitionHalfEdgeFlip_involutive
    (partitionHalfEdgeSplice_involutive P Q) hs ?_⟩
  apply (partitionHalfEdgeWalk P Q).trans ((partitionHalfEdgeWalk P Q).symm hz)
  cases x with
  | inl x => exact (partitionHalfEdgeWalk P Q).refl _
  | inr x => exact involutionWalk_flip partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q) (Sum.inl x)

variable [Fintype α]

theorem terminal_sameCycle_iff_partner (a s : Equiv.Perm α)
    (ha : Function.Involutive a) (hs : Function.Involutive s)
    (hfree : ∀ x, a x ≠ x) (x y : TerminalHalfEdges s) :
    (a * s).SameCycle x.val y.val ↔ y.val = x.val ∨ y.val = pathTerminalPartner a s x.val := by
  constructor
  · intro hxy
    obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
    let i := k % involutionPathPeriod a s x.val
    have hi : i < involutionPathPeriod a s x.val := Nat.mod_lt _ (involutionPathPeriod_pos a s x.val)
    have hki : ((a * s) ^ i) x.val = y.val := by
      change ((a * s) ^ (k % involutionPathPeriod a s x.val)) x.val = y.val
      simpa only [Equiv.Perm.coe_pow, involutionPathPeriod, Function.iterate_mod_minimalPeriod_eq] using hk
    have hfix : s (((a * s) ^ i) x.val) = ((a * s) ^ i) x.val := by rw [hki]; exact y.property
    have hends := (terminal_on_path_iff a s ha hs hfree x.val x.property hi).mp hfix
    rcases hends with hzero | hhalf
    · left
      simpa only [hzero, pow_zero, Equiv.Perm.one_apply] using hki.symm
    · right
      simpa only [hhalf, pathTerminalPartner] using hki.symm
  · rintro (hxy | hxy)
    · rw [hxy]
    · rw [hxy]
      exact (Equiv.Perm.SameCycle.refl _ _).pow_right

theorem actualCompressedPairPartition_sameCycle (P Q : Setoid κ)
    (x y : TerminalHalfEdges (partitionHalfEdgeSplice P Q)) :
    actualCompressedPairPartition P Q x y ↔
      (partitionHalfEdgeFlip * partitionHalfEdgeSplice P Q).SameCycle x.val y.val := by
  rw [terminal_sameCycle_iff_partner partitionHalfEdgeFlip (partitionHalfEdgeSplice P Q)
    partitionHalfEdgeFlip_involutive (partitionHalfEdgeSplice_involutive P Q) partitionHalfEdgeFlip_ne]
  change (x = y ∨ (partitionCoreTerminalPairing P Q).val x = y) ↔ _
  constructor
  · rintro (hxy | hxy)
    · exact Or.inl (congrArg Subtype.val hxy).symm
    · exact Or.inr (congrArg Subtype.val hxy).symm
  · rintro (hxy | hxy)
    · exact Or.inl (Subtype.ext hxy.symm)
    · exact Or.inr (Subtype.ext hxy.symm)

noncomputable def compressedPairCycleMap (P Q : Setoid κ) :
    Quotient (actualCompressedPairPartition P Q) →
      Quotient (Equiv.Perm.SameCycle.setoid (partitionHalfEdgeFlip * partitionHalfEdgeSplice P Q)) :=
  Quotient.map Subtype.val (fun x y h => (actualCompressedPairPartition_sameCycle P Q x y).mp h)

theorem compressedPairCycleMap_bijective (P Q : Setoid κ)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    Function.Bijective (compressedPairCycleMap P Q) := by
  constructor
  · intro u v
    refine Quotient.inductionOn₂ u v ?_
    intro x y hxy
    apply Quotient.sound
    apply (actualCompressedPairPartition_sameCycle P Q x y).mpr
    exact Quotient.exact hxy
  · intro u
    refine Quotient.inductionOn u ?_
    intro x
    obtain ⟨z, hz⟩ := pureFreeCore_halfEdge_path_coverage P Q hc x
    exact ⟨Quotient.mk _ z, Quotient.sound hz⟩

/-- The constructed compressed pair partition and all actual path orbits are in bijection. -/
noncomputable def compressedPairCycleEquiv (P Q : Setoid κ)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    Quotient (actualCompressedPairPartition P Q) ≃
      Quotient (Equiv.Perm.SameCycle.setoid (partitionHalfEdgeFlip * partitionHalfEdgeSplice P Q)) :=
  Equiv.ofBijective (compressedPairCycleMap P Q) (compressedPairCycleMap_bijective P Q hc)

theorem pureFreeCore_path_orbit_card (P Q : Setoid κ)
    (hP : ¬ HasSingletonClass P) (hQ : ¬ HasSingletonClass Q)
    (hc : ∀ e, ¬ IsPureDegreeTwoComponent P Q e) :
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid (partitionHalfEdgeFlip * partitionHalfEdgeSplice P Q))) =
      (highDegreeVertices P Q).card + partitionGraphExcess P Q := by
  rw [← Fintype.card_congr (compressedPairCycleEquiv P Q hc)]
  exact actualCompressedPairPartition_card P Q hP hQ

end TournamentHamiltonian
