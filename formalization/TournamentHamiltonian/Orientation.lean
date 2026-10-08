import TournamentHamiltonian.Definitions
import Mathlib.Logic.Equiv.Prod

/-! Independent Boolean edge coordinates for the random-tournament
averaging argument in §1 and §5.3. -/

namespace TournamentHamiltonian

abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def edgeOfPair {n : ℕ} (u v : Fin n) (hne : u ≠ v) : Edge n :=
  if h : u < v then ⟨(u, v), h⟩
  else ⟨(v, u), lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)⟩

lemma edgeOfPair_eq_cases {n : ℕ} {u v x y : Fin n}
    (huv : u ≠ v) (hxy : x ≠ y)
    (h : edgeOfPair u v huv = edgeOfPair x y hxy) :
    (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  have hv := congrArg Subtype.val h
  unfold edgeOfPair at hv
  split_ifs at hv <;> simp only [Prod.mk.injEq] at hv
  · exact Or.inl hv
  · exact Or.inr hv
  · exact Or.inr ⟨hv.2, hv.1⟩
  · exact Or.inl ⟨hv.2, hv.1⟩

lemma consecutive_ne {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    σ i.castSucc ≠ σ i.succ := by
  intro h
  have hval := congrArg Fin.val (σ.injective h)
  simp only [Fin.val_castSucc, Fin.val_succ] at hval
  omega

def pathEdge {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) : Edge (n + 1) :=
  edgeOfPair (σ i.castSucc) (σ i.succ) (consecutive_ne σ i)

/-- A Hamiltonian permutation requests distinct independent orientation
coordinates, one for each consecutive pair. -/
theorem pathEdge_injective {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    Function.Injective (pathEdge σ) := by
  intro i j h
  obtain h | h := edgeOfPair_eq_cases (consecutive_ne σ i) (consecutive_ne σ j) h
  · exact Fin.ext (congrArg (fun k : Fin (n + 1) => k.val) (σ.injective h.1))
  · have h₁ := congrArg Fin.val (σ.injective h.1)
    have h₂ := congrArg Fin.val (σ.injective h.2)
    simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
    omega

def orientationAdjacency {n : ℕ} (ω : Edge n → Bool) (i j : Fin n) : Bool :=
  if h : i < j then ω ⟨(i, j), h⟩
  else if h : j < i then !ω ⟨(j, i), h⟩ else false

theorem orientationAdjacency_isTournament {n : ℕ} (ω : Edge n → Bool) :
    IsTournament (orientationAdjacency ω) := by
  constructor
  · intro i
    simp [orientationAdjacency]
  · intro i j hne
    rcases lt_or_gt_of_ne hne with h | h
    · simp [orientationAdjacency, h, not_lt_of_gt h]
    · simp [orientationAdjacency, h, not_lt_of_gt h]

def tournamentOfOrientation {n : ℕ} (ω : Edge n → Bool) : Tournament n :=
  ⟨orientationAdjacency ω, orientationAdjacency_isTournament ω⟩

theorem isHamiltonian_iff_consecutive {n : ℕ} (T : Tournament (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    IsHamiltonian T σ ↔ ∀ i : Fin n, T.val (σ i.castSucc) (σ i.succ) = true := by
  constructor
  · intro h i
    exact h i.castSucc i.succ rfl
  · intro h i j hij
    have hi : i.val < n := by omega
    let k : Fin n := ⟨i.val, hi⟩
    have hk : k.castSucc = i := Fin.ext rfl
    have hkj : k.succ = j := Fin.ext (by simpa [k] using hij.symm)
    simpa [hk, hkj] using h k

def pathEdges {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) : Finset (Edge (n + 1)) :=
  Finset.univ.image (pathEdge σ)

def pathRequirement {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (e : Edge (n + 1)) : Bool :=
  decide (σ.symm e.val.1 < σ.symm e.val.2)

theorem pathEdges_card {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    (pathEdges σ).card = n := by
  unfold pathEdges
  rw [Finset.card_image_of_injective _ (pathEdge_injective σ)]
  simp

lemma path_step_iff {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (ω : Edge (n + 1) → Bool) (i : Fin n) :
    (tournamentOfOrientation ω).val (σ i.castSucc) (σ i.succ) = true ↔
      ω (pathEdge σ i) = pathRequirement σ (pathEdge σ i) := by
  have hi : i.castSucc < i.succ := by simp [Fin.lt_def]
  by_cases h : σ i.castSucc < σ i.succ
  · simp [tournamentOfOrientation, orientationAdjacency, pathEdge, edgeOfPair,
      pathRequirement, h, hi]
  · have hr : σ i.succ < σ i.castSucc :=
      lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (consecutive_ne σ i))
    simp [tournamentOfOrientation, orientationAdjacency, pathEdge, edgeOfPair,
      pathRequirement, h, hr, not_lt_of_gt hi]

theorem isHamiltonian_iff_fixed_edges {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (ω : Edge (n + 1) → Bool) :
    IsHamiltonian (tournamentOfOrientation ω) σ ↔
      ∀ e ∈ pathEdges σ, ω e = pathRequirement σ e := by
  rw [isHamiltonian_iff_consecutive]
  constructor
  · intro h e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact (path_step_iff σ ω i).mp (h i)
  · intro h i
    apply (path_step_iff σ ω i).mpr
    exact h _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

end TournamentHamiltonian
