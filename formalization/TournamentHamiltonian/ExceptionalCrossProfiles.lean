import TournamentHamiltonian.ExceptionalDegrees
import TournamentHamiltonian.PairedCrossProducts

/-! Cross-neighbor proportions of actual exceptional vertices. -/
namespace TournamentHamiltonian
open scoped Classical

noncomputable def coreOutProportion {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (x : Fin n) : ℝ := (∑ j ∈ Fᶜ, adjacency T x j) / (Fᶜ.card : ℝ)

theorem adjacency_between_nonneg {n : ℕ} (T : Tournament n) (i j : Fin n) :
    0 ≤ adjacency T i j := by unfold adjacency; split_ifs <;> norm_num

theorem adjacency_between_le_one {n : ℕ} (T : Tournament n) (i j : Fin n) :
    adjacency T i j ≤ 1 := by unfold adjacency; split_ifs <;> norm_num

theorem adjacency_opposite_sum {n : ℕ} (T : Tournament n) (i j : Fin n) (hij : i ≠ j) :
    adjacency T i j + adjacency T j i = 1 := by
  have h := T.property.2 i j hij
  cases hj : T.val j i <;> simp_all [adjacency]

theorem coreOutProportion_bounds {n : ℕ} (T : Tournament n) (F : Finset (Fin n)) :
    ∀ x, 0 ≤ coreOutProportion T F x ∧ coreOutProportion T F x ≤ 1 := by
  intro x
  have hs : (∑ j ∈ Fᶜ, adjacency T x j) ≤ (Fᶜ.card : ℝ) := by
    simpa using Finset.sum_le_sum (s := Fᶜ) (fun j _ => adjacency_between_le_one T x j)
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun j _ => adjacency_between_nonneg T x j)) (by positivity)
  · exact div_le_one_of_le₀ hs (by positivity)

theorem rowDegree_split_core {n : ℕ} (T : Tournament n) (F : Finset (Fin n)) (x : Fin n) :
    (rowDegree T.val x : ℝ) = (∑ j ∈ F, adjacency T x j) +
      (∑ j ∈ Fᶜ, adjacency T x j) := by
  rw [rowDegree_eq_adjacency_sum]
  exact (Finset.sum_add_sum_compl F _).symm

theorem coreOutProportion_exceptional {n : ℕ} (T : Tournament n) (hn : 2 ≤ n)
    (x : Fin n) (hx : x ∈ exceptionalVertices T) (hN : 0 < (exceptionalVertices T)ᶜ.card) :
    coreOutProportion T (exceptionalVertices T) x ≤
        1 / 20 + ((exceptionalVertices T).card + 1 : ℝ) / (exceptionalVertices T)ᶜ.card ∨
      19 / 20 - ((exceptionalVertices T).card + 1 : ℝ) / (exceptionalVertices T)ᶜ.card ≤
        coreOutProportion T (exceptionalVertices T) x := by
  let F := exceptionalVertices T
  have hN0 : (0 : ℝ) < Fᶜ.card := by exact_mod_cast hN
  have hsum0 : 0 ≤ ∑ j ∈ F, adjacency T x j :=
    Finset.sum_nonneg (fun j _ => adjacency_between_nonneg T x j)
  have hsum1 : (∑ j ∈ F, adjacency T x j) ≤ (F.card : ℝ) := by
    simpa using Finset.sum_le_sum (s := F) (fun j _ => adjacency_between_le_one T x j)
  have hsplit := rowDegree_split_core T F x
  have hc : (F.card : ℝ) + (Fᶜ.card : ℝ) = n := by
    exact_mod_cast (by simpa only [Fintype.card_fin] using Finset.card_add_card_compl F : F.card + Fᶜ.card = n)
  rcases (mem_exceptionalVertices_iff_degree T hn x).mp hx with h | h
  · left
    have hn0 : 0 < (n : ℝ) - 1 := by
      have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ hn0] at h
    dsimp [coreOutProportion]
    apply (div_le_iff₀ hN0).mpr
    field_simp
    dsimp [F] at hsplit hsum0 hsum1 hc hN0
    nlinarith
  · right
    have hn0 : 0 < (n : ℝ) - 1 := by
      have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [lt_div_iff₀ hn0] at h
    dsimp [coreOutProportion]
    apply (le_div_iff₀ hN0).mpr
    field_simp
    dsimp [F] at hsplit hsum0 hsum1 hc hN0
    nlinarith

theorem core_incoming_sum {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (x : Fin n) (hx : x ∈ F) :
    (∑ j ∈ Fᶜ, adjacency T j x) = (Fᶜ.card : ℝ) - ∑ j ∈ Fᶜ, adjacency T x j := by
  have h : ∀ j ∈ Fᶜ, adjacency T j x = 1 - adjacency T x j := by
    intro j hj
    have hne : x ≠ j := by rintro rfl; exact Finset.mem_compl.mp hj hx
    linarith [adjacency_opposite_sum T x j hne]
  simp_rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  simp

/-- Both weighted cross-neighbor factors inherit the actual exceptional-degree suppression. -/
theorem exceptional_weighted_cross_pair {n : ℕ} (T : Tournament n) (hn : 2 ≤ n)
    (x : Fin n) (hx : x ∈ exceptionalVertices T) (hN : 0 < (exceptionalVertices T)ᶜ.card)
    (l r : Fin n → ℝ) (beta : ℝ) (hb : 0 ≤ beta)
    (hl : ∀ j, 0 ≤ l j) (hr : ∀ j, 0 ≤ r j)
    (hdl : (∑ j ∈ (exceptionalVertices T)ᶜ, |l j - 1|) ≤ (exceptionalVertices T)ᶜ.card * beta)
    (hdr : (∑ j ∈ (exceptionalVertices T)ᶜ, |r j - 1|) ≤ (exceptionalVertices T)ᶜ.card * beta) :
    let N : ℝ := (exceptionalVertices T)ᶜ.card
    let u := 2 / N * ∑ j ∈ (exceptionalVertices T)ᶜ, adjacency T x j * r j
    let v := 2 / N * ∑ j ∈ (exceptionalVertices T)ᶜ, l j * adjacency T j x
    0 ≤ u ∧ 0 ≤ v ∧ u ≤ 2 + 2 * beta ∧ v ≤ 2 + 2 * beta ∧
      u * v ≤ 19 / 100 + 4 * (((exceptionalVertices T).card + 1 : ℝ) / N) +
        4 * beta + 4 * beta ^ 2 := by
  let F := exceptionalVertices T
  let N : ℝ := Fᶜ.card
  let q := coreOutProportion T F x
  have hN0 : 0 < N := by dsimp [N, F]; exact_mod_cast hN
  have hq := coreOutProportion_bounds T F x
  have hpair := cross_pair_bounds q ((F.card + 1 : ℝ) / N) beta hq.1 hq.2
    (by positivity) hb (coreOutProportion_exceptional T hn x hx hN)
  have hrow := weighted_neighbor_sum_le Fᶜ (adjacency T x) r beta
    (fun j _ => adjacency_between_nonneg T x j) (fun j _ => adjacency_between_le_one T x j) hdr
  have hcol := weighted_neighbor_sum_le Fᶜ (fun j => adjacency T j x) l beta
    (fun j _ => adjacency_between_nonneg T j x) (fun j _ => adjacency_between_le_one T j x) hdl
  have hrow' := mul_le_mul_of_nonneg_left hrow (by positivity : 0 ≤ 2 / N)
  have hcol' := mul_le_mul_of_nonneg_left hcol (by positivity : 0 ≤ 2 / N)
  have heq : (∑ j ∈ Fᶜ, adjacency T x j) = N * q := by
    dsimp [q, coreOutProportion, N]
    field_simp [show (Fᶜ.card : ℝ) ≠ 0 from hN0.ne']
  rw [heq] at hrow'
  rw [core_incoming_sum T F x hx, heq] at hcol'
  have hru : 2 / N * (N * q + N * beta) = 2 * (q + beta) := by field_simp
  have hcv : 2 / N * (N - N * q + N * beta) = 2 * (1 - q + beta) := by field_simp
  rw [hru] at hrow'
  rw [hcv] at hcol'
  simp only [mul_comm (adjacency T _ x) (l _)] at hcol'
  have hu0 : 0 ≤ 2 / N * ∑ j ∈ Fᶜ, adjacency T x j * r j := by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => mul_nonneg (adjacency_between_nonneg T x j) (hr j)))
  have hv0 : 0 ≤ 2 / N * ∑ j ∈ Fᶜ, l j * adjacency T j x := by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => mul_nonneg (hl j) (adjacency_between_nonneg T j x)))
  exact ⟨hu0, hv0, hrow'.trans hpair.2.2.1, hcol'.trans hpair.2.2.2.1,
    (mul_le_mul hrow' hcol' hv0 hpair.1).trans hpair.2.2.2.2⟩

end TournamentHamiltonian
