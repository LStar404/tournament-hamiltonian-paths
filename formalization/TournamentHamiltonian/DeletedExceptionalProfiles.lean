import TournamentHamiltonian.ExceptionalCrossProfiles

/-! Exceptional cross profiles after arbitrary further core deletions. -/
namespace TournamentHamiltonian
open scoped Classical

theorem coreOutProportion_of_exceptional_degree {n : ℕ} (T : Tournament n) (hn : 2 ≤ n) (D : Finset (Fin n))
    (x : Fin n) (hx : x ∈ exceptionalVertices T) (hN : 0 < (D)ᶜ.card) :
    coreOutProportion T (D) x ≤
        1 / 20 + ((D).card + 1 : ℝ) / (D)ᶜ.card ∨
      19 / 20 - ((D).card + 1 : ℝ) / (D)ᶜ.card ≤
        coreOutProportion T (D) x := by
  let F := D
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

theorem deleted_exceptional_weighted_cross_pair {n : ℕ} (T : Tournament n) (hn : 2 ≤ n) (D : Finset (Fin n))
    (x : Fin n) (hx : x ∈ exceptionalVertices T) (hxD : x ∈ D) (hN : 0 < (D)ᶜ.card)
    (l r : Fin n → ℝ) (beta : ℝ) (hb : 0 ≤ beta)
    (hl : ∀ j, 0 ≤ l j) (hr : ∀ j, 0 ≤ r j)
    (hdl : (∑ j ∈ (D)ᶜ, |l j - 1|) ≤ (D)ᶜ.card * beta)
    (hdr : (∑ j ∈ (D)ᶜ, |r j - 1|) ≤ (D)ᶜ.card * beta) :
    let N : ℝ := (D)ᶜ.card
    let u := 2 / N * ∑ j ∈ (D)ᶜ, adjacency T x j * r j
    let v := 2 / N * ∑ j ∈ (D)ᶜ, l j * adjacency T j x
    0 ≤ u ∧ 0 ≤ v ∧ u ≤ 2 + 2 * beta ∧ v ≤ 2 + 2 * beta ∧
      u * v ≤ 19 / 100 + 4 * (((D).card + 1 : ℝ) / N) +
        4 * beta + 4 * beta ^ 2 := by
  let F := D
  let N : ℝ := Fᶜ.card
  let q := coreOutProportion T F x
  have hN0 : 0 < N := by dsimp [N, F]; exact_mod_cast hN
  have hq := coreOutProportion_bounds T F x
  have hpair := cross_pair_bounds q ((F.card + 1 : ℝ) / N) beta hq.1 hq.2
    (by positivity) hb (coreOutProportion_of_exceptional_degree T hn D x hx hN)
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
  rw [core_incoming_sum T F x hxD, heq] at hcol'
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
