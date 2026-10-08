import TournamentHamiltonian.ExceptionalCrossProfiles
import TournamentHamiltonian.FourBlockBounds

/-! Actual exceptional-vertex suppression, with deleted core minors as the analytic input. -/
namespace TournamentHamiltonian
open scoped Classical

theorem exceptional_permanent_normalized_le {n : ℕ} (T : Tournament n) (hn : 2 ≤ n)
    (l r : Fin n → ℝ) (beta B : ℝ) (hb : 0 ≤ beta) (hB : 0 ≤ B)
    (hN : 0 < (exceptionalVertices T)ᶜ.card)
    (hfN : 2 * (exceptionalVertices T).card ≤ (exceptionalVertices T)ᶜ.card)
    (heps : ((exceptionalVertices T).card + 1 : ℝ) / (exceptionalVertices T)ᶜ.card ≤ 1 / 2)
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i)
    (hdl : (∑ j ∈ (exceptionalVertices T)ᶜ, |l j - 1|) ≤ (exceptionalVertices T)ᶜ.card * beta)
    (hdr : (∑ j ∈ (exceptionalVertices T)ᶜ, |r j - 1|) ≤ (exceptionalVertices T)ᶜ.card * beta)
    (hcore : ∀ s ≤ (exceptionalVertices T).card,
      ∀ I ∈ (exceptionalVertices T)ᶜ.powersetCard ((exceptionalVertices T).card - s),
      ∀ J ∈ (exceptionalVertices T)ᶜ.powersetCard ((exceptionalVertices T).card - s),
      selectedPermanent (adjacency T) ((exceptionalVertices T)ᶜ \ J) ((exceptionalVertices T)ᶜ \ I) ≤
        (B * ((((exceptionalVertices T)ᶜ.card - ((exceptionalVertices T).card - s)).factorial : ℝ) /
          (2 : ℝ) ^ ((exceptionalVertices T)ᶜ.card - ((exceptionalVertices T).card - s)))) *
            (∏ i ∈ I, l i) * (∏ j ∈ J, r j)) :
    let f := (exceptionalVertices T).card
    let N : ℝ := (exceptionalVertices T)ᶜ.card
    let c := 19 / 100 + 4 * ((f + 1 : ℝ) / N) + 4 * beta + 4 * beta ^ 2
    let L := 2 + 2 * beta
    (adjacency T).permanent / ((n.factorial : ℝ) / (2 : ℝ) ^ n) ≤
      B * c ^ f * Real.exp (4 * (f : ℝ) ^ 2 / N + 2 * L ^ 2 * (f : ℝ) ^ 2 / (c ^ 2 * N)) := by
  let F := exceptionalVertices T
  let N : ℝ := Fᶜ.card
  let c : ℝ := 19 / 100 + 4 * ((F.card + 1 : ℝ) / N) + 4 * beta + 4 * beta ^ 2
  let L : ℝ := 2 + 2 * beta
  let u : Fin n → ℝ := fun x => 2 / N * ∑ j ∈ Fᶜ, adjacency T x j * r j
  let v : Fin n → ℝ := fun x => 2 / N * ∑ j ∈ Fᶜ, l j * adjacency T j x
  have hN0 : 0 < N := by dsimp [N, F]; exact_mod_cast hN
  have heps0 : 0 ≤ (F.card + 1 : ℝ) / N := by positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hcL : c ≤ L ^ 2 := by dsimp [c, L]; nlinarith
  have hp (x : Fin n) (hx : x ∈ F) :
      0 ≤ u x ∧ 0 ≤ v x ∧ u x ≤ L ∧ v x ≤ L ∧ u x * v x ≤ c :=
    exceptional_weighted_cross_pair T hn x hx hN l r beta hb hl hr hdl hdr
  have hrow (x : Fin n) (_hx : x ∈ F) :
      (∑ j ∈ Fᶜ, adjacency T x j * r j) ≤ (Fᶜ.card : ℝ) / 2 * u x := by
    dsimp [u, N]
    apply le_of_eq
    field_simp [show (Fᶜ.card : ℝ) ≠ 0 from hN0.ne']
  have hcol (x : Fin n) (_hx : x ∈ F) :
      (∑ i ∈ Fᶜ, l i * adjacency T i x) ≤ (Fᶜ.card : ℝ) / 2 * v x := by
    dsimp [v, N]
    apply le_of_eq
    field_simp [show (Fᶜ.card : ℝ) ≠ 0 from hN0.ne']
  have h := permanent_fourBlock_normalized_le (adjacency T) F l r u v B c L
    hB hc hL hcL hN hfN (adjacency_between_nonneg T) (adjacency_between_le_one T) hl hr
    (fun x hx => (hp x hx).1) (fun x hx => (hp x hx).2.1)
    (fun x hx => (hp x hx).2.2.1) (fun x hx => (hp x hx).2.2.2.1)
    (fun x hx => (hp x hx).2.2.2.2) hcore hrow hcol
  simpa only [Fintype.card_fin] using h

end TournamentHamiltonian
