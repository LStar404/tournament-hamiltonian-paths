import TournamentHamiltonian.CrossFactorialNormalization
import TournamentHamiltonian.PairedCrossProducts

/-! Aggregation of the actual four-block expansion. -/
namespace TournamentHamiltonian
open scoped Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem fourBlock_scalar_sum_le (N f : ℕ) (c L : ℝ) (hc : 0 < c) (hL : 0 ≤ L) (hN : 0 < N) :
    (∑ s ∈ Finset.range (f + 1), (f.choose s : ℝ) ^ 2 * (s.factorial : ℝ) *
      (2 / (N : ℝ)) ^ s * c ^ f * (L / c) ^ (2 * s)) ≤
      c ^ f * Real.exp (2 * L ^ 2 * (f : ℝ) ^ 2 / (c ^ 2 * N)) := by
  let x : ℝ := 2 * L ^ 2 * (f : ℝ) ^ 2 / (c ^ 2 * N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hlocal (s : ℕ) : (f.choose s : ℝ) ^ 2 * (s.factorial : ℝ) *
      (2 / (N : ℝ)) ^ s * c ^ f * (L / c) ^ (2 * s) ≤ c ^ f * (x ^ s / (s.factorial : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right (choose_square_mul_factorial_le f s)
      (by positivity : 0 ≤ (2 / (N : ℝ)) ^ s * c ^ f * (L / c) ^ (2 * s))
    convert h using 1 <;> try ring
  calc
    _ ≤ ∑ s ∈ Finset.range (f + 1), c ^ f * (x ^ s / (s.factorial : ℝ)) := Finset.sum_le_sum (fun s _ => hlocal s)
    _ = c ^ f * (∑ s ∈ Finset.range (f + 1), x ^ s / (s.factorial : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ c ^ f * Real.exp x := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx _) (by positivity)

/-- Separate the two actual cross-minor sums after bounding the actual core minor. -/
theorem fourBlock_inner_sum_le (A : Matrix α α ℝ) (F R C : Finset α) (t : ℕ)
    (l r : α → ℝ) (D a b : ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i) (hD : 0 ≤ D) (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hcore : ∀ I ∈ Fᶜ.powersetCard t, ∀ J ∈ Fᶜ.powersetCard t,
      selectedPermanent A (Fᶜ \ J) (Fᶜ \ I) ≤ D * (∏ i ∈ I, l i) * (∏ j ∈ J, r j))
    (haSum : (∑ J ∈ Fᶜ.powersetCard t, selectedPermanent A J (F \ R) * ∏ j ∈ J, r j) ≤ a)
    (hbSum : (∑ I ∈ Fᶜ.powersetCard t, (∏ i ∈ I, l i) * selectedPermanent A (F \ C) I) ≤ b) :
    (∑ I ∈ Fᶜ.powersetCard t, ∑ J ∈ Fᶜ.powersetCard t,
      selectedPermanent A C R * selectedPermanent A J (F \ R) *
        selectedPermanent A (F \ C) I * selectedPermanent A (Fᶜ \ J) (Fᶜ \ I)) ≤
      selectedPermanent A C R * D * a * b := by
  have hper (U V : Finset α) := selectedPermanent_nonneg A U V hA
  have hsumJ0 : 0 ≤ ∑ J ∈ Fᶜ.powersetCard t, selectedPermanent A J (F \ R) * ∏ j ∈ J, r j :=
    Finset.sum_nonneg (fun J _ => mul_nonneg (hper _ _) (Finset.prod_nonneg (fun j _ => hr j)))
  have hsumI0 : 0 ≤ ∑ I ∈ Fᶜ.powersetCard t, (∏ i ∈ I, l i) * selectedPermanent A (F \ C) I :=
    Finset.sum_nonneg (fun I _ => mul_nonneg (Finset.prod_nonneg (fun i _ => hl i)) (hper _ _))
  calc
    _ ≤ ∑ I ∈ Fᶜ.powersetCard t, ∑ J ∈ Fᶜ.powersetCard t,
        selectedPermanent A C R * selectedPermanent A J (F \ R) *
          selectedPermanent A (F \ C) I * (D * (∏ i ∈ I, l i) * (∏ j ∈ J, r j)) := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro J hJ
      exact mul_le_mul_of_nonneg_left (hcore I hI J hJ) (mul_nonneg (mul_nonneg (hper _ _) (hper _ _)) (hper _ _))
    _ = selectedPermanent A C R * D *
        (∑ J ∈ Fᶜ.powersetCard t, selectedPermanent A J (F \ R) * ∏ j ∈ J, r j) *
        (∑ I ∈ Fᶜ.powersetCard t, (∏ i ∈ I, l i) * selectedPermanent A (F \ C) I) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro J _
      apply Finset.sum_congr rfl
      intro I _
      ring
    _ ≤ selectedPermanent A C R * D * a * b := by
      have h := mul_le_mul haSum hbSum hsumI0 ha
      have hh := mul_le_mul_of_nonneg_left h (mul_nonneg (hper C R) hD)
      simpa only [mul_assoc] using hh

/-- Bound the actual permanent by the four-block sum using core-minor and paired cross bounds. -/
theorem permanent_fourBlock_le (A : Matrix α α ℝ) (F : Finset α)
    (l r u v : α → ℝ) (D : ℕ → ℝ) (c L : ℝ) (hc : 0 < c) (hL : 0 ≤ L)
    (hcL : c ≤ L ^ 2) (hA0 : ∀ i j, 0 ≤ A i j) (hA1 : ∀ i j, A i j ≤ 1)
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i) (hD : ∀ s, 0 ≤ D s)
    (hu0 : ∀ x ∈ F, 0 ≤ u x) (hv0 : ∀ x ∈ F, 0 ≤ v x)
    (huL : ∀ x ∈ F, u x ≤ L) (hvL : ∀ x ∈ F, v x ≤ L)
    (huv : ∀ x ∈ F, u x * v x ≤ c)
    (hcore : ∀ s ≤ F.card, ∀ I ∈ Fᶜ.powersetCard (F.card - s),
      ∀ J ∈ Fᶜ.powersetCard (F.card - s),
      selectedPermanent A (Fᶜ \ J) (Fᶜ \ I) ≤ D s * (∏ i ∈ I, l i) * (∏ j ∈ J, r j))
    (hrow : ∀ s ≤ F.card, ∀ R ∈ F.powersetCard s,
      (∑ J ∈ Fᶜ.powersetCard (F.card - s), selectedPermanent A J (F \ R) * ∏ j ∈ J, r j) ≤
        ((Fᶜ.card : ℝ) / 2) ^ (F.card - s) * ∏ x ∈ F \ R, u x)
    (hcol : ∀ s ≤ F.card, ∀ C ∈ F.powersetCard s,
      (∑ I ∈ Fᶜ.powersetCard (F.card - s), (∏ i ∈ I, l i) * selectedPermanent A (F \ C) I) ≤
        ((Fᶜ.card : ℝ) / 2) ^ (F.card - s) * ∏ x ∈ F \ C, v x) :
    A.permanent ≤ ∑ s ∈ Finset.range (F.card + 1), (F.card.choose s : ℝ) ^ 2 *
      (s.factorial : ℝ) * D s * ((Fᶜ.card : ℝ) / 2) ^ (2 * (F.card - s)) *
        c ^ F.card * (L / c) ^ (2 * s) := by
  rw [permanent_four_blocks_by_size A F]
  apply Finset.sum_le_sum
  intro s hs
  have hsF : s ≤ F.card := by have := Finset.mem_range.mp hs; omega
  have hlocal (R : Finset α) (hR : R ∈ F.powersetCard s) (C : Finset α) (hC : C ∈ F.powersetCard s) :
      (∑ I ∈ Fᶜ.powersetCard (F.card - s), ∑ J ∈ Fᶜ.powersetCard (F.card - s),
        selectedPermanent A C R * selectedPermanent A J (F \ R) *
          selectedPermanent A (F \ C) I * selectedPermanent A (Fᶜ \ J) (Fᶜ \ I)) ≤
        (s.factorial : ℝ) * D s * ((Fᶜ.card : ℝ) / 2) ^ (2 * (F.card - s)) *
          c ^ F.card * (L / c) ^ (2 * s) := by
    have hRs := (Finset.mem_powersetCard.mp hR).1
    have hCs := (Finset.mem_powersetCard.mp hC).1
    have hRcard := (Finset.mem_powersetCard.mp hR).2
    have hCcard := (Finset.mem_powersetCard.mp hC).2
    have hprodR : 0 ≤ ∏ x ∈ F \ R, u x := Finset.prod_nonneg (fun x hx => hu0 x (Finset.mem_sdiff.mp hx).1)
    have hprodC : 0 ≤ ∏ x ∈ F \ C, v x := Finset.prod_nonneg (fun x hx => hv0 x (Finset.mem_sdiff.mp hx).1)
    have hh := fourBlock_inner_sum_le A F R C (F.card - s) l r (D s)
      (((Fᶜ.card : ℝ) / 2) ^ (F.card - s) * ∏ x ∈ F \ R, u x)
      (((Fᶜ.card : ℝ) / 2) ^ (F.card - s) * ∏ x ∈ F \ C, v x)
      hA0 hl hr (hD s) (mul_nonneg (by positivity) hprodR) (mul_nonneg (by positivity) hprodC)
      (hcore s hsF) (hrow s hsF R hR) (hcol s hsF C hC)
    have hi : selectedPermanent A C R ≤ (s.factorial : ℝ) := by
      simpa only [hCcard] using selectedPermanent_le_factorial A C R hA0 hA1
    have hp := retained_cross_product_le F R C hRs hCs u v c L hc hL hcL hu0 hv0 huL hvL huv
    rw [hRcard, hCcard, ← two_mul s] at hp
    have hm := mul_le_mul hi hp (mul_nonneg hprodR hprodC) (by positivity : (0 : ℝ) ≤ s.factorial)
    have hfinal := mul_le_mul_of_nonneg_right hm
      (mul_nonneg (hD s) (by positivity : 0 ≤ ((Fᶜ.card : ℝ) / 2) ^ (2 * (F.card - s))))
    apply hh.trans
    convert hfinal using 1 <;> rw [show 2 * (F.card - s) = (F.card - s) + (F.card - s) by omega, pow_add] <;> ring
  calc
    _ ≤ ∑ R ∈ F.powersetCard s, ∑ C ∈ F.powersetCard s,
        (s.factorial : ℝ) * D s * ((Fᶜ.card : ℝ) / 2) ^ (2 * (F.card - s)) *
          c ^ F.card * (L / c) ^ (2 * s) :=
      Finset.sum_le_sum (fun R hR => Finset.sum_le_sum (fun C hC => hlocal R hR C hC))
    _ = _ := by simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]; ring

omit [Fintype α] [DecidableEq α] in
theorem fourBlock_normalized_sum_le (N f : ℕ) (B c L : ℝ) (hB : 0 ≤ B)
    (hc : 0 < c) (hL : 0 ≤ L) (hN : 0 < N) (hfN : 2 * f ≤ N) :
    (∑ s ∈ Finset.range (f + 1), (f.choose s : ℝ) ^ 2 * (s.factorial : ℝ) *
      (B * (((N - (f - s)).factorial : ℝ) / (2 : ℝ) ^ (N - (f - s)))) *
      ((N : ℝ) / 2) ^ (2 * (f - s)) * c ^ f * (L / c) ^ (2 * s)) /
        (((N + f).factorial : ℝ) / (2 : ℝ) ^ (N + f)) ≤
      B * c ^ f * Real.exp (4 * (f : ℝ) ^ 2 / N + 2 * L ^ 2 * (f : ℝ) ^ 2 / (c ^ 2 * N)) := by
  let E : ℝ := Real.exp (4 * (f : ℝ) ^ 2 / N)
  have hlocal (s : ℕ) (hs : s ∈ Finset.range (f + 1)) :
      ((f.choose s : ℝ) ^ 2 * (s.factorial : ℝ) *
        (B * (((N - (f - s)).factorial : ℝ) / (2 : ℝ) ^ (N - (f - s)))) *
        ((N : ℝ) / 2) ^ (2 * (f - s)) * c ^ f * (L / c) ^ (2 * s)) /
          (((N + f).factorial : ℝ) / (2 : ℝ) ^ (N + f)) ≤
      B * E * ((f.choose s : ℝ) ^ 2 * (s.factorial : ℝ) *
        (2 / (N : ℝ)) ^ s * c ^ f * (L / c) ^ (2 * s)) := by
    have hsF : s ≤ f := by have := Finset.mem_range.mp hs; omega
    have hfN' : f ≤ N := by omega
    have heq := fourBlock_cross_normalization N f s hfN' hsF
    have hn := fourBlock_factorial_normalization_le N f s hN hfN hsF
    have h := mul_le_mul_of_nonneg_left hn
      (by positivity : 0 ≤ B * (f.choose s : ℝ) ^ 2 * (s.factorial : ℝ) * c ^ f * (L / c) ^ (2 * s))
    convert h using 1
    · rw [← heq, div_pow]
      ring
    · dsimp [E]
      ring

  rw [Finset.sum_div]
  calc
    _ ≤ ∑ s ∈ Finset.range (f + 1), B * E * ((f.choose s : ℝ) ^ 2 * (s.factorial : ℝ) *
        (2 / (N : ℝ)) ^ s * c ^ f * (L / c) ^ (2 * s)) := by
      apply Finset.sum_le_sum
      intro s hs
      have h := hlocal s hs
      exact h
    _ = B * E * ∑ s ∈ Finset.range (f + 1), (f.choose s : ℝ) ^ 2 * (s.factorial : ℝ) *
        (2 / (N : ℝ)) ^ s * c ^ f * (L / c) ^ (2 * s) := by rw [Finset.mul_sum]
    _ ≤ B * E * (c ^ f * Real.exp (2 * L ^ 2 * (f : ℝ) ^ 2 / (c ^ 2 * N))) :=
      mul_le_mul_of_nonneg_left (fourBlock_scalar_sum_le N f c L hc hL hN) (by dsimp [E]; positivity)
    _ = _ := by dsimp [E]; rw [Real.exp_add]; ring

theorem weighted_cross_column_neighbors_le (A : Matrix α α ℝ) (F G : Finset α)
    (hG : G ⊆ F) (k : ℕ) (r u : α → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hr : ∀ i, 0 ≤ r i)
    (hneighbor : ∀ x ∈ F, (∑ j ∈ Fᶜ, A x j * r j) ≤ (Fᶜ.card : ℝ) / 2 * u x) :
    (∑ J ∈ Fᶜ.powersetCard k, selectedPermanent A J G * ∏ j ∈ J, r j) ≤
      ((Fᶜ.card : ℝ) / 2) ^ G.card * ∏ x ∈ G, u x := by
  apply (weighted_cross_column_sum_le A G Fᶜ k r hA hr).trans
  have h : (∏ x : G, ∑ j : (Fᶜ : Finset α), A x j * r j) ≤ ∏ x : G, (Fᶜ.card : ℝ) / 2 * u x := by
    apply Finset.prod_le_prod₀
    · intro x _
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hA x j) (hr j))
    · intro x _
      rw [Finset.sum_coe_sort Fᶜ (fun j => A x j * r j)]
      exact hneighbor x (hG x.property)
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe, Finset.prod_coe_sort] using h

theorem weighted_cross_row_neighbors_le (A : Matrix α α ℝ) (F G : Finset α)
    (hG : G ⊆ F) (k : ℕ) (l v : α → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hl : ∀ i, 0 ≤ l i)
    (hneighbor : ∀ x ∈ F, (∑ i ∈ Fᶜ, l i * A i x) ≤ (Fᶜ.card : ℝ) / 2 * v x) :
    (∑ I ∈ Fᶜ.powersetCard k, (∏ i ∈ I, l i) * selectedPermanent A G I) ≤
      ((Fᶜ.card : ℝ) / 2) ^ G.card * ∏ x ∈ G, v x := by
  apply (weighted_cross_row_sum_le A G Fᶜ k l hA hl).trans
  have h : (∏ x : G, ∑ i : (Fᶜ : Finset α), l i * A i x) ≤ ∏ x : G, (Fᶜ.card : ℝ) / 2 * v x := by
    apply Finset.prod_le_prod₀
    · intro x _
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hl i) (hA i x))
    · intro x _
      rw [Finset.sum_coe_sort Fᶜ (fun i => l i * A i x)]
      exact hneighbor x (hG x.property)
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe, Finset.prod_coe_sort] using h

/-- The actual normalized permanent has the paired exceptional suppression factor.
The only analytic input is a bound for the actual deleted core minors. -/
theorem permanent_fourBlock_normalized_le (A : Matrix α α ℝ) (F : Finset α)
    (l r u v : α → ℝ) (B c L : ℝ) (hB : 0 ≤ B) (hc : 0 < c) (hL : 0 ≤ L)
    (hcL : c ≤ L ^ 2) (hN : 0 < Fᶜ.card) (hfN : 2 * F.card ≤ Fᶜ.card)
    (hA0 : ∀ i j, 0 ≤ A i j) (hA1 : ∀ i j, A i j ≤ 1)
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i)
    (hu0 : ∀ x ∈ F, 0 ≤ u x) (hv0 : ∀ x ∈ F, 0 ≤ v x)
    (huL : ∀ x ∈ F, u x ≤ L) (hvL : ∀ x ∈ F, v x ≤ L)
    (huv : ∀ x ∈ F, u x * v x ≤ c)
    (hcore : ∀ s ≤ F.card, ∀ I ∈ Fᶜ.powersetCard (F.card - s),
      ∀ J ∈ Fᶜ.powersetCard (F.card - s),
      selectedPermanent A (Fᶜ \ J) (Fᶜ \ I) ≤
        (B * (((Fᶜ.card - (F.card - s)).factorial : ℝ) / (2 : ℝ) ^ (Fᶜ.card - (F.card - s)))) *
          (∏ i ∈ I, l i) * (∏ j ∈ J, r j))
    (hrow : ∀ x ∈ F, (∑ j ∈ Fᶜ, A x j * r j) ≤ (Fᶜ.card : ℝ) / 2 * u x)
    (hcol : ∀ x ∈ F, (∑ i ∈ Fᶜ, l i * A i x) ≤ (Fᶜ.card : ℝ) / 2 * v x) :
    A.permanent / ((Fintype.card α).factorial / (2 : ℝ) ^ Fintype.card α) ≤
      B * c ^ F.card * Real.exp (4 * (F.card : ℝ) ^ 2 / Fᶜ.card +
        2 * L ^ 2 * (F.card : ℝ) ^ 2 / (c ^ 2 * Fᶜ.card)) := by
  let D : ℕ → ℝ := fun s => B * (((Fᶜ.card - (F.card - s)).factorial : ℝ) /
    (2 : ℝ) ^ (Fᶜ.card - (F.card - s)))
  have hp := permanent_fourBlock_le A F l r u v D c L hc hL hcL hA0 hA1 hl hr
    (fun s => by dsimp [D]; positivity) hu0 hv0 huL hvL huv hcore
    (by
      intro s hs R hR
      have h := weighted_cross_column_neighbors_le A F (F \ R) Finset.sdiff_subset
        (F.card - s) r u hA0 hr hrow
      rwa [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp hR).1,
        (Finset.mem_powersetCard.mp hR).2] at h)
    (by
      intro s hs C hC
      have h := weighted_cross_row_neighbors_le A F (F \ C) Finset.sdiff_subset
        (F.card - s) l v hA0 hl hcol
      rwa [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp hC).1,
        (Finset.mem_powersetCard.mp hC).2] at h)
  have hz : (Fintype.card α).factorial / (2 : ℝ) ^ Fintype.card α =
      ((Fᶜ.card + F.card).factorial : ℝ) / (2 : ℝ) ^ (Fᶜ.card + F.card) := by
    rw [add_comm Fᶜ.card F.card, Finset.card_add_card_compl]
  rw [hz]
  apply (div_le_div_of_nonneg_right hp (by positivity)).trans
  exact fourBlock_normalized_sum_le Fᶜ.card F.card B c L hB hc hL hN hfN

end TournamentHamiltonian
