import TournamentHamiltonian.CoreExcessDecorationMass
import TournamentHamiltonian.CompressedCoreMajorant

/-! Actual finite encoded cores and their length-weighted counting bounds. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

abbrev PositiveCoreLengths (α : Type*) [Fintype α] (k : ℕ) :=
  {L : α → Fin (k + 1) // (∀ a, 0 < (L a).val) ∧ (∑ a, (L a).val) = k}

def positiveCoreLengthsNat {α : Type*} [Fintype α] {k : ℕ}
    (L : PositiveCoreLengths α k) : α → ℕ := fun a => (L.val a).val

theorem positiveCoreLengthsNat_injective {α : Type*} [Fintype α] (k : ℕ) :
    Function.Injective (positiveCoreLengthsNat (α := α) (k := k)) := by
  intro L M h
  apply Subtype.ext
  funext a
  exact Fin.ext (congrFun h a)

theorem positiveCoreLengths_sigma_injective {α : Type*} [Fintype α] (s : Finset ℕ) :
    Function.Injective (fun x : Σ k : s, PositiveCoreLengths α k.val => positiveCoreLengthsNat x.2) := by
  rintro ⟨⟨k, hk⟩, L⟩ ⟨⟨m, hm⟩, M⟩ h
  have hkm : k = m := by
    calc
      k = ∑ a, (L.val a).val := L.property.2.symm
      _ = ∑ a, (M.val a).val := Finset.sum_congr rfl (fun a _ => congrFun h a)
      _ = m := M.property.2
  subst m
  have hLM : L = M := positiveCoreLengthsNat_injective k h
  subst M
  rfl

theorem positiveCoreLengths_finite_window_le {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset ℕ) (C q R : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hgap : R * q < 1) :
    (∑ k ∈ s, ∑ L : PositiveCoreLengths α k,
      ∏ a, positiveChainWeight C q R ((L.val a).val - 1)) ≤
      (C * R + C ^ 2 * R ^ 2 / (1 - R * q)) ^ Fintype.card α := by
  let f : (Σ k : s, PositiveCoreLengths α k.val) → (α → ℕ) :=
    fun x a => (x.2.val a).val - 1
  have hf : Function.Injective f := by
    intro x y h
    apply positiveCoreLengths_sigma_injective s
    funext a
    have ha := congrFun h a
    have hx := x.2.property.1 a
    have hy := y.2.property.1 a
    dsimp [f] at ha
    change (x.2.val a).val = (y.2.val a).val
    omega
  calc
    _ = ∑ x : Σ k : s, PositiveCoreLengths α k.val, ∏ a, positiveChainWeight C q R (f x a) := by
      rw [Fintype.sum_sigma]
      exact (Finset.sum_coe_sort s _).symm
    _ = ∑ L ∈ Finset.univ.image f, ∏ a, positiveChainWeight C q R (L a) := by
      rw [Finset.sum_image hf.injOn]
    _ ≤ _ := positiveChainWeight_finite_length_sum_le _ C q R hC hq hR hgap

variable (κ : Type*) [Fintype κ]

structure EncodedCoreData (j b : ℕ) where
  degree : compressedDegreeSequences j b
  colors : Fin b → Bool
  pairing : PairingMap (Σ i : Fin b, Fin (degree.val i))
  lengths : Quotient (pairingSetoid pairing) → Fin (Fintype.card κ + 1)
  positive : ∀ c, 0 < (lengths c).val
  total : (∑ c, (lengths c).val) = Fintype.card κ
  assignment : (Σ c : Quotient (pairingSetoid pairing), Fin ((lengths c).val)) ≃ κ

abbrev EncodedCoreDataSigma (j b : ℕ) :=
  Σ d : compressedDegreeSequences j b, (Fin b → Bool) ×
    (Σ p : PairingMap (Σ i : Fin b, Fin (d.val i)),
      Σ L : PositiveCoreLengths (Quotient (pairingSetoid p)) (Fintype.card κ),
        (Σ c : Quotient (pairingSetoid p), Fin ((L.val c).val)) ≃ κ)

def encodedCoreDataEquiv (j b : ℕ) : EncodedCoreData κ j b ≃ EncodedCoreDataSigma κ j b where
  toFun x := ⟨x.degree, x.colors, x.pairing, ⟨x.lengths, x.positive, x.total⟩, x.assignment⟩
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1.val, x.2.2.2.1.property.1,
    x.2.2.2.1.property.2, x.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance encodedCoreDataFintype (j b : ℕ) : Fintype (EncodedCoreData κ j b) :=
  Fintype.ofEquiv (EncodedCoreDataSigma κ j b) (encodedCoreDataEquiv κ j b).symm

variable {κ}

noncomputable def encodedCorePathWeight (n : ℕ) (C q R : ℝ) {j b : ℕ}
    (x : EncodedCoreData κ j b) : ℝ :=
  (∏ c : Quotient (pairingSetoid x.pairing), positiveChainWeight C q R ((x.lengths c).val - 1)) /
    ((b.factorial : ℝ) * (∏ i, (x.degree.val i : ℝ)) * (n : ℝ) ^ j)

theorem encodedCorePathWeight_nonneg (n : ℕ) (C q R : ℝ) {j b : ℕ}
    (x : EncodedCoreData κ j b) (hC : 0 ≤ C) (hq : 0 ≤ q) (hR : 0 ≤ R) :
    0 ≤ encodedCorePathWeight n C q R x := by
  apply div_nonneg
  · exact Finset.prod_nonneg (fun c _ => positiveChainWeight_nonneg C q R hC hq hR _)
  · positivity

theorem encodedCoreAssignment_card {α : Type*} [Fintype α] {k : ℕ}
    (L : PositiveCoreLengths α k) :
    Fintype.card ((Σ c : α, Fin ((L.val c).val)) ≃ Fin k) = k.factorial := by
  have hcard : Fintype.card (Σ c : α, Fin ((L.val c).val)) = k := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using L.property.2
  let e : (Σ c : α, Fin ((L.val c).val)) ≃ Fin k :=
    (Fintype.equivFin _).trans (finCongr hcard)
  rw [Fintype.card_equiv e, hcard]

end TournamentHamiltonian
