import TournamentHamiltonian.CoreEncodingData

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types true

theorem encodedCoreHalfEdges_card {j b : ℕ} (d : compressedDegreeSequences j b) :
    Fintype.card (Σ i : Fin b, Fin (d.val i)) = 2 * (b + j) := by
  rw [Fintype.card_sigma]
  simpa only [Fintype.card_fin] using (mem_compressedDegreeSequences.mp d.property).1

theorem encodedCorePaths_card {j b : ℕ} (d : compressedDegreeSequences j b)
    (p : PairingMap (Σ i : Fin b, Fin (d.val i))) :
    Fintype.card (Quotient (pairingSetoid p)) = b + j := by
  have hs := coordinatePartitionDegree_sum (pairingSetoid p)
  have hd : ∀ v : Quotient (pairingSetoid p), coordinatePartitionDegree (pairingSetoid p) v = 2 := by
    intro v
    rw [← partitionBlock_card_eq_degree]
    exact pairingSetoid_isPairing p v
  simp_rw [hd] at hs
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  rw [encodedCoreHalfEdges_card d] at hs
  omega

theorem pairingProduct_eq_doubleFactorial (e : ℕ) :
    pairingProduct e = (2 * e - 1).doubleFactorial := by
  induction e with
  | zero => simp [pairingProduct, Nat.doubleFactorial]
  | succ e ih =>
      rw [show 2 * (e + 1) - 1 = 2 * e + 1 by omega, Nat.doubleFactorial_add_one,
        ← ih]
      simp only [pairingProduct, Finset.prod_range_succ]
      ring

theorem encodedCorePairings_card {j b : ℕ} (d : compressedDegreeSequences j b) :
    Fintype.card (PairingMap (Σ i : Fin b, Fin (d.val i))) = pairingProduct (b + j) := by
  rw [pairingMap_card_eq_doubleFactorial, encodedCoreHalfEdges_card d, pairingProduct_eq_doubleFactorial]
  simp

noncomputable def encodedCoreLengthMass (C q R : ℝ) {j b : ℕ}
    (d : compressedDegreeSequences j b) (k : ℕ) : ℝ :=
  ∑ p : PairingMap (Σ i : Fin b, Fin (d.val i)),
    ∑ L : PositiveCoreLengths (Quotient (pairingSetoid p)) k,
      ∏ c, positiveChainWeight C q R ((L.val c).val - 1)

theorem encodedCoreLengthMass_finite_window_le (s : Finset ℕ) (C q R : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hR : 0 ≤ R) (hgap : R * q < 1)
    {j b : ℕ} (d : compressedDegreeSequences j b) :
    (∑ k ∈ s, encodedCoreLengthMass C q R d k) ≤
      (pairingProduct (b + j) : ℝ) *
        (C * R + C ^ 2 * R ^ 2 / (1 - R * q)) ^ (b + j) := by
  unfold encodedCoreLengthMass
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ p : PairingMap (Σ i : Fin b, Fin (d.val i)),
        (C * R + C ^ 2 * R ^ 2 / (1 - R * q)) ^ (b + j) := by
      apply Finset.sum_le_sum
      intro p _
      simpa only [encodedCorePaths_card d p] using
        positiveCoreLengths_finite_window_le (α := Quotient (pairingSetoid p)) s C q R hC hq hR hgap
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, encodedCorePairings_card d]

theorem encodedCoreAssignment_sum_cancel {α : Type*} [Fintype α] {k : ℕ}
    (L : PositiveCoreLengths α k) (w : ℝ) :
    (∑ _a : (Σ c : α, Fin ((L.val c).val)) ≃ Fin k, w / (k.factorial : ℝ)) = w := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, encodedCoreAssignment_card L]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  exact mul_div_cancel₀ w hk

theorem encodedCoreAssignment_sum_cancel_general {α κ : Type*} [Fintype α] [Fintype κ]
    [DecidableEq α] [DecidableEq κ]
    (L : PositiveCoreLengths α (Fintype.card κ)) (w : ℝ) :
    (∑ _a : (Σ c : α, Fin ((L.val c).val)) ≃ κ, w / ((Fintype.card κ).factorial : ℝ)) = w := by
  have hcard : Fintype.card (Σ c : α, Fin ((L.val c).val)) = Fintype.card κ := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using L.property.2
  let e : (Σ c : α, Fin ((L.val c).val)) ≃ κ :=
    ((Fintype.equivFin _).trans (finCongr hcard)).trans (Fintype.equivFin κ).symm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_equiv e, hcard]
  have hk : ((Fintype.card κ).factorial : ℝ) ≠ 0 := by positivity
  exact mul_div_cancel₀ w hk

private theorem finiteDecoratedAssignmentSum {D Col : Type*} [Fintype D] [Fintype Col]
    {P : D → Type*} [∀ d, Fintype (P d)]
    {L : ∀ d, P d → Type*} [∀ d p, Fintype (L d p)]
    {A : ∀ d p, L d p → Type*} [∀ d p l, Fintype (A d p l)]
    (w : ∀ d p, L d p → ℝ) (a : ℝ)
    (hf : ∀ d p l, (∑ _x : A d p l, w d p l / a) = w d p l) :
    (∑ x : Σ d : D, Col × (Σ p : P d, Σ l : L d p, A d p l),
      w x.1 x.2.2.1 x.2.2.2.1 / a) =
      (Fintype.card Col : ℝ) * ∑ d, ∑ p, ∑ l, w d p l := by
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  simp_rw [hf]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

set_option maxHeartbeats 1000000 in
theorem encodedCoreData_weight_sum_normalized_general {κ : Type*} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (C q R : ℝ) (j b : ℕ) :
    (∑ x : EncodedCoreData κ j b, encodedCorePathWeight n C q R x) /
      ((Fintype.card κ).factorial : ℝ) =
      ∑ d : compressedDegreeSequences j b,
        (2 : ℝ) ^ b * encodedCoreLengthMass C q R d (Fintype.card κ) /
          ((b.factorial : ℝ) * (∏ i, (d.val i : ℝ)) * (n : ℝ) ^ j) := by
  rw [Finset.sum_div]
  calc
    _ = ∑ x : EncodedCoreDataSigma κ j b,
        (∏ c : Quotient (pairingSetoid x.2.2.1),
          positiveChainWeight C q R ((x.2.2.2.1.val c).val - 1)) /
          ((b.factorial : ℝ) * (∏ i, (x.1.val i : ℝ)) * (n : ℝ) ^ j) /
          ((Fintype.card κ).factorial : ℝ) := by
      apply Fintype.sum_equiv (encodedCoreDataEquiv κ j b)
      intro x
      rfl
    _ = (Fintype.card (Fin b → Bool) : ℝ) * ∑ d : compressedDegreeSequences j b,
        encodedCoreLengthMass C q R d (Fintype.card κ) /
          ((b.factorial : ℝ) * (∏ i, (d.val i : ℝ)) * (n : ℝ) ^ j) := by
      have h := finiteDecoratedAssignmentSum
        (D := compressedDegreeSequences j b) (Col := Fin b → Bool)
        (P := fun d => PairingMap (Σ i : Fin b, Fin (d.val i)))
        (L := fun _ p => PositiveCoreLengths (Quotient (pairingSetoid p)) (Fintype.card κ))
        (A := fun _ p L => (Σ c : Quotient (pairingSetoid p), Fin ((L.val c).val)) ≃ κ)
        (fun d p L => (∏ c, positiveChainWeight C q R ((L.val c).val - 1)) /
          ((b.factorial : ℝ) * (∏ i, (d.val i : ℝ)) * (n : ℝ) ^ j))
        ((Fintype.card κ).factorial : ℝ)
        (fun _ _ L => encodedCoreAssignment_sum_cancel_general L _)
      simpa only [encodedCoreLengthMass, Finset.sum_div] using h
    _ = _ := by
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring

theorem encodedCoreData_weight_sum_normalized (n : ℕ) (C q R : ℝ) (j b k : ℕ) :
    (∑ x : EncodedCoreData (Fin k) j b, encodedCorePathWeight n C q R x) / (k.factorial : ℝ) =
      ∑ d : compressedDegreeSequences j b,
        (2 : ℝ) ^ b * encodedCoreLengthMass C q R d k /
          ((b.factorial : ℝ) * (∏ i, (d.val i : ℝ)) * (n : ℝ) ^ j) := by
  simpa only [Fintype.card_fin] using encodedCoreData_weight_sum_normalized_general (κ := Fin k) n C q R j b

theorem compressedDegreeCompensation_subtype_sum (j b : ℕ) :
    compressedDegreeCompensation j b = ∑ d : compressedDegreeSequences j b,
      ((2 : ℝ) ^ b * (pairingProduct (b + j) : ℝ)) /
        ((b.factorial : ℝ) * ∏ i, (d.val i : ℝ)) := by
  have hs : (∑ d : compressedDegreeSequences j b, ∏ i, (d.val i : ℝ)⁻¹) =
      ∑ d ∈ compressedDegreeSequences j b, ∏ i, (d i : ℝ)⁻¹ :=
    Finset.sum_coe_sort (compressedDegreeSequences j b) (fun d : Fin b → ℕ => ∏ i, (d i : ℝ)⁻¹)
  calc
    _ = ((2 : ℝ) ^ b / (b.factorial : ℝ) * (pairingProduct (b + j) : ℝ)) *
        ∑ d : compressedDegreeSequences j b, ∏ i, (d.val i : ℝ)⁻¹ := by
      rw [hs, ← pairing_factorial_ratio_eq]
      unfold compressedDegreeCompensation
      ring
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.prod_inv_distrib]
      ring

/-- Counting all finite encoded cores removes the original-edge factorial and
leaves precisely the manuscript compensation coefficient. -/
theorem encodedCoreData_finite_window_weight_le (n : ℕ) (C q R : ℝ) (j b : ℕ)
    (s : Finset ℕ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hR : 0 ≤ R) (hgap : R * q < 1) :
    (∑ k ∈ s, (∑ x : EncodedCoreData (Fin k) j b, encodedCorePathWeight n C q R x) /
      (k.factorial : ℝ)) ≤
      compressedDegreeCompensation j b *
        (C * R + C ^ 2 * R ^ 2 / (1 - R * q)) ^ (b + j) / (n : ℝ) ^ j := by
  simp_rw [encodedCoreData_weight_sum_normalized]
  rw [Finset.sum_comm]
  calc
    _ = ∑ d : compressedDegreeSequences j b,
        ((2 : ℝ) ^ b / ((b.factorial : ℝ) * (∏ i, (d.val i : ℝ)) * (n : ℝ) ^ j)) *
          ∑ k ∈ s, encodedCoreLengthMass C q R d k := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ ∑ d : compressedDegreeSequences j b,
        ((2 : ℝ) ^ b / ((b.factorial : ℝ) * (∏ i, (d.val i : ℝ)) * (n : ℝ) ^ j)) *
          ((pairingProduct (b + j) : ℝ) *
            (C * R + C ^ 2 * R ^ 2 / (1 - R * q)) ^ (b + j)) := by
      apply Finset.sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left (encodedCoreLengthMass_finite_window_le s C q R hC hq hR hgap d)
        (by positivity)
    _ = _ := by
      rw [compressedDegreeCompensation_subtype_sum, Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d _
      ring

end TournamentHamiltonian
