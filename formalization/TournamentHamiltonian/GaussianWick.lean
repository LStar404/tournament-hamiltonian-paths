import TournamentHamiltonian.GaussianMoments
import TournamentHamiltonian.PartitionChromatic
import TournamentHamiltonian.PairingCardinality

/-! Actual finite Gaussian bilinear moments and their coordinate expansion. -/

namespace TournamentHamiltonian

open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {κ ι ρ : Type*} [Fintype κ] [Fintype ι] [Fintype ρ]

noncomputable def tupleMultiplicity (r : κ → ι) (a : ι) : ℕ :=
  (Finset.univ.filter (fun e => r e = a)).card

theorem tuple_prod_eq_prod_powers {R : Type*} [CommMonoid R] (r : κ → ι) (x : ι → R) :
    (∏ e : κ, x (r e)) = ∏ a : ι, x a ^ tupleMultiplicity r a := by
  simpa [tupleMultiplicity] using
    (Finset.prod_fiberwise' (Finset.univ : Finset κ) r x).symm

noncomputable def standardGaussianTupleMoment (r : κ → ι) : ℝ :=
  ∫ x : ι → ℝ, ∏ e : κ, x (r e) ∂Measure.pi (fun _ => gaussianReal 0 1)

theorem standardGaussianTupleMoment_eq (r : κ → ι) :
    standardGaussianTupleMoment r = ∏ a : ι, standardGaussianMoment (tupleMultiplicity r a) := by
  simp only [standardGaussianTupleMoment, tuple_prod_eq_prod_powers]
  exact standardGaussian_product_moment _

theorem standardGaussianTuple_integrable (r : κ → ι) :
    Integrable (fun x : ι → ℝ => ∏ e : κ, x (r e)) (Measure.pi (fun _ => gaussianReal 0 1)) := by
  simpa only [tuple_prod_eq_prod_powers] using
    standardGaussian_product_integrable (tupleMultiplicity r)

theorem standardGaussianTupleMoment_nonneg (r : κ → ι) :
    0 ≤ standardGaussianTupleMoment r := by
  rw [standardGaussianTupleMoment_eq]
  exact Finset.prod_nonneg (fun _ _ => standardGaussianMoment_nonneg _)

theorem tupleMultiplicity_sum (r : κ → ι) :
    (∑ a : ι, tupleMultiplicity r a) = Fintype.card κ := by
  simpa [tupleMultiplicity] using
    (Finset.sum_fiberwise (Finset.univ : Finset κ) r (fun _ => (1 : ℕ)))

theorem standardGaussianTupleMoment_odd {k : ℕ} (r : Fin (2 * k + 1) → ι) :
    standardGaussianTupleMoment r = 0 := by
  rw [standardGaussianTupleMoment_eq]
  have hex : ∃ a : ι, Odd (tupleMultiplicity r a) := by
    by_contra hn
    have hall : ∀ a : ι, Even (tupleMultiplicity r a) := by
      simpa only [not_exists, Nat.not_odd_iff_even] using hn
    have he : Even (∑ a : ι, tupleMultiplicity r a) :=
      Finset.even_sum (tupleMultiplicity r) (fun a _ => hall a)
    rw [tupleMultiplicity_sum, Fintype.card_fin] at he
    exact (Nat.not_even_iff_odd.mpr (by exact ⟨k, rfl⟩)) he
  obtain ⟨a, j, hj⟩ := hex
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  rw [hj, standardGaussianMoment_odd]

/-- Independent standard Gaussian vectors of arbitrary rectangular dimensions. -/
noncomputable def gaussianBilinearMoment (Z : Matrix ι ρ ℝ) (k : ℕ) : ℝ :=
  ∫ x : ι → ℝ, ∫ y : ρ → ℝ,
    (∑ a : ι, ∑ b : ρ, x a * Z a b * y b) ^ k
      ∂Measure.pi (fun _ => gaussianReal 0 1)
    ∂Measure.pi (fun _ => gaussianReal 0 1)

theorem bilinear_pow_coordinate_expansion (Z : Matrix ι ρ ℝ) (k : ℕ)
    (x : ι → ℝ) (y : ρ → ℝ) :
    (∑ a : ι, ∑ b : ρ, x a * Z a b * y b) ^ k =
      ∑ r : Fin k → ι, ∑ c : Fin k → ρ,
        (∏ e : Fin k, Z (r e) (c e)) * (∏ e : Fin k, x (r e)) * (∏ e : Fin k, y (c e)) := by
  calc
    _ = ∏ _ : Fin k, (∑ a : ι, ∑ b : ρ, x a * Z a b * y b) := by simp
    _ = _ := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro e _
      ring

theorem gaussianBilinearMoment_coordinate_expansion (Z : Matrix ι ρ ℝ) (k : ℕ) :
    gaussianBilinearMoment Z k =
      ∑ r : Fin k → ι, ∑ c : Fin k → ρ,
        (∏ e : Fin k, Z (r e) (c e)) *
          standardGaussianTupleMoment r * standardGaussianTupleMoment c := by
  unfold gaussianBilinearMoment
  simp_rw [bilinear_pow_coordinate_expansion]
  have hy (x : ι → ℝ) (r : Fin k → ι) (c : Fin k → ρ) :
      Integrable (fun y : ρ → ℝ => (∏ e, Z (r e) (c e)) *
        (∏ e, x (r e)) * (∏ e, y (c e))) (Measure.pi (fun _ => gaussianReal 0 1)) :=
    (standardGaussianTuple_integrable c).const_mul _
  have hi (x : ι → ℝ) :
      (∫ y : ρ → ℝ, ∑ r : Fin k → ι, ∑ c : Fin k → ρ,
        (∏ e, Z (r e) (c e)) * (∏ e, x (r e)) * (∏ e, y (c e))
          ∂Measure.pi (fun _ => gaussianReal 0 1)) =
        ∑ r : Fin k → ι, ∑ c : Fin k → ρ,
          (∏ e, Z (r e) (c e)) * (∏ e, x (r e)) * standardGaussianTupleMoment c := by
    rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun c _ => hy x r c))]
    apply Finset.sum_congr rfl
    intro r _
    rw [integral_finsetSum _ (fun c _ => hy x r c)]
    apply Finset.sum_congr rfl
    intro c _
    rw [integral_const_mul]
    rfl
  simp_rw [hi]
  have hx (r : Fin k → ι) (c : Fin k → ρ) :
      Integrable (fun x : ι → ℝ => (∏ e, Z (r e) (c e)) *
        (∏ e, x (r e)) * standardGaussianTupleMoment c)
        (Measure.pi (fun _ => gaussianReal 0 1)) :=
    ((standardGaussianTuple_integrable r).const_mul _).mul_const _
  change (∫ x : ι → ℝ, ∑ r : Fin k → ι, ∑ c : Fin k → ρ,
    (∏ e, Z (r e) (c e)) * (∏ e, x (r e)) * standardGaussianTupleMoment c
      ∂Measure.pi (fun _ => gaussianReal 0 1)) = _
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun c _ => hx r c))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum _ (fun c _ => hx r c)]
  apply Finset.sum_congr rfl
  intro c _
  rw [integral_mul_const, integral_const_mul]
  rfl

theorem gaussianBilinearMoment_odd (Z : Matrix ι ρ ℝ) (k : ℕ) :
    gaussianBilinearMoment Z (2 * k + 1) = 0 := by
  rw [gaussianBilinearMoment_coordinate_expansion]
  simp only [standardGaussianTupleMoment_odd, mul_zero, Finset.sum_const_zero]

theorem gaussianBilinearMoment_even_nonneg (Z : Matrix ι ρ ℝ) (k : ℕ) :
    0 ≤ gaussianBilinearMoment Z (2 * k) := by
  unfold gaussianBilinearMoment
  apply integral_nonneg
  intro x
  apply integral_nonneg
  intro y
  exact Even.pow_nonneg (even_two_mul k) _

theorem standardGaussianMoment_eq_pairing_number (k : ℕ) :
    standardGaussianMoment k =
      ((if Even k then (k - 1).doubleFactorial else 0 : ℕ) : ℝ) := by
  by_cases hk : Even k
  · rw [ite_eq_left hk]
    obtain ⟨j, hj⟩ := hk
    rw [hj, show j + j = 2 * j by omega, standardGaussianMoment_even]
  · rw [ite_eq_right hk, Nat.cast_zero]
    obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp hk
    rw [hj, standardGaussianMoment_odd]

/-- Real Wick's formula for repeated coordinates, with all pairings counted exactly. -/
theorem standardGaussianTupleMoment_pairing_count (r : κ → ι) :
    standardGaussianTupleMoment r =
      ((Finset.univ.filter (fun P : Setoid κ => IsPairingPartition P ∧ P ≤ Setoid.ker r)).card : ℝ) := by
  rw [standardGaussianTupleMoment_eq, compatible_pairingPartition_count, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro a _
  exact standardGaussianMoment_eq_pairing_number (tupleMultiplicity r a)

theorem standardGaussianTupleMoment_pairing_sum (r : κ → ι) :
    standardGaussianTupleMoment r =
      ∑ P ∈ Finset.univ.filter (fun P : Setoid κ => IsPairingPartition P),
        if P ≤ Setoid.ker r then (1 : ℝ) else 0 := by
  rw [standardGaussianTupleMoment_pairing_count, ← Finset.sum_filter]
  simp only [Finset.filter_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The same block-label contraction with distinct row and column index types. -/
noncomputable def rectangularPartitionContraction (Z : Matrix ι ρ ℝ) (P Q : Setoid κ) : ℝ :=
  ∑ r : Quotient P → ι, ∑ c : Quotient Q → ρ,
    ∏ e : κ, Z (r (Quotient.mk P e)) (c (Quotient.mk Q e))

private theorem sum_quotient_labels {α : Type*} [Fintype α] [DecidableEq κ] (P : Setoid κ)
    (w : (κ → α) → ℝ) :
    (∑ r : Quotient P → α, w (r ∘ Quotient.mk P)) =
      ∑ r ∈ Finset.univ.filter (fun r : κ → α => P ≤ Setoid.ker r), w r := by
  calc
    _ = ∑ r : {r : κ → α // P ≤ Setoid.ker r}, w r := by
      apply (Fintype.sum_equiv (Setoid.liftEquiv P) _ _ ?_).symm
      intro r
      congr 1
    _ = _ := (Finset.sum_subtype _ (by simp) w).symm

theorem rectangularPartitionContraction_eq [DecidableEq κ] (Z : Matrix ι ρ ℝ) (P Q : Setoid κ) :
    rectangularPartitionContraction Z P Q =
      ∑ r ∈ Finset.univ.filter (fun r : κ → ι => P ≤ Setoid.ker r),
        ∑ c ∈ Finset.univ.filter (fun c : κ → ρ => Q ≤ Setoid.ker c),
          ∏ e : κ, Z (r e) (c e) := by
  unfold rectangularPartitionContraction
  calc
    _ = ∑ r : Quotient P → ι,
        ∑ c ∈ Finset.univ.filter (fun c : κ → ρ => Q ≤ Setoid.ker c),
          ∏ e : κ, Z (r (Quotient.mk P e)) (c e) := by
      apply Finset.sum_congr rfl
      intro r _
      exact sum_quotient_labels Q (fun c => ∏ e : κ, Z (r (Quotient.mk P e)) (c e))
    _ = _ := sum_quotient_labels P (fun r =>
      ∑ c ∈ Finset.univ.filter (fun c : κ → ρ => Q ≤ Setoid.ker c), ∏ e : κ, Z (r e) (c e))

theorem rectangularPartitionContraction_square (Z : Matrix ι ι ℝ) (P Q : Setoid κ) :
    rectangularPartitionContraction Z P Q = partitionContraction Z P Q := rfl

private theorem sum_four_swap {α β γ δ : Type*} (s : Finset α) (t : Finset β)
    (u : Finset γ) (v : Finset δ) (f : α → β → γ → δ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a b c d) =
      ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, f a b c d := by
  calc
    _ = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, ∑ d ∈ v, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, ∑ d ∈ v, f a b c d := Finset.sum_comm
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ d ∈ v, ∑ b ∈ t, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]

set_option maxHeartbeats 1000000 in
/-- Wick's two-pairing formula for arbitrary rectangular real bilinear Gaussian moments. -/
theorem gaussianBilinearMoment_pairing_expansion (Z : Matrix ι ρ ℝ) (k : ℕ) :
    gaussianBilinearMoment Z k =
      ∑ P ∈ Finset.univ.filter (fun P : Setoid (Fin k) => IsPairingPartition P),
        ∑ Q ∈ Finset.univ.filter (fun Q : Setoid (Fin k) => IsPairingPartition Q),
          rectangularPartitionContraction Z P Q := by
  classical
  rw [gaussianBilinearMoment_coordinate_expansion]
  let w (r : Fin k → ι) (c : Fin k → ρ) : ℝ := ∏ e : Fin k, Z (r e) (c e)
  change (∑ r : Fin k → ι, ∑ c : Fin k → ρ,
    w r c * standardGaussianTupleMoment r * standardGaussianTupleMoment c) = _
  simp_rw [standardGaussianTupleMoment_pairing_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [sum_four_swap]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P _
  apply Finset.sum_congr rfl
  intro Q _
  rw [rectangularPartitionContraction_eq]
  change (∑ r : Fin k → ι, ∑ c : Fin k → ρ,
    w r c * (if P ≤ Setoid.ker r then 1 else 0) * (if Q ≤ Setoid.ker c then 1 else 0)) =
      ∑ r ∈ Finset.univ.filter (fun r : Fin k → ι => P ≤ Setoid.ker r),
        ∑ c ∈ Finset.univ.filter (fun c : Fin k → ρ => Q ≤ Setoid.ker c), w r c
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hp : P ≤ Setoid.ker r
  · simp only [hp, ite_true, mul_one]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hq : Q ≤ Setoid.ker c <;> simp [hq]
  · simp [hp]

end TournamentHamiltonian
