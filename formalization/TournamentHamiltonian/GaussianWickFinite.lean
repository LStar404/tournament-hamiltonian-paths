import TournamentHamiltonian.GaussianWick

/-! Wick expansion on arbitrary finite edge label types, with actual Gaussian integrals. -/
namespace TournamentHamiltonian
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false
variable {κ ι ρ : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [Fintype ρ]
theorem bilinear_pow_coordinate_expansion_finite (Z : Matrix ι ρ ℝ)
    (x : ι → ℝ) (y : ρ → ℝ) :
    (∑ a : ι, ∑ b : ρ, x a * Z a b * y b) ^ Fintype.card κ =
      ∑ r : κ → ι, ∑ c : κ → ρ,
        (∏ e : κ, Z (r e) (c e)) * (∏ e : κ, x (r e)) * (∏ e : κ, y (c e)) := by
  calc
    _ = ∏ _ : κ, (∑ a : ι, ∑ b : ρ, x a * Z a b * y b) := by simp
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

theorem gaussianBilinearMoment_coordinate_expansion_finite (Z : Matrix ι ρ ℝ)  :
    gaussianBilinearMoment Z (Fintype.card κ) =
      ∑ r : κ → ι, ∑ c : κ → ρ,
        (∏ e : κ, Z (r e) (c e)) *
          standardGaussianTupleMoment r * standardGaussianTupleMoment c := by
  unfold gaussianBilinearMoment
  simp_rw [bilinear_pow_coordinate_expansion_finite]
  have hy (x : ι → ℝ) (r : κ → ι) (c : κ → ρ) :
      Integrable (fun y : ρ → ℝ => (∏ e, Z (r e) (c e)) *
        (∏ e, x (r e)) * (∏ e, y (c e))) (Measure.pi (fun _ => gaussianReal 0 1)) :=
    (standardGaussianTuple_integrable c).const_mul _
  have hi (x : ι → ℝ) :
      (∫ y : ρ → ℝ, ∑ r : κ → ι, ∑ c : κ → ρ,
        (∏ e, Z (r e) (c e)) * (∏ e, x (r e)) * (∏ e, y (c e))
          ∂Measure.pi (fun _ => gaussianReal 0 1)) =
        ∑ r : κ → ι, ∑ c : κ → ρ,
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
  have hx (r : κ → ι) (c : κ → ρ) :
      Integrable (fun x : ι → ℝ => (∏ e, Z (r e) (c e)) *
        (∏ e, x (r e)) * standardGaussianTupleMoment c)
        (Measure.pi (fun _ => gaussianReal 0 1)) :=
    ((standardGaussianTuple_integrable r).const_mul _).mul_const _
  change (∫ x : ι → ℝ, ∑ r : κ → ι, ∑ c : κ → ρ,
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
theorem gaussianBilinearMoment_pairing_expansion_finite (Z : Matrix ι ρ ℝ)  :
    gaussianBilinearMoment Z (Fintype.card κ) =
      ∑ P ∈ Finset.univ.filter (fun P : Setoid (κ) => IsPairingPartition P),
        ∑ Q ∈ Finset.univ.filter (fun Q : Setoid (κ) => IsPairingPartition Q),
          rectangularPartitionContraction Z P Q := by
  classical
  rw [gaussianBilinearMoment_coordinate_expansion_finite]
  let w (r : κ → ι) (c : κ → ρ) : ℝ := ∏ e : κ, Z (r e) (c e)
  change (∑ r : κ → ι, ∑ c : κ → ρ,
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
  change (∑ r : κ → ι, ∑ c : κ → ρ,
    w r c * (if P ≤ Setoid.ker r then 1 else 0) * (if Q ≤ Setoid.ker c then 1 else 0)) =
      ∑ r ∈ Finset.univ.filter (fun r : κ → ι => P ≤ Setoid.ker r),
        ∑ c ∈ Finset.univ.filter (fun c : κ → ρ => Q ≤ Setoid.ker c), w r c
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
