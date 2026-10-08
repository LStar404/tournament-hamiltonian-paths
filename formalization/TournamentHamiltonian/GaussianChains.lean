import TournamentHamiltonian.GaussianCoreGraph
import Mathlib.Analysis.SpecificLimits.Normed

/-! Actual alternating matrix-chain contractions and their summed activity majorant. -/

namespace TournamentHamiltonian

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def orientedChainFactor (B : Matrix ι ι ℝ) (s : Bool) : Matrix ι ι ℝ :=
  if s then B.transpose else B

def chainEndpointOrientation : ℕ → Bool → Bool
  | 0, s => s
  | k + 1, s => chainEndpointOrientation k (!s)

/-- Matrix multiplication sums all internal numerical labels of the alternating chain. -/
noncomputable def alternatingChain (B : Matrix ι ι ℝ) : ℕ → Bool → Matrix ι ι ℝ
  | 0, _ => 1
  | k + 1, s => orientedChainFactor B s * alternatingChain B k (!s)

theorem alternatingChain_succ_right (B : Matrix ι ι ℝ) (k : ℕ) (s : Bool) :
    alternatingChain B (k + 1) s = alternatingChain B k s *
      orientedChainFactor B (chainEndpointOrientation k s) := by
  induction k generalizing s with
  | zero => simp [alternatingChain, chainEndpointOrientation]
  | succ k ih =>
    change orientedChainFactor B s * alternatingChain B (k + 1) (!s) =
      (orientedChainFactor B s * alternatingChain B k (!s)) *
        orientedChainFactor B (chainEndpointOrientation k (!s))
    rw [ih, Matrix.mul_assoc]

theorem alternatingChain_peel_endpoints (B : Matrix ι ι ℝ) (k : ℕ) (s : Bool) :
    alternatingChain B (k + 2) s = orientedChainFactor B s *
      alternatingChain B k (!s) * orientedChainFactor B (chainEndpointOrientation (k + 1) s) := by
  change orientedChainFactor B s * alternatingChain B (k + 1) (!s) = _
  rw [alternatingChain_succ_right, ← Matrix.mul_assoc]
  rfl

theorem orientedChainFactor_norm (B : Matrix ι ι ℝ) (s : Bool) :
    ‖orientedChainFactor B s‖ = ‖B‖ := by
  cases s
  · rfl
  · simpa only [orientedChainFactor, Bool.true_eq_false, ite_true,
      Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose B

private theorem matrix_one_opNorm_le : ‖(1 : Matrix ι ι ℝ)‖ ≤ 1 := by
  rw [show (1 : Matrix ι ι ℝ) = Matrix.diagonal (fun _ : ι => (1 : ℝ)) by
    ext i j; simp [Matrix.one_apply, Matrix.diagonal], Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun _ => by simp)

theorem alternatingChain_opNorm_le (B : Matrix ι ι ℝ) (q : ℝ) (hq : ‖B‖ ≤ q)
    (k : ℕ) (s : Bool) : ‖alternatingChain B k s‖ ≤ q ^ k := by
  have hq0 : 0 ≤ q := (norm_nonneg B).trans hq
  induction k generalizing s with
  | zero => simpa [alternatingChain] using (matrix_one_opNorm_le (ι := ι))
  | succ k ih =>
    rw [alternatingChain]
    calc
      _ ≤ ‖orientedChainFactor B s‖ * ‖alternatingChain B k (!s)‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ q * q ^ k := mul_le_mul (by rwa [orientedChainFactor_norm]) (ih _)
        (norm_nonneg _) hq0
      _ = q ^ (k + 1) := by ring

omit [DecidableEq ι] in
theorem matrix_sandwich_entry_eq_bilinear (A M D : Matrix ι ι ℝ) (i j : ι) :
    (A * M * D) i j = gaussianBilinearVariable M (A i, fun a => D a j) := by
  simp only [Matrix.mul_apply, gaussianBilinearVariable, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem matrix_sandwich_entry_abs_le (A M D : Matrix ι ι ℝ) (i j : ι) :
    |(A * M * D) i j| ≤
      ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ ι)‖ * ‖M‖ *
        ‖(WithLp.toLp 2 (fun a => D a j) : EuclideanSpace ℝ ι)‖ := by
  rw [matrix_sandwich_entry_eq_bilinear]
  exact gaussianBilinearVariable_abs_le M _

omit [DecidableEq ι] in
theorem bounded_entries_euclideanNorm_le (x : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hn : 0 < Fintype.card ι) (hx : ∀ i, |x i| ≤ C / (Fintype.card ι : ℝ)) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ≤ C / Real.sqrt (Fintype.card ι : ℝ) := by
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg hC (Real.sqrt_nonneg _))).mp
  rw [EuclideanSpace.norm_sq_eq]
  have hs : (∑ i, ‖x i‖ ^ 2) ≤ (Fintype.card ι : ℝ) * (C / (Fintype.card ι : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ _i : ι, (C / (Fintype.card ι : ℝ)) ^ 2 :=
        Finset.sum_le_sum (fun i _ =>
          (sq_le_sq₀ (norm_nonneg _) (div_nonneg hC hnpos.le)).mpr (by simpa using hx i))
      _ = _ := by simp
  calc
    _ ≤ _ := hs
    _ = (C / Real.sqrt (Fintype.card ι : ℝ)) ^ 2 := by
      simp only [div_pow, Real.sq_sqrt hnpos.le]
      field_simp

theorem alternatingChain_entry_abs_le (B : Matrix ι ι ℝ) (C q : ℝ)
    (hC : 0 ≤ C) (hn : 0 < Fintype.card ι)
    (hB : ∀ i j, |B i j| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (k : ℕ) (s : Bool) (i j : ι) :
    |alternatingChain B (k + 2) s i j| ≤
      C ^ 2 / (Fintype.card ι : ℝ) * q ^ k := by
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hq0 : 0 ≤ q := (norm_nonneg B).trans hq
  have hf : ∀ s i j, |orientedChainFactor B s i j| ≤ C / (Fintype.card ι : ℝ) := by
    intro s i j
    cases s
    · simpa [orientedChainFactor] using hB i j
    · simpa [orientedChainFactor] using hB j i
  rw [alternatingChain_peel_endpoints]
  calc
    _ ≤ _ := matrix_sandwich_entry_abs_le _ _ _ i j
    _ ≤ (C / Real.sqrt (Fintype.card ι : ℝ)) * q ^ k *
        (C / Real.sqrt (Fintype.card ι : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul
          (bounded_entries_euclideanNorm_le _ C hC hn (fun a => hf s i a))
          (alternatingChain_opNorm_le B q hq k (!s)) (norm_nonneg _)
          (div_nonneg hC (Real.sqrt_nonneg _))
      · exact bounded_entries_euclideanNorm_le _ C hC hn (fun a => hf _ a j)
      · exact norm_nonneg _
      · positivity
    _ = _ := by
      have hs : (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = (Fintype.card ι : ℝ) :=
        Real.sq_sqrt hnpos.le
      field_simp
      rw [hs]
      ring

private theorem alternatingChain_weighted_tail_le (B : Matrix ι ι ℝ) (C q R : ℝ)
    (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i j, |B i j| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (k : ℕ) (s : Bool) (i j : ι) :
    |alternatingChain B (k + 2) s i j| * R ^ (k + 2) ≤
      (C ^ 2 * R ^ 2 / (Fintype.card ι : ℝ)) * (R * q) ^ k := by
  calc
    _ ≤ (C ^ 2 / (Fintype.card ι : ℝ) * q ^ k) * R ^ (k + 2) :=
      mul_le_mul_of_nonneg_right (alternatingChain_entry_abs_le B C q hC hn hB hq k s i j)
        (pow_nonneg hR _)
    _ = _ := by rw [pow_add, mul_pow]; ring

theorem alternatingChain_weighted_summable (B : Matrix ι ι ℝ) (C q R : ℝ)
    (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i j, |B i j| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (hgap : R * q < 1) (s : Bool) (i j : ι) :
    Summable (fun k => |alternatingChain B (k + 1) s i j| * R ^ (k + 1)) := by
  have hq0 : 0 ≤ q := (norm_nonneg B).trans hq
  have hg := (hasSum_geometric_of_lt_one (mul_nonneg hR hq0) hgap).summable.mul_left
    (C ^ 2 * R ^ 2 / (Fintype.card ι : ℝ))
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (abs_nonneg _) (pow_nonneg hR _)) _ hg
  intro k
  exact alternatingChain_weighted_tail_le B C q R hC hn hR hB hq k s i j

/-- Summing all positive chain lengths gives the precise manuscript chain majorant. -/
theorem alternatingChain_weighted_tsum_le (B : Matrix ι ι ℝ) (C q R : ℝ)
    (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i j, |B i j| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (hgap : R * q < 1) (s : Bool) (i j : ι) :
    (∑' k, |alternatingChain B (k + 1) s i j| * R ^ (k + 1)) ≤
      (C * R + C ^ 2 * R ^ 2 / (1 - R * q)) / (Fintype.card ι : ℝ) := by
  have hq0 : 0 ≤ q := (norm_nonneg B).trans hq
  have hs := alternatingChain_weighted_summable B C q R hC hn hR hB hq hgap s i j
  have ht := (summable_nat_add_iff 1).mpr hs
  have hg := (hasSum_geometric_of_lt_one (mul_nonneg hR hq0) hgap).mul_left
    (C ^ 2 * R ^ 2 / (Fintype.card ι : ℝ))
  have htail := Summable.tsum_le_tsum (fun k =>
    alternatingChain_weighted_tail_le B C q R hC hn hR hB hq k s i j) ht hg.summable
  have hfirst : |alternatingChain B 1 s i j| * R ≤ C / (Fintype.card ι : ℝ) * R := by
    apply mul_le_mul_of_nonneg_right _ hR
    cases s
    · simpa [alternatingChain, orientedChainFactor] using hB i j
    · simpa [alternatingChain, orientedChainFactor] using hB j i
  rw [← hs.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, zero_add, pow_one]
  calc
    _ ≤ C / (Fintype.card ι : ℝ) * R +
        (C ^ 2 * R ^ 2 / (Fintype.card ι : ℝ)) * (1 - R * q)⁻¹ := by
      rw [hg.tsum_eq] at htail
      exact add_le_add hfirst htail
    _ = _ := by ring

end TournamentHamiltonian
