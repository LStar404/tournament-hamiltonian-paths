import TournamentHamiltonian.LocalScaling
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator NNReal

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

noncomputable def localExpRemainder (a : ℝ) : ℝ := Real.exp a - 1 - a

theorem local_exp_sub_one_bound (a : ℝ) (ha : |a| ≤ 1) :
    |Real.exp a - 1| ≤ 2 * |a| := by
  have hr := Real.norm_exp_sub_one_sub_id_le (by simpa only [Real.norm_eq_abs] using ha)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs] at hr
  have he : Real.exp a - 1 = (Real.exp a - 1 - a) + a := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hs : a ^ 2 ≤ |a| := by nlinarith [sq_abs a, abs_nonneg a]
  linarith

theorem local_exp_remainder_lipschitz (R a b : ℝ) (_hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 4)
    (ha : |a| ≤ 2 * R) (hb : |b| ≤ 2 * R) :
    |localExpRemainder a - localExpRemainder b| ≤ 4 * R * |a - b| := by
  have hf (x : ℝ) : HasDerivAt localExpRemainder (Real.exp x - 1) x := by
    exact ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)
  have hbound (x : ℝ) (hx : x ∈ Set.Icc (-2 * R) (2 * R)) :
      ‖Real.exp x - 1‖ ≤ 4 * R := by
    have hxabs : |x| ≤ 2 * R := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    rw [Real.norm_eq_abs]
    exact (local_exp_sub_one_bound x (by linarith)).trans (by linarith)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_hx : x ∈ Set.Icc (-2 * R) (2 * R)) => (hf x).hasDerivWithinAt) hbound
    (convex_Icc (-2 * R) (2 * R))
    (x := b) (y := a) (by exact ⟨by linarith [(abs_le.mp hb).1], (abs_le.mp hb).2⟩)
    (by exact ⟨by linarith [(abs_le.mp ha).1], (abs_le.mp ha).2⟩)
  simpa only [Real.norm_eq_abs] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def localMarginalVector (X : Matrix ι ι ℝ) : (ι ⊕ ι) → ℝ :=
  Sum.elim (matrixRowError X) (matrixColumnError X)

noncomputable def localHessian (X : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal (fun i => ∑ j, X i j)) X X.transpose
    (Matrix.diagonal (fun j => ∑ i, X i j))

noncomputable def localNonlinearRemainder (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ) : (ι ⊕ ι) → ℝ :=
  Sum.elim (fun i => ∑ j, X i j * localExpRemainder (z (Sum.inl i) + z (Sum.inr j)))
    (fun j => ∑ i, X i j * localExpRemainder (z (Sum.inl i) + z (Sum.inr j)))

noncomputable def localScaledMatrix (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ) : Matrix ι ι ℝ :=
  fun i j => X i j * Real.exp (z (Sum.inl i) + z (Sum.inr j))

noncomputable def localBalanceVector (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ) : (ι ⊕ ι) → ℝ :=
  Sum.elim (fun i => (∑ j, localScaledMatrix X z i j) - 1)
    (fun j => (∑ i, localScaledMatrix X z i j) - 1)

omit [DecidableEq ι] in
theorem localNonlinearRemainder_zero (X : Matrix ι ι ℝ) :
    localNonlinearRemainder X 0 = 0 := by
  ext i
  rcases i with i | i <;> simp [localNonlinearRemainder, localExpRemainder]

omit [DecidableEq ι] in
theorem localNonlinearRemainder_lipschitz (X : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (R : ℝ) (hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 4)
    (z w : (ι ⊕ ι) → ℝ) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖localNonlinearRemainder X z - localNonlinearRemainder X w‖ ≤ 16 * R * ‖z - w‖ := by
  have hcoord (v : (ι ⊕ ι) → ℝ) (hv : ‖v‖ ≤ R) (k : ι ⊕ ι) : |v k| ≤ R := by
    have h := norm_le_pi_norm v k
    rw [Real.norm_eq_abs] at h
    exact h.trans hv
  have hd (i j : ι) : |localExpRemainder (z (Sum.inl i) + z (Sum.inr j)) -
      localExpRemainder (w (Sum.inl i) + w (Sum.inr j))| ≤ 8 * R * ‖z - w‖ := by
    have ha : |z (Sum.inl i) + z (Sum.inr j)| ≤ 2 * R :=
      (abs_add_le (z (Sum.inl i)) (z (Sum.inr j))).trans
      (by linarith [hcoord z hz (Sum.inl i), hcoord z hz (Sum.inr j)])
    have hb : |w (Sum.inl i) + w (Sum.inr j)| ≤ 2 * R :=
      (abs_add_le (w (Sum.inl i)) (w (Sum.inr j))).trans
      (by linarith [hcoord w hw (Sum.inl i), hcoord w hw (Sum.inr j)])
    have h := local_exp_remainder_lipschitz R _ _ hR0 hR1 ha hb
    have he : z (Sum.inl i) + z (Sum.inr j) - (w (Sum.inl i) + w (Sum.inr j)) =
        (z - w) (Sum.inl i) + (z - w) (Sum.inr j) := by simp; ring
    rw [he] at h
    have hs : |(z - w) (Sum.inl i) + (z - w) (Sum.inr j)| ≤ 2 * ‖z - w‖ := by
      have h1 := norm_le_pi_norm (z - w) (Sum.inl i)
      have h2 := norm_le_pi_norm (z - w) (Sum.inr j)
      rw [Real.norm_eq_abs] at h1 h2
      linarith [abs_add_le ((z - w) (Sum.inl i)) ((z - w) (Sum.inr j))]
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * R by positivity)])
  have hsum (v : ι → ℝ) (f : ι → ℝ) (hv : ∑ k, |v k| ≤ 2)
      (hf : ∀ k, |f k| ≤ 8 * R * ‖z - w‖) : |∑ k, v k * f k| ≤ 16 * R * ‖z - w‖ := by
    calc
      _ ≤ ∑ k, |v k * f k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |v k| * (8 * R * ‖z - w‖) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hf k) (abs_nonneg _)
      _ = (∑ k, |v k|) * (8 * R * ‖z - w‖) := (Finset.sum_mul ..).symm
      _ ≤ 2 * (8 * R * ‖z - w‖) := mul_le_mul_of_nonneg_right hv (by positivity)
      _ = _ := by ring
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  rcases k with i | j
  · simpa only [localNonlinearRemainder, Sum.elim_inl, Pi.sub_apply, Real.norm_eq_abs,
      ← Finset.sum_sub_distrib, ← mul_sub] using hsum (X i) _ (hrow i) (hd i)
  · simpa only [localNonlinearRemainder, Sum.elim_inr, Pi.sub_apply, Real.norm_eq_abs,
      ← Finset.sum_sub_distrib, ← mul_sub] using hsum (fun i => X i j) _ (hcol j) (fun i => hd i j)

theorem localHessian_difference_eq (X : Matrix ι ι ℝ) :
    localHessian X - localBalancedHessian (localCenteredKernel X) =
      Matrix.fromBlocks (Matrix.diagonal (matrixRowError X)) (X - marginalBalancedMatrix X)
        (X - marginalBalancedMatrix X).transpose (Matrix.diagonal (matrixColumnError X)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases hij : i = j
    · subst j
      simp [localHessian, localBalancedHessian, Matrix.fromBlocks, matrixRowError]
    · simp [localHessian, localBalancedHessian, Matrix.fromBlocks, hij]
  · simp only [localHessian, localBalancedHessian, localCenteredKernel,
      Matrix.fromBlocks, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Sum.elim_inl, Sum.elim_inr]
    ring
  · simp only [localHessian, localBalancedHessian, localCenteredKernel,
      Matrix.fromBlocks, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.transpose_apply,
      Sum.elim_inl, Sum.elim_inr]
    have hp : averagingMatrix ι i j = averagingMatrix ι j i := rfl
    rw [hp]
    ring
  · by_cases hij : i = j
    · subst j
      simp [localHessian, localBalancedHessian, Matrix.fromBlocks, matrixColumnError]
    · simp [localHessian, localBalancedHessian, Matrix.fromBlocks, hij]

theorem localHessian_difference_row_bound (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (eps : ℝ) (_heps : 0 ≤ eps) (ha : ∀ i, |matrixRowError X i| ≤ eps)
    (hb : ∀ j, |matrixColumnError X j| ≤ eps) (i : ι ⊕ ι) :
    (∑ j, |(localHessian X - localBalancedHessian (localCenteredKernel X)) i j|) ≤ 3 * eps := by
  have hpR : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hp
  have hentry (i j : ι) : |(X - marginalBalancedMatrix X) i j| ≤ 2 * eps / Fintype.card ι := by
    simp only [Matrix.sub_apply, marginalBalancedMatrix, sub_sub_cancel]
    rw [abs_div, abs_of_pos hpR]
    apply div_le_div_of_nonneg_right _ hpR.le
    linarith [abs_add_le (matrixRowError X i) (matrixColumnError X j), ha i, hb j]
  have hsum (i : ι) : (∑ j, |(X - marginalBalancedMatrix X) i j|) ≤ 2 * eps := by
    calc
      _ ≤ ∑ _j : ι, 2 * eps / Fintype.card ι := Finset.sum_le_sum (fun j _ => hentry i j)
      _ = _ := by simp [mul_div_cancel₀ _ hpR.ne']
  have hsumT (i : ι) : (∑ j, |(X - marginalBalancedMatrix X).transpose i j|) ≤ 2 * eps := by
    calc
      _ ≤ ∑ _j : ι, 2 * eps / Fintype.card ι := Finset.sum_le_sum (fun j _ => hentry j i)
      _ = _ := by simp [mul_div_cancel₀ _ hpR.ne']
  rw [localHessian_difference_eq]
  have hdiag (v : ι → ℝ) (i : ι) : (∑ j, |Matrix.diagonal v i j|) = |v i| := by
    simp [Matrix.diagonal_apply, apply_ite]
  rcases i with i | i <;> simp only [Fintype.sum_sum_type]
  · change (∑ j, |Matrix.diagonal (matrixRowError X) i j|) +
        (∑ j, |(X - marginalBalancedMatrix X) i j|) ≤ _
    rw [hdiag]
    linarith [ha i, hsum i]
  · change (∑ j, |(X - marginalBalancedMatrix X).transpose i j|) +
        (∑ j, |Matrix.diagonal (matrixColumnError X) i j|) ≤ _
    rw [hdiag]
    linarith [hb i, hsumT i]

noncomputable def localScalingMap (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ) : (ι ⊕ ι) → ℝ :=
  -(localBalancedInverse (localCenteredKernel X) *ᵥ
    (localMarginalVector X +
      (localHessian X - localBalancedHessian (localCenteredKernel X)) *ᵥ z +
      localNonlinearRemainder X z))

theorem localScalingMap_lipschitz (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (C q eps R : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1) (heps : 0 ≤ eps)
    (hentry : ∀ i j, |localCenteredKernel X i j| ≤ C / Fintype.card ι)
    (hEq : ‖localCenteredKernel X‖ ≤ q)
    (ha : ∀ i, |matrixRowError X i| ≤ eps) (hb : ∀ j, |matrixColumnError X j| ≤ eps)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 4) (z w : (ι ⊕ ι) → ℝ) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖localScalingMap X z - localScalingMap X w‖ ≤
      localScalingInverseBudget C q * (3 * eps + 16 * R) * ‖z - w‖ := by
  let A := localHessian X - localBalancedHessian (localCenteredKernel X)
  let M := localBalancedInverse (localCenteredKernel X)
  have he : localScalingMap X z - localScalingMap X w =
      -(M *ᵥ (A *ᵥ (z - w) + (localNonlinearRemainder X z - localNonlinearRemainder X w))) := by
    simp only [localScalingMap, M, A, Matrix.mulVec_add, Matrix.mulVec_sub]
    abel
  have hL := localScalingInverseBudget_nonneg C q hC hq1
  have hA := absolute_row_bound_mulVec A (3 * eps) (by positivity)
    (localHessian_difference_row_bound X hp eps heps ha hb) (z - w)
  have hN := localNonlinearRemainder_lipschitz X hrow hcol R hR0 hR1 z w hz hw
  rw [he, norm_neg]
  calc
    _ ≤ localScalingInverseBudget C q *
        ‖A *ᵥ (z - w) + (localNonlinearRemainder X z - localNonlinearRemainder X w)‖ :=
      localBalancedInverse_infinity_control _ hp C q hC hq0 hq1 hentry hEq _
    _ ≤ localScalingInverseBudget C q *
        (‖A *ᵥ (z - w)‖ + ‖localNonlinearRemainder X z - localNonlinearRemainder X w‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hL
    _ ≤ localScalingInverseBudget C q * (3 * eps * ‖z - w‖ + 16 * R * ‖z - w‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hA hN) hL
    _ = _ := by ring

theorem localScalingMap_zero_bound (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (C q eps : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1) (heps : 0 ≤ eps)
    (hentry : ∀ i j, |localCenteredKernel X i j| ≤ C / Fintype.card ι)
    (hEq : ‖localCenteredKernel X‖ ≤ q)
    (ha : ∀ i, |matrixRowError X i| ≤ eps) (hb : ∀ j, |matrixColumnError X j| ≤ eps) :
    ‖localScalingMap X 0‖ ≤ localScalingInverseBudget C q * eps := by
  have hg : ‖localMarginalVector X‖ ≤ eps := by
    apply (pi_norm_le_iff_of_nonneg heps).mpr
    intro i
    rcases i with i | i
    · simpa only [localMarginalVector, Sum.elim_inl, Real.norm_eq_abs] using ha i
    · simpa only [localMarginalVector, Sum.elim_inr, Real.norm_eq_abs] using hb i
  have h := localBalancedInverse_infinity_control (localCenteredKernel X) hp C q hC hq0 hq1 hentry hEq
    (localMarginalVector X)
  simpa only [localScalingMap, localNonlinearRemainder_zero, Matrix.mulVec_zero,
    add_zero, norm_neg] using h.trans (mul_le_mul_of_nonneg_left hg
      (localScalingInverseBudget_nonneg C q hC hq1))

/-- Banach's theorem applied to the actual local marginal equations. -/
theorem exists_local_scaling_fixedPoint (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (C q eps : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1) (heps : 0 ≤ eps)
    (hentry : ∀ i j, |localCenteredKernel X i j| ≤ C / Fintype.card ι)
    (hEq : ‖localCenteredKernel X‖ ≤ q)
    (ha : ∀ i, |matrixRowError X i| ≤ eps) (hb : ∀ j, |matrixColumnError X j| ≤ eps)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (hsmall : eps ≤ 1 / (256 * localScalingInverseBudget C q ^ 2)) :
    ∃ z : (ι ⊕ ι) → ℝ, ‖z‖ ≤ 4 * localScalingInverseBudget C q * eps ∧
      Function.IsFixedPt (localScalingMap X) z := by
  let L := localScalingInverseBudget C q
  let R := 4 * L * eps
  have hL : 3 / 2 ≤ L := by
    dsimp [L, localScalingInverseBudget]
    have h := div_nonneg (sq_nonneg C) (show 0 ≤ 1 - q by linarith)
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hsmall' : eps * (256 * L ^ 2) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 256 * L ^ 2)).mp hsmall
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 / 4 := by
    have h := mul_nonneg (show 0 ≤ L - 3 / 2 by linarith) hR0
    dsimp [R] at *
    nlinarith
  have hcoeff : L * (3 * eps + 16 * R) ≤ 1 / 2 := by
    have h := mul_nonneg (show 0 ≤ L - 3 / 2 by linarith) (mul_nonneg hL0 heps)
    dsimp [R]
    nlinarith
  have hzero : ‖localScalingMap X 0‖ ≤ L * eps :=
    localScalingMap_zero_bound X hp C q eps hC hq0 hq1 heps hentry hEq ha hb
  have hlip (z w : (ι ⊕ ι) → ℝ) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
      ‖localScalingMap X z - localScalingMap X w‖ ≤ (1 / 2 : ℝ) * ‖z - w‖ :=
    (localScalingMap_lipschitz X hp C q eps R hC hq0 hq1 heps hentry hEq ha hb hrow hcol
      hR0 hR1 z w hz hw).trans (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))
  have hmaps : Set.MapsTo (localScalingMap X) (Metric.closedBall 0 R) (Metric.closedBall 0 R) := by
    intro z hz
    have hz' : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have h0 : ‖(0 : (ι ⊕ ι) → ℝ)‖ ≤ R := by simpa using hR0
    have h := hlip z 0 hz' h0
    simp only [sub_zero] at h
    have hnorm : ‖localScalingMap X z‖ ≤ R := by
      calc
        _ = ‖(localScalingMap X z - localScalingMap X 0) + localScalingMap X 0‖ := by congr 1; abel
        _ ≤ ‖localScalingMap X z - localScalingMap X 0‖ + ‖localScalingMap X 0‖ := norm_add_le _ _
        _ ≤ (1 / 2 : ℝ) * ‖z‖ + L * eps := add_le_add h hzero
        _ ≤ R := by dsimp [R] at *; nlinarith
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hc : ContractingWith (1 / 2 : ℝ≥0)
      (hmaps.restrict (localScalingMap X) (Metric.closedBall 0 R) (Metric.closedBall 0 R)) := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro z w
      change dist (localScalingMap X z.val) (localScalingMap X w.val) ≤
        (1 / 2 : ℝ≥0) * dist z.val w.val
      have hz : ‖z.val‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      have hw : ‖w.val‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using w.property
      simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hlip z.val w.val hz hw
  obtain ⟨z, hz, hfix, _⟩ := ContractingWith.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps hc
    (x := 0) (by simpa only [Metric.mem_closedBall, dist_self] using hR0) (edist_ne_top _ _)
  refine ⟨z, ?_, hfix⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz

noncomputable def localGaugeFunctional (z : (ι ⊕ ι) → ℝ) : ℝ :=
  (∑ i, z (Sum.inl i)) - ∑ i, z (Sum.inr i)

omit [DecidableEq ι] in
theorem localGaugeFunctional_add (z w : (ι ⊕ ι) → ℝ) :
    localGaugeFunctional (z + w) = localGaugeFunctional z + localGaugeFunctional w := by
  simp only [localGaugeFunctional, Pi.add_apply, Finset.sum_add_distrib]
  ring

omit [DecidableEq ι] in
theorem localGaugeFunctional_zero : localGaugeFunctional (0 : (ι ⊕ ι) → ℝ) = 0 := by
  simp [localGaugeFunctional]

omit [DecidableEq ι] in
theorem localBalanceVector_gauge_zero (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ) :
    localGaugeFunctional (localBalanceVector X z) = 0 := by
  simp only [localGaugeFunctional, localBalanceVector, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_comm]
  ring

omit [DecidableEq ι] in
theorem averagingMatrix_mulVec (z : ι → ℝ) (i : ι) :
    (averagingMatrix ι *ᵥ z) i = (∑ j, z j) / Fintype.card ι := by
  simp only [averagingMatrix, Matrix.mulVec, dotProduct, Matrix.smul_apply,
    smul_eq_mul, Matrix.of_apply, mul_one]
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_comm]

omit [DecidableEq ι] in
theorem localGaugeCorrection_mulVec (z : (ι ⊕ ι) → ℝ) :
    localGaugeCorrection ι *ᵥ z =
      Sum.elim (fun _ => localGaugeFunctional z / (2 * Fintype.card ι))
        (fun _ => -localGaugeFunctional z / (2 * Fintype.card ι)) := by
  ext i
  rcases i with i | i
  · simp only [localGaugeCorrection, Matrix.fromBlocks_mulVec, Sum.elim_inl,
      Pi.add_apply, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
      averagingMatrix_mulVec, Function.comp_apply, localGaugeFunctional]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [localGaugeCorrection, Matrix.fromBlocks_mulVec, Sum.elim_inr,
      Pi.add_apply, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
      averagingMatrix_mulVec, Function.comp_apply, localGaugeFunctional]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

omit [DecidableEq ι] in
theorem localGaugeCorrection_gauge (hp : 0 < Fintype.card ι) (z : (ι ⊕ ι) → ℝ) :
    localGaugeFunctional (localGaugeCorrection ι *ᵥ z) = localGaugeFunctional z := by
  have hpR : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [localGaugeCorrection_mulVec]
  simp only [localGaugeFunctional, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp [hpR]
  ring

theorem localBalanceVector_eq (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ) :
    localBalanceVector X z = localMarginalVector X + localHessian X *ᵥ z +
      localNonlinearRemainder X z := by
  ext i
  rcases i with i | i
  · simp only [localBalanceVector, localMarginalVector, localHessian, localNonlinearRemainder,
      Matrix.fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply, Matrix.mulVec_diagonal, Function.comp_apply,
      matrixRowError, localExpRemainder, localScaledMatrix]
    simp only [Matrix.mulVec, dotProduct, mul_sub, mul_add, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_mul, mul_one, Function.comp_apply]
    ring
  · simp only [localBalanceVector, localMarginalVector, localHessian, localNonlinearRemainder,
      Matrix.fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply, Matrix.mulVec_diagonal, Function.comp_apply,
      matrixColumnError, localExpRemainder, localScaledMatrix]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_sub, mul_add, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_mul, mul_one, Function.comp_apply]
    ring

theorem localScaling_fixedPoint_balances (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (hmass : matrixEntryMass X = Fintype.card ι) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hEq : ‖localCenteredKernel X‖ ≤ q) (z : (ι ⊕ ι) → ℝ)
    (hfix : Function.IsFixedPt (localScalingMap X) z) :
    localGaugeFunctional z = 0 ∧ localBalanceVector X z = 0 := by
  let E := localCenteredKernel X
  let H := localBalancedHessian E + localGaugeCorrection ι
  let M := localBalancedInverse E
  have hE : DoublyCentered E := localCenteredKernel_doublyCentered X hp hmass
  have hMH : M * H = 1 := localBalancedInverse_mul_hessian E hp hE q hq0 hq1 hEq
  have hHM : H * M = 1 := by
    change H * localBalancedInverse E = 1
    rw [← localBalancedHessian_inverse E hp hE q hq0 hq1 hEq]
    exact Matrix.mul_nonsing_inv H (Matrix.isUnit_det_of_left_inverse hMH)
  have h := congrArg (fun v => H *ᵥ v) hfix.eq
  change H *ᵥ (-(M *ᵥ (localMarginalVector X +
    (localHessian X - localBalancedHessian E) *ᵥ z + localNonlinearRemainder X z))) = H *ᵥ z at h
  rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, hHM, Matrix.one_mulVec] at h
  have hbal : localBalanceVector X z + localGaugeCorrection ι *ᵥ z = 0 := by
    rw [localBalanceVector_eq]
    dsimp only [H, E] at h
    rw [Matrix.add_mulVec, Matrix.sub_mulVec] at h
    linear_combination -h
  have hg := congrArg localGaugeFunctional hbal
  rw [localGaugeFunctional_add, localBalanceVector_gauge_zero, localGaugeCorrection_gauge hp,
    localGaugeFunctional_zero, zero_add] at hg
  refine ⟨hg, ?_⟩
  have hNz : localGaugeCorrection ι *ᵥ z = 0 := by
    rw [localGaugeCorrection_mulVec, hg]
    ext i
    rcases i with i | i <;> simp
  simpa only [hNz, add_zero] using hbal

/-- Actual finite balancing potentials obtained from the density and spectral
gap assumptions, without assuming the existence of a scaling. -/
theorem exists_local_balancing_potentials (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (hmass : matrixEntryMass X = Fintype.card ι)
    (C q eps : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1) (heps : 0 ≤ eps)
    (hentry : ∀ i j, |localCenteredKernel X i j| ≤ C / Fintype.card ι)
    (hEq : ‖localCenteredKernel X‖ ≤ q)
    (ha : ∀ i, |matrixRowError X i| ≤ eps) (hb : ∀ j, |matrixColumnError X j| ≤ eps)
    (hrow : ∀ i, ∑ j, |X i j| ≤ 2) (hcol : ∀ j, ∑ i, |X i j| ≤ 2)
    (hsmall : eps ≤ 1 / (256 * localScalingInverseBudget C q ^ 2)) :
    ∃ z : (ι ⊕ ι) → ℝ, ‖z‖ ≤ 4 * localScalingInverseBudget C q * eps ∧
      (∑ i, z (Sum.inl i)) = (∑ i, z (Sum.inr i)) ∧
      (∀ i, ∑ j, localScaledMatrix X z i j = 1) ∧
      (∀ j, ∑ i, localScaledMatrix X z i j = 1) := by
  obtain ⟨z, hz, hfix⟩ := exists_local_scaling_fixedPoint X hp C q eps hC hq0 hq1 heps
    hentry hEq ha hb hrow hcol hsmall
  have hbal := localScaling_fixedPoint_balances X hp hmass q hq0 hq1 hEq z hfix
  refine ⟨z, hz, sub_eq_zero.mp hbal.1, ?_, ?_⟩
  · intro i
    have h := congrFun hbal.2 (Sum.inl i)
    change (∑ j, localScaledMatrix X z i j) - 1 = 0 at h
    linarith
  · intro j
    have h := congrFun hbal.2 (Sum.inr j)
    change (∑ i, localScaledMatrix X z i j) - 1 = 0 at h
    linarith

omit [Fintype ι] [DecidableEq ι] in
theorem localScaledMatrix_eq_exp_scaling (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ) :
    localScaledMatrix X z = fun i j => Real.exp (z (Sum.inl i)) * X i j * Real.exp (z (Sum.inr j)) := by
  ext i j
  rw [localScaledMatrix, Real.exp_add]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem localScaledMatrix_nonnegative (X : Matrix ι ι ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (z : (ι ⊕ ι) → ℝ) (i j : ι) : 0 ≤ localScaledMatrix X z i j :=
  mul_nonneg (hX i j) (Real.exp_pos _).le

omit [Fintype ι] [DecidableEq ι] in
theorem localScaledMatrix_zero_support (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ) (i j : ι) :
    localScaledMatrix X z i j = 0 ↔ X i j = 0 := by
  simp only [localScaledMatrix, mul_eq_zero, (Real.exp_pos _).ne', or_false]

end TournamentHamiltonian
