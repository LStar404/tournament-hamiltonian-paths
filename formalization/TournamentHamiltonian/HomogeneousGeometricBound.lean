import TournamentHamiltonian.CircularPSDComparison
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators ComplexOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem antidiagonal_exponent_le {n : ℕ} (a : ι → ℕ)
    (ha : a ∈ Finset.piAntidiag (Finset.univ : Finset ι) n) (i : ι) : a i ≤ n := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => Nat.zero_le (a j))
    (Finset.mem_univ i)
  rwa [(Finset.mem_piAntidiag.mp ha).1] at h

noncomputable def homogeneousExponentRestriction (i₀ : ι) (n : ℕ)
    (a : {a : ι → ℕ // a ∈ Finset.piAntidiag (Finset.univ : Finset ι) n}) :
    {i : ι // i ≠ i₀} → Fin (n + 1) :=
  fun i => ⟨a.val i.val, Nat.lt_succ_of_le (antidiagonal_exponent_le a.val a.property i.val)⟩

theorem homogeneousExponentRestriction_injective (i₀ : ι) (n : ℕ) :
    Function.Injective (homogeneousExponentRestriction i₀ n) := by
  intro a b hab
  have hother : ∀ i, i ≠ i₀ → a.val i = b.val i := by
    intro i hi
    exact congrArg Fin.val (congrFun hab ⟨i, hi⟩)
  have hsum : (∑ i ∈ (Finset.univ : Finset ι).erase i₀, a.val i) =
      ∑ i ∈ (Finset.univ : Finset ι).erase i₀, b.val i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hother i (Finset.ne_of_mem_erase hi)
  have ha := (Finset.mem_piAntidiag.mp a.property).1
  have hb := (Finset.mem_piAntidiag.mp b.property).1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀)] at ha hb
  apply Subtype.ext
  funext i
  by_cases hi : i = i₀
  · subst i
    omega
  · exact hother i hi

theorem finite_geometric_sum_le_inverse (x : ℝ) (hx : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    (∑ k : Fin (n + 1), x ^ k.val) ≤ (1 - x)⁻¹ := by
  rw [Fin.sum_univ_eq_sum_range, ← tsum_geometric_of_lt_one hx h1]
  exact (summable_geometric_of_lt_one hx h1).sum_le_tsum _ (fun k _ => pow_nonneg hx k)

theorem spectralHomogeneousPolynomial_le_geometric (d : ι → ℝ) (i₀ : ι)
    (hd : ∀ i, 0 ≤ d i) (h₀ : d i₀ = 1) (h1 : ∀ i, i ≠ i₀ → d i < 1) (n : ℕ) :
    spectralHomogeneousPolynomial d n ≤
      ∏ i : {i : ι // i ≠ i₀}, (1 - d i.val)⁻¹ := by
  let A := {a : ι → ℕ // a ∈ Finset.piAntidiag (Finset.univ : Finset ι) n}
  let J := {i : ι // i ≠ i₀}
  have hterm : ∀ a : A, (∏ i, d i ^ a.val i) =
      ∏ i : J, d i.val ^ (homogeneousExponentRestriction i₀ n a i).val := by
    intro a
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀), h₀, one_pow, one_mul]
    exact Finset.prod_subtype _ (by simp) _
  have hbound : (∑ a : A, ∏ i, d i ^ a.val i) ≤
      ∑ b : J → Fin (n + 1), ∏ i : J, d i.val ^ (b i).val := by
    apply Finset.sum_le_sum_of_injOn (homogeneousExponentRestriction i₀ n)
      (homogeneousExponentRestriction_injective i₀ n).injOn
      (by intro b _; exact Finset.mem_univ b)
    · intro a _
      exact (hterm a).le
    · intro b _ _
      exact Finset.prod_nonneg (fun i _ => pow_nonneg (hd i.val) _)
  have hsum : spectralHomogeneousPolynomial d n = ∑ a : A, ∏ i, d i ^ a.val i := by
    exact Finset.sum_subtype _ (by intro a; rfl) _
  rw [hsum]
  calc
    _ ≤ _ := hbound
    _ = ∏ i : J, ∑ k : Fin (n + 1), d i.val ^ k.val :=
      (Fintype.prod_sum (fun i : J => fun k : Fin (n + 1) => d i.val ^ k.val)).symm
    _ ≤ _ := Finset.prod_le_prod₀
      (fun i _ => Finset.sum_nonneg (fun k _ => pow_nonneg (hd i.val) _))
      (fun i _ => finite_geometric_sum_le_inverse _ (hd i.val) (h1 i.val i.property) n)

/-- The manuscript's PSD bound with one unit eigenvalue and a strict gap on the others. -/
theorem complex_posSemidef_permanent_le_geometric (H : Matrix ι ι ℂ)
    (hH : H.PosSemidef) (i₀ : ι) (h₀ : hH.isHermitian.eigenvalues i₀ = 1)
    (h1 : ∀ i, i ≠ i₀ → hH.isHermitian.eigenvalues i < 1) :
    H.permanent.re ≤ (Fintype.card ι).factorial /
      (Fintype.card ι : ℝ) ^ Fintype.card ι *
        ∏ i : {i : ι // i ≠ i₀}, (1 - hH.isHermitian.eigenvalues i.val)⁻¹ := by
  have hp : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
  exact (complex_posSemidef_permanent_le_homogeneous H hH hp).trans
    (mul_le_mul_of_nonneg_left
      (spectralHomogeneousPolynomial_le_geometric _ i₀ hH.eigenvalues_nonneg h₀ h1 _)
      (by positivity))

end TournamentHamiltonian
