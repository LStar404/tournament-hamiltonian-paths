import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

open scoped BigOperators

namespace TournamentHamiltonian

theorem root_phase_power_conj_cancel {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (a : ℕ) :
    ζ ^ a * star (ζ ^ a) = 1 := by
  change ζ ^ a * (starRingEnd ℂ) (ζ ^ a) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow,
    hζ.norm'_eq_one hN, one_pow, one_pow, Complex.ofReal_one]

theorem root_phase_cross_sum {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (a b : ℕ)
    (ha : a < N) (hb : b < N) :
    (∑ j : Fin N, (ζ ^ j.val) ^ a * star ((ζ ^ j.val) ^ b)) =
      if a = b then (N : ℂ) else 0 := by
  have hpower : ∀ j : ℕ, (ζ ^ j) ^ a * star ((ζ ^ j) ^ b) =
      (ζ ^ a * star (ζ ^ b)) ^ j := by
    intro j
    simp only [mul_pow, star_pow, ← pow_mul, Nat.mul_comm j]
  simp_rw [hpower]
  by_cases hab : a = b
  · subst b
    rw [root_phase_power_conj_cancel hζ hN]
    simp
  · simp only [hab, ite_false]
    have hneq : ζ ^ a * star (ζ ^ b) ≠ 1 := by
      intro he
      have h := congrArg (fun x : ℂ => x * ζ ^ b) he
      have hcancel : star (ζ ^ b) * ζ ^ b = 1 := by
        simpa only [mul_comm] using root_phase_power_conj_cancel hζ hN b
      rw [mul_assoc, hcancel, mul_one, one_mul] at h
      exact hab (hζ.pow_inj ha hb h)
    have hNpow : (ζ ^ a * star (ζ ^ b)) ^ N = 1 := by
      have hstar : star ζ ^ N = 1 := by
        simpa only [star_pow, star_one] using congrArg star hζ.pow_eq_one
      simp only [mul_pow, star_pow, ← pow_mul]
      rw [Nat.mul_comm a N, Nat.mul_comm b N, pow_mul, pow_mul,
        hζ.pow_eq_one, hstar, one_pow, one_pow, mul_one]
    rw [Fin.sum_univ_eq_sum_range]
    have h := geom_sum_mul (ζ ^ a * star (ζ ^ b)) N
    rw [hNpow, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hneq)

end TournamentHamiltonian
