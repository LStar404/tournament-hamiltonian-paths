import TournamentHamiltonian.PartitionWeights
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots

/-! Deriving the general partition Möbius weights from counting injective colourings. -/

namespace TournamentHamiltonian

open scoped BigOperators
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq

variable (κ : Type*) [Fintype κ]

/-- The genuine partition-lattice characteristic polynomial. -/
noncomputable def partitionChromaticPolynomial : Polynomial ℤ :=
  ∑ P : Setoid κ, C (IncidenceAlgebra.mu ℤ ⊥ P) * X ^ Fintype.card (Quotient P)

theorem partition_coloring_count (m : ℕ) :
    (∑ P : Setoid κ, IncidenceAlgebra.mu ℤ ⊥ P *
      (m : ℤ) ^ Fintype.card (Quotient P)) =
      (m.descFactorial (Fintype.card κ) : ℤ) := by
  have h := moebius_fiber_bottom (fun r : κ → Fin m => Setoid.ker r) (fun _ => (1 : ℤ))
  have hi : (∑ r ∈ Finset.univ.filter (fun r : κ → Fin m => Setoid.ker r = ⊥), (1 : ℤ)) =
      (m.descFactorial (Fintype.card κ) : ℤ) := by
    simp only [Setoid.ker_eq_bot_iff, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    calc
      _ = Fintype.card {r : κ → Fin m // Function.Injective r} :=
        (Fintype.card_of_subtype _ (by simp)).symm
      _ = Fintype.card (κ ↪ Fin m) :=
        Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding κ (Fin m))
      _ = _ := by rw [Fintype.card_embedding_eq, Fintype.card_fin]
  have hp (P : Setoid κ) :
      (∑ r ∈ Finset.univ.filter (fun r : κ → Fin m => P ≤ Setoid.ker r), (1 : ℤ)) =
        (m : ℤ) ^ Fintype.card (Quotient P) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc : (Finset.univ.filter (fun r : κ → Fin m => P ≤ Setoid.ker r)).card =
        m ^ Fintype.card (Quotient P) := by
      calc
        _ = Fintype.card {r : κ → Fin m // P ≤ Setoid.ker r} :=
          (Fintype.card_of_subtype _ (by simp)).symm
        _ = Fintype.card (Quotient P → Fin m) := Fintype.card_congr (Setoid.liftEquiv P)
        _ = _ := by rw [Fintype.card_fun, Fintype.card_fin]
    rw [hc, Nat.cast_pow]
  simpa only [hi, hp] using h.symm

theorem partitionChromaticPolynomial_eval_nat (m : ℕ) :
    (partitionChromaticPolynomial κ).eval (m : ℤ) =
      (descPochhammer ℤ (Fintype.card κ)).eval (m : ℤ) := by
  simp only [partitionChromaticPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [partition_coloring_count, descPochhammer_eval_eq_descFactorial]

theorem partitionChromaticPolynomial_eq_descPochhammer :
    partitionChromaticPolynomial κ = descPochhammer ℤ (Fintype.card κ) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℤ))).mono
  rintro _ ⟨m, rfl⟩
  exact partitionChromaticPolynomial_eval_nat κ m

theorem quotient_card_one_iff_top [Nonempty κ] (P : Setoid κ) :
    Fintype.card (Quotient P) = 1 ↔ P = ⊤ := by
  constructor
  · intro h
    exact Quotient.subsingleton_iff.mp (Fintype.card_le_one_iff_subsingleton.mp h.le)
  · intro h
    subst P
    have : Subsingleton (Quotient (⊤ : Setoid κ)) := Quotient.subsingleton_iff.mpr rfl
    exact Fintype.card_eq_one_iff.mpr
      ⟨Quotient.mk _ (Classical.arbitrary κ), fun _ => Subsingleton.elim _ _⟩

theorem partitionChromaticPolynomial_coeff_one [Nonempty κ] :
    (partitionChromaticPolynomial κ).coeff 1 = IncidenceAlgebra.mu ℤ (⊥ : Setoid κ) ⊤ := by
  simp only [partitionChromaticPolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  simp [eq_comm, quotient_card_one_iff_top]

theorem descPochhammer_coeff_one_succ (n : ℕ) :
    (descPochhammer ℤ (n + 1)).coeff 1 = (-1 : ℤ) ^ n * (n.factorial : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_right, mul_sub, coeff_sub, coeff_mul_X, coeff_mul_natCast, ih]
    have hzero : (descPochhammer ℤ (n + 1)).coeff 0 = 0 := by
      simpa only [coeff_zero_eq_eval_zero] using
        (descPochhammer_ne_zero_eval_zero ℤ (Nat.succ_ne_zero n))
    rw [hzero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

/-- The nonempty single-block Möbius coefficient, derived from the colouring identity. -/
theorem setoid_mu_top_int [Nonempty κ] :
    IncidenceAlgebra.mu ℤ (⊥ : Setoid κ) ⊤ =
      (-1 : ℤ) ^ (Fintype.card κ - 1) * ((Fintype.card κ - 1).factorial : ℤ) := by
  rw [← partitionChromaticPolynomial_coeff_one, partitionChromaticPolynomial_eq_descPochhammer]
  have hn : 0 < Fintype.card κ := Fintype.card_pos
  obtain ⟨n, hn'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [hn', descPochhammer_coeff_one_succ, Nat.add_one_sub_one]

/-- The empty lattice is a singleton; its Möbius coefficient is one. -/
theorem setoid_mu_top_empty [IsEmpty κ] {R : Type*} [CommRing R] :
    IncidenceAlgebra.mu R (⊥ : Setoid κ) ⊤ = 1 := by
  have hb : (⊥ : Setoid κ) = ⊤ := by
    apply Setoid.ext
    intro i
    exact isEmptyElim i
  rw [hb]
  exact IncidenceAlgebra.mu_self _

/-- The general single-block formula, including the separately checked empty case. -/
theorem setoid_mu_top_factorial {R : Type*} [CommRing R] :
    IncidenceAlgebra.mu R (⊥ : Setoid κ) ⊤ =
      (-1 : R) ^ (Fintype.card κ - 1) * ((Fintype.card κ - 1).factorial : R) := by
  cases isEmpty_or_nonempty κ with
  | inl h => simp [setoid_mu_top_empty, Fintype.card_eq_zero]
  | inr h =>
    rw [mu_bottom_cast, setoid_mu_top_int]
    simp

/-- The full explicit block weights in the manuscript, with no restriction on block sizes. -/
theorem partition_mu_block_weights (P : Setoid κ) {R : Type*} [CommRing R] :
    IncidenceAlgebra.mu R (⊥ : Setoid κ) P =
      ∏ v : Quotient P, (-1 : R) ^ (Fintype.card (PartitionBlock P v) - 1) *
        ((Fintype.card (PartitionBlock P v) - 1).factorial : R) := by
  rw [partition_mu_eq_product_blocks]
  apply Finset.prod_congr rfl
  intro v _
  exact setoid_mu_top_factorial (PartitionBlock P v)

theorem partition_mu_degree_weights (P : Setoid κ) {R : Type*} [CommRing R] :
    IncidenceAlgebra.mu R (⊥ : Setoid κ) P =
      ∏ v : Quotient P, (-1 : R) ^ (coordinatePartitionDegree P v - 1) *
        ((coordinatePartitionDegree P v - 1).factorial : R) := by
  simpa only [partitionBlock_card_eq_degree] using partition_mu_block_weights κ P (R := R)

/-- The factorial weight of a graph's partition vertices. -/
noncomputable def partitionFactorialWeight (R : Type*) [CommRing R] (P : Setoid κ) : R :=
  ∏ v : Quotient P, (-1 : R) ^ (coordinatePartitionDegree P v - 1) *
    ((coordinatePartitionDegree P v - 1).factorial : R)

theorem partitionFactorialWeight_eq_mu {R : Type*} [CommRing R] (P : Setoid κ) :
    partitionFactorialWeight κ R P = IncidenceAlgebra.mu R (⊥ : Setoid κ) P :=
  (partition_mu_degree_weights κ P).symm

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The exact finite distinct-coordinate sum with explicit, proved factorial weights. -/
theorem distinctCoordinateSum_factorial_partition_expansion (B : Matrix ι ι R) (k : ℕ) :
    distinctCoordinateSum B k =
      ∑ P : Setoid (Fin k), ∑ Q : Setoid (Fin k),
        partitionFactorialWeight (Fin k) R P * partitionFactorialWeight (Fin k) R Q *
          partitionContraction B P Q := by
  simp only [partitionFactorialWeight_eq_mu]
  exact distinctCoordinateSum_partition_expansion B k

/-- Row and column centering removes degree-one vertices in the explicit factorial expansion. -/
theorem distinctCoordinateSum_centered_factorial_expansion (B : Matrix ι ι R) (k : ℕ)
    (hrow : ∀ i, (∑ j : ι, B i j) = 0) (hcol : ∀ j, (∑ i : ι, B i j) = 0) :
    distinctCoordinateSum B k =
      ∑ P ∈ Finset.univ.filter (fun P : Setoid (Fin k) => ¬ HasSingletonClass P),
        ∑ Q ∈ Finset.univ.filter (fun Q : Setoid (Fin k) => ¬ HasSingletonClass Q),
          partitionFactorialWeight (Fin k) R P * partitionFactorialWeight (Fin k) R Q *
            partitionContraction B P Q := by
  simp only [partitionFactorialWeight_eq_mu]
  exact distinctCoordinateSum_centered_partition_expansion B k hrow hcol

/-- Explicit graph weights for the actual normalized permanent polynomial coefficient. -/
theorem normalized_coeff_factorial_partition_expansion {K : Type*} [Field K] [CharZero K]
    (E : Matrix ι ι K) (k : ℕ) :
    (((Fintype.card ι).descFactorial k : K) / (Fintype.card ι : K) ^ k) *
        (normalizedPermanentPolynomial E).coeff k =
      (∑ P : Setoid (Fin k), ∑ Q : Setoid (Fin k),
        partitionFactorialWeight (Fin k) K P * partitionFactorialWeight (Fin k) K Q *
          partitionContraction (fun i j => E i j / (Fintype.card ι : K)) P Q) /
        (k.factorial : K) := by
  simp only [partitionFactorialWeight_eq_mu]
  exact normalized_coeff_partition_expansion E k

end TournamentHamiltonian
