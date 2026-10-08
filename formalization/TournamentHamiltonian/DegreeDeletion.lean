import TournamentHamiltonian.StirlingNormalization
import TournamentHamiltonian.PathConvolutionCoefficients

/-! Actual induced tournaments and quantitative variance under deletions. -/

namespace TournamentHamiltonian

open scoped Classical

noncomputable def subsetVertexEquiv {n : ℕ} (U : Finset (Fin n)) : Fin U.card ≃ U :=
  (U.orderIsoOfFin rfl).toEquiv

noncomputable def inducedTournament {n : ℕ} (T : Tournament n) (U : Finset (Fin n)) :
    Tournament U.card :=
  ⟨fun i j => T.val (subsetVertexEquiv U i) (subsetVertexEquiv U j), by
    constructor
    · intro i
      exact T.property.1 _
    · intro i j hij
      exact T.property.2 _ _ (fun h => hij ((subsetVertexEquiv U).injective (Subtype.ext h)))⟩

theorem adjacency_inducedTournament {n : ℕ} (T : Tournament n) (U : Finset (Fin n)) :
    adjacency (inducedTournament T U) =
      ((adjacency T).submatrix Subtype.val Subtype.val).submatrix
        (subsetVertexEquiv U) (subsetVertexEquiv U) := rfl

theorem adjacency_principal_permanent_eq_induced {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) :
    ((adjacency T).submatrix (Subtype.val : U → Fin n) Subtype.val).permanent =
      (adjacency (inducedTournament T U)).permanent := by
  rw [adjacency_inducedTournament]
  exact (permanent_submatrix_equiv_self _ (subsetVertexEquiv U)).symm

theorem adjacency_principal_permanent_le_stirling {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) :
    ((adjacency T).submatrix (Subtype.val : U → Fin n) Subtype.val).permanent ≤
      Real.exp 7 * Real.sqrt ((U.card : ℝ) + 1) * (U.card.factorial : ℝ) / (2 : ℝ) ^ U.card := by
  rw [adjacency_principal_permanent_eq_induced]
  exact adjacency_permanent_le_stirling_all (inducedTournament T U)

noncomputable def subsetScore {n : ℕ} (T : Tournament n) (U : Finset (Fin n))
    (i : Fin n) : ℝ := ∑ j ∈ U, signMatrix T i j

theorem signMatrix_abs_le_one {n : ℕ} (T : Tournament n) (i j : Fin n) :
    |signMatrix T i j| ≤ 1 := by
  by_cases h : i = j
  · simp [signMatrix, h]
  · cases he : T.val i j <;> norm_num [signMatrix, h, he]

theorem subsetScore_abs_le_card {n : ℕ} (T : Tournament n) (U : Finset (Fin n))
    (i : Fin n) : |subsetScore T U i| ≤ U.card := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    simpa using Finset.sum_le_sum (s := U) (fun j _ => signMatrix_abs_le_one T i j))

theorem score_abs_le_order {n : ℕ} (T : Tournament n) (i : Fin n) :
    |score T i| ≤ n := by
  simpa [subsetScore, score] using subsetScore_abs_le_card T Finset.univ i

theorem subsetScore_add_compl {n : ℕ} (T : Tournament n) (U : Finset (Fin n))
    (i : Fin n) : subsetScore T U i + subsetScore T Uᶜ i = score T i := by
  exact Finset.sum_add_sum_compl U (fun j => signMatrix T i j)

theorem subsetScore_sub_score_abs_le {n : ℕ} (T : Tournament n) (U : Finset (Fin n))
    (i : Fin n) : |subsetScore T U i - score T i| ≤ Uᶜ.card := by
  have he : subsetScore T U i - score T i = -subsetScore T Uᶜ i := by
    linarith [subsetScore_add_compl T U i]
  rw [he, abs_neg]
  exact subsetScore_abs_le_card T Uᶜ i

theorem signMatrix_inducedTournament {n : ℕ} (T : Tournament n) (U : Finset (Fin n))
    (i j : Fin U.card) :
    signMatrix (inducedTournament T U) i j =
      signMatrix T (subsetVertexEquiv U i) (subsetVertexEquiv U j) := by
  have he : (i = j) ↔ ((subsetVertexEquiv U i : Fin n) = subsetVertexEquiv U j) := by
    constructor
    · rintro rfl; rfl
    · exact fun h => (subsetVertexEquiv U).injective (Subtype.ext h)
  simp only [signMatrix, inducedTournament, he]
  rfl

theorem score_inducedTournament {n : ℕ} (T : Tournament n) (U : Finset (Fin n))
    (i : Fin U.card) :
    score (inducedTournament T U) i = subsetScore T U (subsetVertexEquiv U i) := by
  simp only [score, signMatrix_inducedTournament]
  rw [(subsetVertexEquiv U).sum_comp (fun j : U => signMatrix T (subsetVertexEquiv U i) j)]
  exact U.sum_coe_sort _

theorem degreeVariance_inducedTournament_eq {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) :
    degreeVariance (inducedTournament T U) = (∑ i ∈ U, subsetScore T U i ^ 2) / 4 := by
  rw [degreeVariance_eq_score_sum]
  simp only [score_inducedTournament]
  rw [(subsetVertexEquiv U).sum_comp (fun i : U => subsetScore T U i ^ 2)]
  exact congrArg (fun x : ℝ => x / 4) (U.sum_coe_sort (fun i => subsetScore T U i ^ 2))

/-- A fixed Young inequality gives a useful variance retention bound without
regularity assumptions. The lost terms are controlled by the actual deleted
vertices and their score changes. -/
theorem degreeVariance_inducedTournament_ge {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) :
    (7 / 8 : ℝ) * degreeVariance T - (Uᶜ.card : ℝ) * (n : ℝ) ^ 2 / 4 -
      2 * (n : ℝ) * (Uᶜ.card : ℝ) ^ 2 ≤ degreeVariance (inducedTournament T U) := by
  let k : ℝ := Uᶜ.card
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hlocal (i : Fin n) : (7 / 8 : ℝ) * score T i ^ 2 - 7 * k ^ 2 ≤ subsetScore T U i ^ 2 := by
    have hd := subsetScore_sub_score_abs_le T U i
    change |subsetScore T U i - score T i| ≤ k at hd
    have hs : (subsetScore T U i - score T i) ^ 2 ≤ k ^ 2 := by
      have hs := (sq_le_sq₀ (abs_nonneg (subsetScore T U i - score T i)) hk).mpr hd
      simpa only [sq_abs] using hs
    nlinarith [sq_nonneg (subsetScore T U i - 7 * (score T i - subsetScore T U i))]
  have hs := Finset.sum_le_sum (s := U) (fun i _ => hlocal i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at hs
  have hremoved : (∑ i ∈ Uᶜ, score T i ^ 2) ≤ k * (n : ℝ) ^ 2 := by
    have h := Finset.sum_le_sum (s := Uᶜ) (fun i _ =>
      (sq_le_sq₀ (abs_nonneg _) (by positivity : (0 : ℝ) ≤ n)).mpr (score_abs_le_order T i))
    simpa [k] using h
  have hsplit : (∑ i ∈ U, score T i ^ 2) + (∑ i ∈ Uᶜ, score T i ^ 2) =
      ∑ i, score T i ^ 2 := Finset.sum_add_sum_compl U _
  have hcard : (U.card : ℝ) ≤ n := by
    exact_mod_cast (show U.card ≤ n by simpa using U.card_le_univ)
  have hcardmul := mul_le_mul_of_nonneg_right hcard (sq_nonneg k)
  rw [degreeVariance_inducedTournament_eq, degreeVariance_eq_score_sum]
  change (7 / 8 : ℝ) * ((∑ i, score T i ^ 2) / 4) - k * (n : ℝ) ^ 2 / 4 -
    2 * (n : ℝ) * k ^ 2 ≤ (∑ i ∈ U, subsetScore T U i ^ 2) / 4
  nlinarith [mul_nonneg hk (sq_nonneg (n : ℝ))]

theorem adjacency_principal_permanent_le_stirling_retained_variance {n : ℕ}
    (T : Tournament n) (U : Finset (Fin n)) (hU : 3 ≤ U.card) :
    ((adjacency T).submatrix (Subtype.val : U → Fin n) Subtype.val).permanent ≤
      Real.exp 7 * Real.sqrt ((U.card : ℝ) + 1) * (U.card.factorial : ℝ) / (2 : ℝ) ^ U.card *
        Real.exp (-((7 / 8 : ℝ) * degreeVariance T - (Uᶜ.card : ℝ) * (n : ℝ) ^ 2 / 4 -
          2 * (n : ℝ) * (Uᶜ.card : ℝ) ^ 2) / (8 * (U.card : ℝ) ^ 2)) := by
  rw [adjacency_principal_permanent_eq_induced]
  apply (adjacency_permanent_le_stirling_variance (inducedTournament T U) hU).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (neg_le_neg (degreeVariance_inducedTournament_ge T U))
    (by positivity)

end TournamentHamiltonian
