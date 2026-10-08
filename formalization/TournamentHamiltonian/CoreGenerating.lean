import TournamentHamiltonian.PrincipalGenerating
import TournamentHamiltonian.GeneratingDeterminant
import TournamentHamiltonian.CrossPermanentBounds
import TournamentHamiltonian.DegreeDeletion

/-! Actual core generating sums, reindexed without changing any selected minor. -/
namespace TournamentHamiltonian
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem core_principalWeight_generating_det {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) (z : ℝ) :
    ((1 : Matrix U U ℝ) + z • (1 + (adjacency T).submatrix Subtype.val Subtype.val)).det =
      ∑ V ∈ U.powerset, z ^ V.card * (principalWeightMatrix T V).det := by
  rw [matrix_principal_generating_det]
  have hlocal (t : Finset U) :
      z ^ t.card * (((1 : Matrix U U ℝ) + (adjacency T).submatrix Subtype.val Subtype.val).submatrix
        (Subtype.val : t → U) Subtype.val).det =
      z ^ (t.map (Function.Embedding.subtype _)).card *
        (principalWeightMatrix T (t.map (Function.Embedding.subtype _))).det := by
    simp only [Finset.card_map]
    congr 1
    let e := t.equivMap (Function.Embedding.subtype _)
    have heval (i : t) : ((e i : t.map (Function.Embedding.subtype _)) : Fin n) = i.val.val := rfl
    have heq : (principalWeightMatrix T (t.map (Function.Embedding.subtype _))).submatrix e e =
        ((1 : Matrix U U ℝ) + (adjacency T).submatrix Subtype.val Subtype.val).submatrix
          (Subtype.val : t → U) Subtype.val := by
      ext i j
      simp only [principalWeightMatrix, Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply,
        heval, Subtype.ext_iff]
    rw [← heq, Matrix.det_submatrix_equiv_self]
  simp_rw [hlocal]
  exact sum_finsets_subtype_eq_powerset U (fun V => z ^ V.card * (principalWeightMatrix T V).det)

theorem core_principalWeight_generating_eq_induced {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) (z : ℝ) :
    (∑ V ∈ U.powerset, z ^ V.card * (principalWeightMatrix T V).det) =
      ((1 : Matrix (Fin U.card) (Fin U.card) ℝ) + z • (1 + adjacency (inducedTournament T U))).det := by
  rw [← core_principalWeight_generating_det]
  have hmat : ((1 : Matrix U U ℝ) + z • (1 + (adjacency T).submatrix Subtype.val Subtype.val)).submatrix
      (subsetVertexEquiv U) (subsetVertexEquiv U) =
      (1 : Matrix (Fin U.card) (Fin U.card) ℝ) + z • (1 + adjacency (inducedTournament T U)) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      (subsetVertexEquiv U).injective.eq_iff, adjacency_inducedTournament]
  rw [← hmat, Matrix.det_submatrix_equiv_self]

theorem core_principalWeight_generating_le {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) (hn : 0 < n) :
    (∑ V ∈ U.powerset, (2 / (n : ℝ)) ^ V.card * (principalWeightMatrix T V).det) ≤
      2 * Real.exp 1 * ((1 : Matrix (Fin U.card) (Fin U.card) ℝ) +
        (1 / (U.card : ℝ)) • signMatrix (inducedTournament T U)).det := by
  rw [core_principalWeight_generating_eq_induced]
  exact tournament_generating_det_le _ n hn (by simpa using U.card_le_univ)

end TournamentHamiltonian
