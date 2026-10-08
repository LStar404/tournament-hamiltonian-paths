import TournamentHamiltonian.AmbientCoreWeights
import TournamentHamiltonian.SelectedMinorEmbeddings
import TournamentHamiltonian.RectangularPermanentBridge
import TournamentHamiltonian.NonprincipalScaling

/-! Exact reindexing of actual ambient core minors and their paired weight products. -/
namespace TournamentHamiltonian
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def coreVertexEmbedding {n : ℕ} (M : Finset (Fin n)) : Fin M.card ↪ Fin n :=
  (subsetVertexEquiv M).toEmbedding.trans (Function.Embedding.subtype (fun x => x ∈ M))

noncomputable def coreIndexSet {n : ℕ} (M I : Finset (Fin n)) : Finset (Fin M.card) :=
  (I.subtype (fun x => x ∈ M)).map (subsetVertexEquiv M).symm.toEmbedding

theorem coreVertexEmbedding_apply {n : ℕ} (M : Finset (Fin n)) (i : Fin M.card) :
    coreVertexEmbedding M i = subsetVertexEquiv M i := rfl

theorem coreIndexSet_map {n : ℕ} (M I : Finset (Fin n)) (hI : I ⊆ M) :
    (coreIndexSet M I).map (coreVertexEmbedding M) = I := by
  rw [coreIndexSet, Finset.map_map]
  have he : (subsetVertexEquiv M).symm.toEmbedding.trans (coreVertexEmbedding M) =
      Function.Embedding.subtype (fun x => x ∈ M) := by
    ext x
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      coreVertexEmbedding_apply, Equiv.apply_symm_apply, Function.Embedding.subtype_apply]
  rw [he, Finset.subtype_map_of_mem hI]

theorem coreIndexSet_card {n : ℕ} (M I : Finset (Fin n)) (hI : I ⊆ M) :
    (coreIndexSet M I).card = I.card := by
  have h := congrArg Finset.card (coreIndexSet_map M I hI)
  simpa only [Finset.card_map] using h

theorem coreVertexEmbedding_univ_map {n : ℕ} (M : Finset (Fin n)) :
    (Finset.univ : Finset (Fin M.card)).map (coreVertexEmbedding M) = M := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact (subsetVertexEquiv M i).property
  · intro hx
    apply Finset.mem_map.mpr
    refine ⟨(subsetVertexEquiv M).symm ⟨x, hx⟩, Finset.mem_univ _, ?_⟩
    simp only [coreVertexEmbedding_apply, Equiv.apply_symm_apply]

theorem coreIndexSet_compl_map {n : ℕ} (M I : Finset (Fin n)) (hI : I ⊆ M) :
    (coreIndexSet M I)ᶜ.map (coreVertexEmbedding M) = M \ I := by
  rw [Finset.compl_eq_univ_sdiff, Finset.map_sdiff,
    coreVertexEmbedding_univ_map, coreIndexSet_map M I hI]

theorem selectedPermanent_core_reindex {n : ℕ} (T : Tournament n) (M I J : Finset (Fin n))
    (hI : I ⊆ M) (hJ : J ⊆ M) :
    selectedPermanent (adjacency T) (M \ J) (M \ I) =
      selectedPermanent (adjacency (inducedTournament T M))
        (coreIndexSet M J)ᶜ (coreIndexSet M I)ᶜ := by
  have h := selectedPermanent_submatrix_embedding (adjacency T) (coreVertexEmbedding M)
    (coreIndexSet M J)ᶜ (coreIndexSet M I)ᶜ
  rw [coreIndexSet_compl_map M I hI, coreIndexSet_compl_map M J hJ] at h
  exact h.symm

theorem coreIndexSet_potential_prod {n : ℕ} (T : Tournament n) (M I : Finset (Fin n))
    (hI : I ⊆ M) (f : ℝ → ℝ) :
    (∏ i ∈ coreIndexSet M I, f (tournamentScorePotential (inducedTournament T M) i)) =
      ∏ x ∈ I, f (ambientCorePotential T M x) := by
  have h := Finset.prod_map (coreIndexSet M I) (coreVertexEmbedding M)
    (fun x => f (ambientCorePotential T M x))
  rw [coreIndexSet_map M I hI] at h
  simp_rw [coreVertexEmbedding_apply, ambientCorePotential_equiv] at h
  exact h.symm

theorem coreIndexSet_left_prod {n : ℕ} (T : Tournament n) (M I : Finset (Fin n)) (hI : I ⊆ M) :
    (∏ i ∈ coreIndexSet M I, pairedLeft (tournamentScorePotential (inducedTournament T M) i)) =
      ∏ x ∈ I, ambientCoreLeft T M x := coreIndexSet_potential_prod T M I hI pairedLeft

theorem coreIndexSet_right_prod {n : ℕ} (T : Tournament n) (M I : Finset (Fin n)) (hI : I ⊆ M) :
    (∏ i ∈ coreIndexSet M I, pairedRight (tournamentScorePotential (inducedTournament T M) i)) =
      ∏ x ∈ I, ambientCoreRight T M x := coreIndexSet_potential_prod T M I hI pairedRight

theorem selectedPermanent_core_rectangular_reindex {n : ℕ} (T : Tournament n)
    (M I J : Finset (Fin n)) (hI : I ⊆ M) (hJ : J ⊆ M)
    (e : ((coreIndexSet M I)ᶜ : Finset (Fin M.card)) ≃
      ((coreIndexSet M J)ᶜ : Finset (Fin M.card))) :
    selectedPermanent (adjacency T) (M \ J) (M \ I) =
      rectangularPermanent (nonprincipalSubmatrix (adjacency (inducedTournament T M))
        (coreIndexSet M I) (coreIndexSet M J)) e := by
  rw [selectedPermanent_core_reindex T M I J hI hJ]
  exact selectedPermanent_eq_rectangularPermanent _ _ _ e

theorem ambient_core_minor_bound_of_rectangular {n : ℕ} (T : Tournament n)
    (M : Finset (Fin n)) (t : ℕ) (B : ℝ)
    (hper : ∀ I J : Finset (Fin M.card), ∀ hI : I.card = t, ∀ hJ : J.card = t,
      let e := deletedComplementEquiv I J (hI.trans hJ.symm)
      rectangularPermanent (nonprincipalSubmatrix (adjacency (inducedTournament T M)) I J) e ≤
        (B * (((M.card - t).factorial : ℝ) / (2 : ℝ) ^ (M.card - t))) *
          (∏ i ∈ I, pairedLeft (tournamentScorePotential (inducedTournament T M) i)) *
          (∏ j ∈ J, pairedRight (tournamentScorePotential (inducedTournament T M) j))) :
    ∀ I ∈ M.powersetCard t, ∀ J ∈ M.powersetCard t,
      selectedPermanent (adjacency T) (M \ J) (M \ I) ≤
        (B * (((M.card - t).factorial : ℝ) / (2 : ℝ) ^ (M.card - t))) *
          (∏ i ∈ I, ambientCoreLeft T M i) * (∏ j ∈ J, ambientCoreRight T M j) := by
  intro I hI J hJ
  obtain ⟨hIM, hIt⟩ := Finset.mem_powersetCard.mp hI
  obtain ⟨hJM, hJt⟩ := Finset.mem_powersetCard.mp hJ
  have hIc : (coreIndexSet M I).card = t := (coreIndexSet_card M I hIM).trans hIt
  have hJc : (coreIndexSet M J).card = t := (coreIndexSet_card M J hJM).trans hJt
  let e := deletedComplementEquiv (coreIndexSet M I) (coreIndexSet M J) (hIc.trans hJc.symm)
  rw [selectedPermanent_core_rectangular_reindex T M I J hIM hJM e]
  have hp := hper (coreIndexSet M I) (coreIndexSet M J) hIc hJc
  rw [coreIndexSet_left_prod T M I hIM, coreIndexSet_right_prod T M J hJM] at hp
  exact hp

end TournamentHamiltonian
