import TournamentHamiltonian.CrossPermanentBounds

/-! Selected actual minors under embeddings and ambient subset reindexing. -/
namespace TournamentHamiltonian
open scoped Classical
variable {α β R : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [CommSemiring R]

omit [Fintype α] [Fintype β] in
theorem selectedPermanent_submatrix_embedding (A : Matrix α α R) (e : β ↪ α)
    (s t : Finset β) :
    selectedPermanent (A.submatrix e e) s t = selectedPermanent A (s.map e) (t.map e) := by
  change bijectionPermanent (fun (i : t) (j : s) => A (e i) (e j)) =
    bijectionPermanent (fun (i : t.map e) (j : s.map e) => A i j)
  exact rectangularPermanent_submatrix_equiv (fun (i : t.map e) (j : s.map e) => A i j)
    (s.equivMap e) (t.equivMap e)

omit [Fintype α] [Fintype β] [DecidableEq β] in
theorem selectedPermanent_subtype_sets (A : Matrix α α R) (U s t : Finset α)
    (hs : s ⊆ U) (ht : t ⊆ U) :
    selectedPermanent (A.submatrix (Subtype.val : U → α) Subtype.val)
      (s.subtype (fun x => x ∈ U)) (t.subtype (fun x => x ∈ U)) = selectedPermanent A s t := by
  have h := selectedPermanent_submatrix_embedding A (Function.Embedding.subtype (fun x => x ∈ U))
    (s.subtype (fun x => x ∈ U)) (t.subtype (fun x => x ∈ U))
  rw [Finset.subtype_map_of_mem hs, Finset.subtype_map_of_mem ht] at h
  exact h

omit [Fintype α] [Fintype β] [DecidableEq β] [CommSemiring R] in
theorem subtype_compl_map (U F : Finset α) (hF : F ⊆ U) :
    ((F.subtype (fun x => x ∈ U))ᶜ).map (Function.Embedding.subtype (fun x => x ∈ U)) = U \ F := by
  have hu : (Finset.univ : Finset U).map (Function.Embedding.subtype (fun x => x ∈ U)) = U := by
    ext x
    simp
  rw [Finset.compl_eq_univ_sdiff, Finset.map_sdiff, hu, Finset.subtype_map_of_mem hF]

omit [Fintype β] [DecidableEq β] [CommSemiring R] in
theorem disjoint_subtype_compl_map (U F : Finset α) (hUF : Disjoint U F) :
    ((F.subtype (fun x => x ∈ Uᶜ))ᶜ).map
      (Function.Embedding.subtype (fun x => x ∈ Uᶜ)) = (F ∪ U)ᶜ := by
  have hF : F ⊆ Uᶜ := by
    intro x hx
    exact Finset.mem_compl.mpr (Finset.disjoint_right.mp hUF hx)
  rw [subtype_compl_map Uᶜ F hF]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_union]
  tauto

omit [Fintype β] [DecidableEq β] [CommSemiring R] in
theorem disjoint_subtype_card (U F : Finset α) (hUF : Disjoint U F) :
    (F.subtype (fun x => x ∈ Uᶜ)).card = F.card := by
  have hF : F ⊆ Uᶜ := by
    intro x hx
    exact Finset.mem_compl.mpr (Finset.disjoint_right.mp hUF hx)
  have h := Finset.subtype_map_of_mem hF
  have hc := congrArg Finset.card h
  simpa only [Finset.card_map] using hc

end TournamentHamiltonian
