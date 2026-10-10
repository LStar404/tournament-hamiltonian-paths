import TournamentHamiltonian.FourBlockBounds
import TournamentHamiltonian.SelectedMinorEmbeddings
import TournamentHamiltonian.DeletedExceptionalCrossBounds

/-! The actual four-block estimate after disjoint short deletions. The remaining
analytic hypothesis bounds actual ambient core minors; all cross factors are proved. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem deleted_permanent_fourBlock_normalized_le {n : ℕ} (T : Tournament n)
    (F U : Finset (Fin n)) (hUF : Disjoint U F)
    (B : ℝ) (hB : 0 ≤ B)
    (hN : 0 < (F ∪ U)ᶜ.card) (hfN : 2 * F.card ≤ (F ∪ U)ᶜ.card)
    (hl : ∀ x, 0 ≤ ambientCoreLeft T (F ∪ U)ᶜ x)
    (hr : ∀ x, 0 ≤ ambientCoreRight T (F ∪ U)ᶜ x)
    (hcross : ∀ x ∈ F,
      let M := (F ∪ U)ᶜ
      let u := 2 / (M.card : ℝ) * ∑ j ∈ M, adjacency T x j * ambientCoreRight T M j
      let v := 2 / (M.card : ℝ) * ∑ j ∈ M, ambientCoreLeft T M j * adjacency T j x
      0 ≤ u ∧ 0 ≤ v ∧ u ≤ 3 ∧ v ≤ 3 ∧ u * v ≤ 1 / 4)
    (hcore : let M := (F ∪ U)ᶜ
      ∀ s ≤ F.card, ∀ I ∈ M.powersetCard (F.card - s),
        ∀ J ∈ M.powersetCard (F.card - s),
          selectedPermanent (adjacency T) (M \ J) (M \ I) ≤
            (B * (((M.card - (F.card - s)).factorial : ℝ) /
              (2 : ℝ) ^ (M.card - (F.card - s)))) *
              (∏ i ∈ I, ambientCoreLeft T M i) * (∏ j ∈ J, ambientCoreRight T M j)) :
    ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent /
      (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) ≤
        B * (1 / 4 : ℝ) ^ F.card * Real.exp (292 * (F.card : ℝ) ^ 2 / (F ∪ U)ᶜ.card) := by
  let F' := F.subtype (fun x => x ∈ Uᶜ)
  let M := (F ∪ U)ᶜ
  let e := Function.Embedding.subtype (fun x => x ∈ Uᶜ)
  let A : Matrix (Uᶜ : Finset (Fin n)) (Uᶜ : Finset (Fin n)) ℝ :=
    (adjacency T).submatrix Subtype.val Subtype.val
  let l : (Uᶜ : Finset (Fin n)) → ℝ := fun x => ambientCoreLeft T M x
  let r : (Uᶜ : Finset (Fin n)) → ℝ := fun x => ambientCoreRight T M x
  let u : (Uᶜ : Finset (Fin n)) → ℝ := fun x =>
    2 / (M.card : ℝ) * ∑ j ∈ M, adjacency T x j * ambientCoreRight T M j
  let v : (Uᶜ : Finset (Fin n)) → ℝ := fun x =>
    2 / (M.card : ℝ) * ∑ j ∈ M, ambientCoreLeft T M j * adjacency T j x
  have hmap : F'ᶜ.map e = M := disjoint_subtype_compl_map U F hUF
  have hfc : F'.card = F.card := disjoint_subtype_card U F hUF
  have hmc : F'ᶜ.card = M.card := by
    have h := congrArg Finset.card hmap
    simpa only [Finset.card_map] using h
  have hm0 : (0 : ℝ) < M.card := by exact_mod_cast hN
  have hx (x : (Uᶜ : Finset (Fin n))) (hx : x ∈ F') :
      0 ≤ u x ∧ 0 ≤ v x ∧ u x ≤ 3 ∧ v x ≤ 3 ∧ u x * v x ≤ 1 / 4 :=
    hcross x (Finset.mem_subtype.mp hx)
  have h := permanent_fourBlock_normalized_le A F' l r u v B (1 / 4) 3 hB
    (by norm_num) (by norm_num) (by norm_num) (by rwa [hmc]) (by rwa [hfc, hmc])
    (fun i j => adjacency_between_nonneg T i j) (fun i j => adjacency_between_le_one T i j)
    (fun i => hl i) (fun j => hr j)
    (fun x hxF => (hx x hxF).1) (fun x hxF => (hx x hxF).2.1)
    (fun x hxF => (hx x hxF).2.2.1) (fun x hxF => (hx x hxF).2.2.2.1)
    (fun x hxF => (hx x hxF).2.2.2.2)
    (by
      intro s hs I hI J hJ
      simp only [hfc, hmc] at hs hI hJ ⊢
      have hmem (K : Finset (Uᶜ : Finset (Fin n))) (hK : K ∈ F'ᶜ.powersetCard (F.card - s)) :
          K.map e ∈ M.powersetCard (F.card - s) := by
        apply Finset.mem_powersetCard.mpr
        constructor
        · rw [← hmap]
          exact Finset.map_subset_map.mpr (Finset.mem_powersetCard.mp hK).1
        · simpa only [Finset.card_map] using (Finset.mem_powersetCard.mp hK).2
      change selectedPermanent ((adjacency T).submatrix e e) (F'ᶜ \ J) (F'ᶜ \ I) ≤ _
      rw [selectedPermanent_submatrix_embedding (adjacency T) e]
      rw [Finset.map_sdiff, Finset.map_sdiff, hmap]
      have hc := hcore s hs (I.map e) (hmem I hI) (J.map e) (hmem J hJ)
      simp only [Finset.prod_map] at hc
      have hel (i : (Uᶜ : Finset (Fin n))) : ambientCoreLeft T (F ∪ U)ᶜ (e i) = l i := rfl
      have her (i : (Uᶜ : Finset (Fin n))) : ambientCoreRight T (F ∪ U)ᶜ (e i) = r i := rfl
      simp_rw [hel, her] at hc
      exact hc)
    (by
      intro x hxF
      have he : (∑ j ∈ F'ᶜ, A x j * r j) = ∑ j ∈ M, adjacency T x j * ambientCoreRight T M j := by
        have hh := Finset.sum_map F'ᶜ e (fun j => adjacency T x j * ambientCoreRight T M j)
        rw [hmap] at hh
        exact hh.symm
      rw [he, hmc]
      dsimp [u]
      have heq : (M.card : ℝ) / 2 * (2 / M.card) = 1 := by field_simp
      rw [← mul_assoc, heq, one_mul])
    (by
      intro x hxF
      have he : (∑ i ∈ F'ᶜ, l i * A i x) = ∑ i ∈ M, ambientCoreLeft T M i * adjacency T i x := by
        have hh := Finset.sum_map F'ᶜ e (fun i => ambientCoreLeft T M i * adjacency T i x)
        rw [hmap] at hh
        exact hh.symm
      rw [he, hmc]
      dsimp [v]
      have heq : (M.card : ℝ) / 2 * (2 / M.card) = 1 := by field_simp
      rw [← mul_assoc, heq, one_mul])
  have hn : Fintype.card (Uᶜ : Finset (Fin n)) = n - U.card := by
    simp
  rw [hn, hfc, hmc] at h
  convert h using 1
  congr 2
  ring

theorem short_deleted_permanent_fourBlock_eventually :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
      ∀ U : Finset (Fin n), U.card < subsetCutoff n → Disjoint U (exceptionalVertices T) →
      ∀ B : ℝ, 0 ≤ B →
      let F := exceptionalVertices T
      let M := (F ∪ U)ᶜ
      (∀ s ≤ F.card, ∀ I ∈ M.powersetCard (F.card - s), ∀ J ∈ M.powersetCard (F.card - s),
        selectedPermanent (adjacency T) (M \ J) (M \ I) ≤
          (B * (((M.card - (F.card - s)).factorial : ℝ) /
            (2 : ℝ) ^ (M.card - (F.card - s)))) *
            (∏ i ∈ I, ambientCoreLeft T M i) * (∏ j ∈ J, ambientCoreRight T M j)) →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent /
        (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) ≤
          B * (1 / 4 : ℝ) ^ F.card * Real.exp (292 * (F.card : ℝ) ^ 2 / M.card) := by
  have hlog := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 1600
  simp only [mul_zero] at hlog
  filter_upwards [hlog.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    actual_deleted_exceptional_cross_bounds, ambient_deleted_core_weight_budgets,
    short_deleted_exceptional_core_uniform_dense, eventually_ge_atTop (2 : ℕ)]
    with n hlogn hcross hweights hcore hn T hV U hU hUF B hB
  dsimp only
  intro hp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogR : 1600 * Real.log (n : ℝ) ≤ n := by
    change 1600 * (Real.log (n : ℝ) / n) ≤ 1 at hlogn
    have he : 1600 * (Real.log (n : ℝ) / n) = (1600 * Real.log (n : ℝ)) / n := by ring
    rw [he] at hlogn
    simpa only [one_mul] using (div_le_iff₀ hn0).mp hlogn
  have hf := exceptionalVertices_card_le_log T hn hV
  have hN := hcore T hV U hU
  have hfN : 2 * (exceptionalVertices T).card ≤ (exceptionalVertices T ∪ U)ᶜ.card := by
    have h : (2 : ℝ) * (exceptionalVertices T).card ≤ (exceptionalVertices T ∪ U)ᶜ.card := by
      linarith [hN.2.1]
    exact_mod_cast h
  have hNpos : 0 < (exceptionalVertices T ∪ U)ᶜ.card := by omega
  exact deleted_permanent_fourBlock_normalized_le T (exceptionalVertices T) U hUF B hB hNpos hfN
    (hweights T hV U hU).1 (hweights T hV U hU).2.1 (hcross T hV U hU) hp

end TournamentHamiltonian
