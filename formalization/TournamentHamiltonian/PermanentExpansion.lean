import TournamentHamiltonian.ScalingIdentities
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators

/-! Exact finite coefficient normalization for §3.2. -/

namespace TournamentHamiltonian

open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- The permanent of a rectangularly selected minor, indexed canonically by
all bijections between its selected column and row sets. It is zero when
their cardinalities differ. -/
noncomputable def selectedPermanent (B : Matrix ι ι R) (s t : Finset ι) : R :=
  ∑ e : s ≃ t, ∏ i : s, B (e i) i

/-- Direct expansion of the actual permanent, before collecting equal degrees. -/
theorem permanent_one_add_expansion (B : Matrix ι ι R) (z : R) :
    Matrix.permanent (fun i j => 1 + z * B i j) =
      ∑ s : Finset ι, z ^ s.card *
        ∑ σ : Equiv.Perm ι, ∏ i ∈ s, B (σ i) i := by
  classical
  unfold Matrix.permanent
  simp_rw [add_comm (1 : R), Fintype.prod_add]
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

private noncomputable def gluePermutation (s t : Finset ι)
    (e : s ≃ t) (f : {i // i ∉ s} ≃ {i // i ∉ t}) : Equiv.Perm ι :=
  Equiv.subtypeCongr e f

omit [Fintype ι] in
private theorem gluePermutation_apply_mem (s t : Finset ι)
    (e : s ≃ t) (f : {i // i ∉ s} ≃ {i // i ∉ t}) (i : s) :
    gluePermutation s t e f i = e i := by
  classical
  simp [gluePermutation, Equiv.subtypeCongr]

omit [Fintype ι] in
private theorem gluePermutation_apply_notMem (s t : Finset ι)
    (e : s ≃ t) (f : {i // i ∉ s} ≃ {i // i ∉ t}) (i : {i // i ∉ s}) :
    gluePermutation s t e f i = f i := by
  classical
  simp [gluePermutation, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_neg]

omit [Fintype ι] in
private theorem gluePermutation_image (s t : Finset ι)
    (e : s ≃ t) (f : {i // i ∉ s} ≃ {i // i ∉ t}) :
    s.image (gluePermutation s t e f) = t := by
  classical
  ext j
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    rw [gluePermutation_apply_mem s t e f ⟨i, hi⟩]
    exact (e ⟨i, hi⟩).property
  · intro hj
    refine Finset.mem_image.mpr ⟨e.symm ⟨j, hj⟩, (e.symm ⟨j, hj⟩).property, ?_⟩
    rw [gluePermutation_apply_mem]
    simp

private noncomputable def permutationSplit (s : Finset ι) :
    (Σ t : Finset ι, (s ≃ t) × ({i // i ∉ s} ≃ {i // i ∉ t})) ≃ Equiv.Perm ι :=
  Equiv.ofBijective (fun x => gluePermutation s x.1 x.2.1 x.2.2) (by
    classical
    constructor
    · intro x y h
      change gluePermutation s x.1 x.2.1 x.2.2 = gluePermutation s y.1 y.2.1 y.2.2 at h
      have ht : x.1 = y.1 := by
        rw [← gluePermutation_image s x.1 x.2.1 x.2.2,
          ← gluePermutation_image s y.1 y.2.1 y.2.2, h]
      rcases x with ⟨t, e, f⟩
      rcases y with ⟨u, e', f'⟩
      dsimp at ht
      subst u
      have he : e = e' := by
        apply Equiv.ext
        intro i
        apply Subtype.ext
        simpa only [gluePermutation_apply_mem] using congrArg (fun σ => σ i) h
      have hf : f = f' := by
        apply Equiv.ext
        intro i
        apply Subtype.ext
        simpa only [gluePermutation_apply_notMem] using congrArg (fun σ => σ i) h
      subst e'
      subst f'
      rfl
    · intro σ
      let t := s.image σ
      have hm (i : ι) : i ∈ s ↔ σ i ∈ t := by
        simp [t, Finset.mem_image, σ.injective.eq_iff]
      let e : s ≃ t := σ.subtypeEquiv hm
      let f : {i // i ∉ s} ≃ {i // i ∉ t} :=
        σ.subtypeEquiv (fun i => not_congr (hm i))
      refine ⟨⟨t, e, f⟩, ?_⟩
      apply Equiv.ext
      intro i
      by_cases hi : i ∈ s
      · simpa [e] using gluePermutation_apply_mem s t e f ⟨i, hi⟩
      · simpa [f] using gluePermutation_apply_notMem s t e f ⟨i, hi⟩)

set_option backward.isDefEq.respectTransparency.types false in
theorem permanent_selected_extension_count (B : Matrix ι ι R) (s : Finset ι) :
    (∑ σ : Equiv.Perm ι, ∏ i ∈ s, B (σ i) i) =
      ((Fintype.card ι - s.card).factorial : R) *
        ∑ t : Finset ι, selectedPermanent B s t := by
  classical
  have hs : (∑ σ : Equiv.Perm ι, ∏ i ∈ s, B (σ i) i) =
      ∑ x : (Σ t : Finset ι, (s ≃ t) × ({i // i ∉ s} ≃ {i // i ∉ t})),
        ∏ i : s, B (x.2.1 i) i := by
    apply (Fintype.sum_equiv (permutationSplit s) _ _ ?_).symm
    intro x
    calc
      (∏ i : s, B (x.2.1 i) i) = ∏ i : s, B (((permutationSplit s) x) i) i := by
        apply Finset.prod_congr rfl
        intro i _
        change B (x.2.1 i) i = B (gluePermutation s x.1 x.2.1 x.2.2 i) i
        rw [gluePermutation_apply_mem]
      _ = _ := Finset.prod_coe_sort s (fun i => B (((permutationSplit s) x) i) i)
  rw [hs]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  simp_rw [selectedPermanent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro e _
  have hc : Fintype.card ({i // i ∉ s} ≃ {i // i ∉ t}) =
      (Fintype.card ι - s.card).factorial := by
    calc
      _ = (Fintype.card {i // i ∉ s}).factorial := Fintype.card_equiv e.toCompl
      _ = _ := by rw [Fintype.card_subtype_compl, Fintype.card_coe]
  let v : R := ∏ i : s, B (e i) i
  change (∑ _ : ({i // i ∉ s} ≃ {i // i ∉ t}), v) =
    ((Fintype.card ι - s.card).factorial : R) * v
  simpa only [Finset.card_univ, hc, nsmul_eq_mul] using
    (Finset.sum_const (s := (Finset.univ : Finset ({i // i ∉ s} ≃ {i // i ∉ t}))) v)

/-- The coefficient-generating minor formula, valid in every commutative semiring. -/
theorem permanent_one_add_minor_expansion (B : Matrix ι ι R) (z : R) :
    Matrix.permanent (fun i j => 1 + z * B i j) =
      ∑ s : Finset ι, z ^ s.card *
        ((Fintype.card ι - s.card).factorial : R) *
          ∑ t : Finset ι, selectedPermanent B s t := by
  rw [permanent_one_add_expansion]
  simp_rw [permanent_selected_extension_count]
  simp only [mul_assoc]

set_option backward.isDefEq.respectTransparency.types false in
omit [Fintype ι] in
theorem selectedPermanent_eq_permanent (B : Matrix ι ι R) (s t : Finset ι)
    (e : s ≃ t) :
    selectedPermanent B s t = Matrix.permanent (fun i j : s => B (e i) j) := by
  classical
  unfold selectedPermanent Matrix.permanent
  apply (Fintype.sum_equiv (Equiv.equivCongr (Equiv.refl s) e) _ _ ?_).symm
  intro σ
  rfl

omit [Fintype ι] in
theorem selectedPermanent_eq_zero_of_card_ne (B : Matrix ι ι R) (s t : Finset ι)
    (h : s.card ≠ t.card) : selectedPermanent B s t = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e _
  exact (h (by simpa using Fintype.card_congr e)).elim

private theorem selectedPermanent_sum_card (B : Matrix ι ι R) (s : Finset ι) :
    (∑ t : Finset ι, selectedPermanent B s t) =
      ∑ t ∈ Finset.univ.filter (fun t : Finset ι => t.card = s.card),
        selectedPermanent B s t := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro t _ ht
  apply selectedPermanent_eq_zero_of_card_ne
  simpa [eq_comm] using ht

/-- The sum of all actual `k` by `k` minor permanents. -/
noncomputable def permanentMinorSum (B : Matrix ι ι R) (k : ℕ) : R :=
  ∑ s ∈ Finset.univ.filter (fun s : Finset ι => s.card = k),
    ∑ t ∈ Finset.univ.filter (fun t : Finset ι => t.card = k),
      selectedPermanent B s t

theorem permanent_one_add_degree_expansion (B : Matrix ι ι R) (z : R) :
    Matrix.permanent (fun i j => 1 + z * B i j) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        z ^ k * ((Fintype.card ι - k).factorial : R) * permanentMinorSum B k := by
  classical
  rw [permanent_one_add_minor_expansion]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.range (Fintype.card ι + 1)) (g := Finset.card)
    (fun s _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ s)))]
  apply Finset.sum_congr rfl
  intro k _
  unfold permanentMinorSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [(Finset.mem_filter.mp hs).2, selectedPermanent_sum_card,
    (Finset.mem_filter.mp hs).2]

theorem permanentMinorSum_eq_zero_of_lt (B : Matrix ι ι R) (k : ℕ)
    (hk : Fintype.card ι < k) : permanentMinorSum B k = 0 := by
  classical
  have he : Finset.univ.filter (fun s : Finset ι => s.card = k) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro s _ h
    have := Finset.card_le_univ s
    omega
  simp [permanentMinorSum, he]

@[simp] theorem permanentMinorSum_zero (B : Matrix ι ι R) : permanentMinorSum B 0 = 1 := by
  classical
  simp [permanentMinorSum, selectedPermanent, Finset.card_eq_zero, Finset.filter_eq']

omit [Fintype ι] in
theorem map_selectedPermanent {S : Type*} [CommSemiring S] (f : R →+* S)
    (B : Matrix ι ι R) (s t : Finset ι) :
    selectedPermanent (fun i j => f (B i j)) s t = f (selectedPermanent B s t) := by
  classical
  simp [selectedPermanent, map_sum, map_prod]

theorem map_permanentMinorSum {S : Type*} [CommSemiring S] (f : R →+* S)
    (B : Matrix ι ι R) (k : ℕ) :
    permanentMinorSum (fun i j => f (B i j)) k = f (permanentMinorSum B k) := by
  classical
  simp [permanentMinorSum, map_selectedPermanent, map_sum]

/-- The actual permanent as a polynomial in the perturbation parameter. -/
noncomputable def permanentPolynomial (B : Matrix ι ι R) : Polynomial R :=
  Matrix.permanent (fun i j => 1 + Polynomial.X * Polynomial.C (B i j))

set_option backward.isDefEq.respectTransparency.types false in
theorem permanentPolynomial_expansion (B : Matrix ι ι R) :
    permanentPolynomial B =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        Polynomial.C (((Fintype.card ι - k).factorial : R) * permanentMinorSum B k) *
          Polynomial.X ^ k := by
  classical
  unfold permanentPolynomial
  rw [permanent_one_add_degree_expansion (fun i j => Polynomial.C (B i j)) Polynomial.X]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_permanentMinorSum, Polynomial.C_mul, map_natCast]
  ring

/-- Exact coefficients, including zero coefficients above the matrix size. -/
theorem permanentPolynomial_coeff (B : Matrix ι ι R) (k : ℕ) :
    (permanentPolynomial B).coeff k =
      ((Fintype.card ι - k).factorial : R) * permanentMinorSum B k := by
  classical
  rw [permanentPolynomial_expansion, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k ≤ Fintype.card ι
  · simp [Finset.mem_range, hk]
  · rw [permanentMinorSum_eq_zero_of_lt B k (Nat.lt_of_not_ge hk), mul_zero]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
    simp [show k ≠ j by omega]

theorem permanentPolynomial_eval (B : Matrix ι ι R) (z : R) :
    (permanentPolynomial B).eval z = Matrix.permanent (fun i j => 1 + z * B i j) := by
  classical
  simp only [permanentPolynomial, Matrix.permanent, Polynomial.eval_finsetSum,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C]

omit [Fintype ι] in
theorem selectedPermanent_scale (c : R) (B : Matrix ι ι R) (s t : Finset ι) :
    selectedPermanent (fun i j => c * B i j) s t =
      c ^ s.card * selectedPermanent B s t := by
  classical
  simp [selectedPermanent, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.mul_sum]

theorem permanentMinorSum_scale (c : R) (B : Matrix ι ι R) (k : ℕ) :
    permanentMinorSum (fun i j => c * B i j) k = c ^ k * permanentMinorSum B k := by
  classical
  unfold permanentMinorSum
  simp_rw [selectedPermanent_scale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [(Finset.mem_filter.mp hs).2, Finset.mul_sum]

section Normalization

variable {K : Type*} [Field K] [CharZero K]

/-- The actual normalized permanent polynomial `per(J+tE)/n!`. -/
noncomputable def normalizedPermanentPolynomial (E : Matrix ι ι K) : Polynomial K :=
  Polynomial.C ((Fintype.card ι).factorial : K)⁻¹ * permanentPolynomial E

theorem factorial_ratio_eq_inv_descFactorial (n k : ℕ) (hk : k ≤ n) :
    ((n - k).factorial : K) / (n.factorial : K) =
      (1 : K) / (n.descFactorial k : K) := by
  have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hd : (n.descFactorial k : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hk))
  field_simp
  exact_mod_cast Nat.factorial_mul_descFactorial hk

/-- The coefficient `a_k` is exactly the minor sum divided by `(n)_k`.
Above degree `n`, both sides vanish; no positive-size assumption is needed. -/
theorem normalizedPermanentPolynomial_coeff (E : Matrix ι ι K) (k : ℕ) :
    (normalizedPermanentPolynomial E).coeff k =
      permanentMinorSum E k / ((Fintype.card ι).descFactorial k : K) := by
  rw [normalizedPermanentPolynomial, Polynomial.coeff_C_mul, permanentPolynomial_coeff]
  by_cases hk : k ≤ Fintype.card ι
  · have hr := factorial_ratio_eq_inv_descFactorial (K := K) (Fintype.card ι) k hk
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm] at hr
    rw [← mul_assoc, hr]
    simp [div_eq_mul_inv, mul_comm]
  · rw [permanentMinorSum_eq_zero_of_lt E k (Nat.lt_of_not_ge hk)]
    simp

omit [CharZero K] in
theorem normalizedPermanentPolynomial_eval (E : Matrix ι ι K) (z : K) :
    (normalizedPermanentPolynomial E).eval z =
      Matrix.permanent (fun i j => 1 + z * E i j) / ((Fintype.card ι).factorial : K) := by
  simp [normalizedPermanentPolynomial, permanentPolynomial_eval,
    div_eq_mul_inv, mul_comm]

/-- The coefficient `F_k` obtained by rescaling `a_k` is the minor sum of `B=E/n`. -/
theorem normalized_coeff_rescaling (E : Matrix ι ι K) (k : ℕ) :
    (((Fintype.card ι).descFactorial k : K) / (Fintype.card ι : K) ^ k) *
        (normalizedPermanentPolynomial E).coeff k =
      permanentMinorSum (fun i j => E i j / (Fintype.card ι : K)) k := by
  rw [normalizedPermanentPolynomial_coeff]
  simp_rw [div_eq_mul_inv, mul_comm (E _ _)]
  rw [permanentMinorSum_scale, inv_pow]
  by_cases hk : k ≤ Fintype.card ι
  · have hd : ((Fintype.card ι).descFactorial k : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hk))
    field_simp
  · rw [permanentMinorSum_eq_zero_of_lt E k (Nat.lt_of_not_ge hk)]
    simp

end Normalization

private noncomputable def enumerationEmbedding {κ : Type*} (s : Finset ι)
    (e : κ ≃ s) : κ ↪ ι where
  toFun i := e i
  inj' _ _ h := e.injective (Subtype.ext h)

omit [Fintype ι] in
private theorem enumerationEmbedding_image {κ : Type*} [Fintype κ]
    (s : Finset ι) (e : κ ≃ s) :
    Finset.univ.image (enumerationEmbedding s e) = s := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact (e i).property
  · intro hj
    refine Finset.mem_image.mpr ⟨e.symm ⟨j, hj⟩, Finset.mem_univ _, ?_⟩
    change ↑(e (e.symm ⟨j, hj⟩)) = j
    exact congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩)

private noncomputable def embeddingSplit {κ : Type*} [Fintype κ] [DecidableEq κ] :
    (Σ s : Finset ι, κ ≃ s) ≃ (κ ↪ ι) :=
  Equiv.ofBijective (fun x => enumerationEmbedding x.1 x.2) (by
    classical
    constructor
    · intro x y h
      have hs : x.1 = y.1 := by
        rw [← enumerationEmbedding_image x.1 x.2, ← enumerationEmbedding_image y.1 y.2]
        exact congrArg (fun f : κ ↪ ι => Finset.univ.image f) h
      rcases x with ⟨s, e⟩
      rcases y with ⟨t, f⟩
      dsimp at hs
      subst t
      have hef : e = f := by
        apply Equiv.ext
        intro i
        apply Subtype.ext
        exact congrArg (fun f : κ ↪ ι => f i) h
      subst f
      rfl
    · intro f
      let s := Finset.univ.image f
      let e : κ ≃ s := Equiv.ofBijective (fun i => ⟨f i,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩) (by
          constructor
          · intro i j h
            exact f.injective (congrArg Subtype.val h)
          · intro j
            obtain ⟨i, _, hi⟩ := Finset.mem_image.mp j.property
            exact ⟨i, Subtype.ext hi⟩)
      exact ⟨⟨s, e⟩, by ext i; rfl⟩)

omit [Fintype ι] in
private theorem paired_enumeration_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Matrix ι ι R) (s t : Finset ι) (c : κ ≃ s) :
    (∑ r : κ ≃ t, ∏ i : κ, B (r i) (c i)) = selectedPermanent B s t := by
  classical
  unfold selectedPermanent
  apply Fintype.sum_equiv (Equiv.equivCongr c (Equiv.refl t))
  intro r
  apply Fintype.prod_equiv c
  intro i
  simp

omit [Fintype ι] in
private theorem card_enumerations {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : Finset ι) :
    Fintype.card (κ ≃ s) = if s.card = Fintype.card κ then (Fintype.card κ).factorial else 0 := by
  classical
  split_ifs with hs
  · let e : κ ≃ s := Fintype.equivOfCardEq (by simpa using hs.symm)
    exact Fintype.card_equiv e
  · have : IsEmpty (κ ≃ s) := ⟨fun e => hs (by simpa using (Fintype.card_congr e).symm)⟩
    exact Fintype.card_of_isEmpty

/-- The sum over ordered tuples with pairwise distinct row and column labels. -/
noncomputable def distinctCoordinateSum (B : Matrix ι ι R) (k : ℕ) : R :=
  ∑ c : Fin k ↪ ι, ∑ r : Fin k ↪ ι, ∏ i : Fin k, B (r i) (c i)

theorem distinctCoordinateSum_eq_factorial_minorSum (B : Matrix ι ι R) (k : ℕ) :
    distinctCoordinateSum B k = (k.factorial : R) * permanentMinorSum B k := by
  classical
  unfold distinctCoordinateSum
  let he := embeddingSplit (ι := ι) (κ := Fin k)
  have hs : (∑ c : Fin k ↪ ι, ∑ r : Fin k ↪ ι, ∏ i : Fin k, B (r i) (c i)) =
      ∑ x : (Σ s : Finset ι, Fin k ≃ s),
        ∑ y : (Σ t : Finset ι, Fin k ≃ t), ∏ i : Fin k, B (y.2 i) (x.2 i) := by
    apply (Fintype.sum_equiv he _ _ ?_).symm
    intro x
    apply Fintype.sum_equiv he
    intro y
    rfl
  rw [hs]
  simp only [Fintype.sum_sigma]
  simp_rw [paired_enumeration_sum]
  have hconst (s : Finset ι) :
      (∑ _ : Fin k ≃ s, ∑ t : Finset ι, selectedPermanent B s t) =
        if s.card = k then (k.factorial : R) * ∑ t : Finset ι, selectedPermanent B s t else 0 := by
    let v := ∑ t : Finset ι, selectedPermanent B s t
    change (∑ _ : Fin k ≃ s, v) = if s.card = k then (k.factorial : R) * v else 0
    rw [Finset.sum_const, Finset.card_univ, card_enumerations]
    simp only [Fintype.card_fin]
    split_ifs <;> simp [nsmul_eq_mul]
  simp_rw [hconst]
  rw [← Finset.sum_filter]
  unfold permanentMinorSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [selectedPermanent_sum_card, (Finset.mem_filter.mp hs).2]

theorem permanentMinorSum_eq_distinctCoordinateSum_div_factorial
    {K : Type*} [Field K] [CharZero K] (B : Matrix ι ι K) (k : ℕ) :
    permanentMinorSum B k = distinctCoordinateSum B k / (k.factorial : K) := by
  rw [distinctCoordinateSum_eq_factorial_minorSum]
  have hk : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

/-- The exact distinct-coordinate identity in §3.2, with its `1/k!`
factor derived from the actual polynomial coefficient. -/
theorem normalized_coeff_distinct_coordinates {K : Type*} [Field K] [CharZero K]
    (E : Matrix ι ι K) (k : ℕ) :
    (((Fintype.card ι).descFactorial k : K) / (Fintype.card ι : K) ^ k) *
        (normalizedPermanentPolynomial E).coeff k =
      distinctCoordinateSum (fun i j => E i j / (Fintype.card ι : K)) k /
        (k.factorial : K) := by
  rw [normalized_coeff_rescaling]
  exact permanentMinorSum_eq_distinctCoordinateSum_div_factorial _ _

@[simp] theorem distinctCoordinateSum_zero (B : Matrix ι ι R) :
    distinctCoordinateSum B 0 = 1 := by
  rw [distinctCoordinateSum_eq_factorial_minorSum, permanentMinorSum_zero]
  simp

theorem distinctCoordinateSum_eq_zero_of_lt (B : Matrix ι ι R) (k : ℕ)
    (hk : Fintype.card ι < k) : distinctCoordinateSum B k = 0 := by
  rw [distinctCoordinateSum_eq_factorial_minorSum, permanentMinorSum_eq_zero_of_lt B k hk,
    mul_zero]

@[simp] theorem normalizedPermanentPolynomial_coeff_zero {K : Type*} [Field K] [CharZero K]
    (E : Matrix ι ι K) : (normalizedPermanentPolynomial E).coeff 0 = 1 := by
  rw [normalizedPermanentPolynomial_coeff, permanentMinorSum_zero]
  simp

theorem normalizedPermanentPolynomial_isEmpty {K : Type*} [Field K] [CharZero K]
    [IsEmpty ι] (E : Matrix ι ι K) : normalizedPermanentPolynomial E = 1 := by
  have hp : permanentPolynomial E = 1 := Matrix.permanent_isEmpty
  rw [normalizedPermanentPolynomial, hp]
  simp

end TournamentHamiltonian
