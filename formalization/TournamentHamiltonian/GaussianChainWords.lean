import TournamentHamiltonian.GaussianChains

/-! Actual alternating matrix-chain entries as sums over all internal numerical labels. -/

namespace TournamentHamiltonian

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def alternatingChainWord (B : Matrix ι ι ℝ) :
    (m : ℕ) → Bool → ι → ι → (Fin m → ι) → ℝ
  | 0, s, x, y, _ => orientedChainFactor B s x y
  | m + 1, s, x, y, w => orientedChainFactor B s x (w 0) *
      alternatingChainWord B m (!s) (w 0) y (Fin.tail w)

theorem alternatingChainWord_sum (B : Matrix ι ι ℝ) (m : ℕ) (s : Bool) (x y : ι) :
    (∑ w : Fin m → ι, alternatingChainWord B m s x y w) = alternatingChain B (m + 1) s x y := by
  induction m generalizing s x y with
  | zero => simp [alternatingChainWord, alternatingChain]
  | succ m ih =>
      calc
        _ = ∑ v : ι × (Fin m → ι), alternatingChainWord B (m + 1) s x y (Fin.cons v.1 v.2) := by
          apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => ι)).symm
          intro w
          simp [Fin.consEquiv]
        _ = ∑ z : ι, ∑ w : Fin m → ι,
            orientedChainFactor B s x z * alternatingChainWord B m (!s) z y w := by
          rw [Fintype.sum_prod_type]
          simp only [alternatingChainWord, Fin.cons_zero, Fin.tail_cons]
        _ = ∑ z : ι, orientedChainFactor B s x z * alternatingChain B (m + 1) (!s) z y := by
          apply Finset.sum_congr rfl
          intro z _
          rw [← Finset.mul_sum, ih]
        _ = _ := by
          change _ = (orientedChainFactor B s * alternatingChain B (m + 1) (!s)) x y
          exact Matrix.mul_apply.symm

def chainWordVertices (m : ℕ) (x y : ι) (w : Fin m → ι) : Fin (m + 2) → ι :=
  Fin.cons x (Fin.snoc w y)

omit [Fintype ι] [DecidableEq ι] in
theorem alternatingChainWord_eq_prod (B : Matrix ι ι ℝ) (m : ℕ) (s : Bool) (x y : ι)
    (w : Fin m → ι) :
    alternatingChainWord B m s x y w = ∏ i : Fin (m + 1),
      orientedChainFactor B (chainEndpointOrientation i.val s)
        (chainWordVertices m x y w i.castSucc) (chainWordVertices m x y w i.succ) := by
  induction m generalizing s x y with
  | zero =>
      simp [alternatingChainWord, chainWordVertices, chainEndpointOrientation]
      change orientedChainFactor B s x y = orientedChainFactor B s x
        (Fin.snoc (α := fun _ : Fin 1 => ι) w y (Fin.last 0))
      rw [Fin.snoc_last]
  | succ m ih =>
      cases w using Fin.consCases with
      | cons z w =>
          simp only [alternatingChainWord, Fin.cons_zero, Fin.tail_cons]
          rw [Fin.prod_univ_succ]
          unfold chainWordVertices
          rw [← Fin.cons_snoc_eq_snoc_cons]
          simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
            chainEndpointOrientation, Fin.castSucc_succ, Fin.val_succ]
          rw [ih]
          rfl

end TournamentHamiltonian
