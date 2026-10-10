import TournamentHamiltonian.CarouselPathLower
import TournamentHamiltonian.ActualUniformUpper

namespace TournamentHamiltonian
open scoped Classical
open Filter

set_option backward.isDefEq.respectTransparency false

theorem maxPaths_upper_uniform :
    ∃ C : ℝ,0≤C ∧ ∃ N : ℕ,2≤N ∧ ∀ n : ℕ,N≤n →
      (maxPaths n : ℝ)≤(upperConstant+C/n)*meanPaths n := by
  obtain ⟨C,hC,hupper⟩ := actual_uniform_pathCount_upper
  obtain ⟨Nu,hu⟩ := eventually_atTop.mp hupper
  refine ⟨C,hC,max Nu 2,le_max_right _ _,?_⟩
  intro n hn
  obtain ⟨T,_hT,hmax⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Tournament n))
    ⟨alternatingTournament n,Finset.mem_univ _⟩ pathCount
  change maxPaths n=pathCount T at hmax
  rw [hmax]
  have h := hu n ((le_max_left Nu 2).trans hn) T
  exact (div_le_iff₀ (by unfold meanPaths; positivity : 0<meanPaths n)).mp h

/-- The actual all-order asymptotic theorem, with one common absolute constant
and one common threshold for its genuine maximum Hamiltonian path count. -/
theorem mainBound : MainBound := by
  obtain ⟨Cl,hCl,Nl,hNl,hl⟩ := maxPaths_lower_uniform
  obtain ⟨Cu,hCu,Nu,hNu,hu⟩ := maxPaths_upper_uniform
  refine ⟨Cl+Cu,add_nonneg hCl hCu,max Nl Nu,hNl.trans (le_max_left _ _),?_⟩
  intro n hn
  have hnNl : Nl≤n := by omega
  have hnNu : Nu≤n := by omega
  have hn0 : (0 : ℝ)≤n := Nat.cast_nonneg _
  have hm : 0≤meanPaths n := by unfold meanPaths; positivity
  have hL : Cl/(n : ℝ)≤(Cl+Cu)/n := div_le_div_of_nonneg_right (by linarith) hn0
  have hU : Cu/(n : ℝ)≤(Cl+Cu)/n := div_le_div_of_nonneg_right (by linarith) hn0
  constructor
  · exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hL lowerConstant) hm).trans (hl n hnNl)
  · exact (hu n hnNu).trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl _) hU) hm)

end TournamentHamiltonian
