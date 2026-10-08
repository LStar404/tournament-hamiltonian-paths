import TournamentHamiltonian.SmallScoreRestorationBudget

namespace TournamentHamiltonian

theorem gaussian_restoration_log_identity (S P f theta a G D : ℝ)
    (hS : 0<S) (hP : 0<P) (hG : 0<G) (hD : 0<D) :
    S*P*f*Real.exp (-theta)*a = Real.exp (-1)*D*f*
      Real.exp (Real.log S+(Real.log P+1)-theta+(Real.log G-Real.log D))*(a/G) := by
  have he : Real.exp (-1)*Real.exp (Real.log S+(Real.log P+1)-theta+(Real.log G-Real.log D))=
      S*P*Real.exp (-theta)*(G/D) := by
    rw [←Real.exp_add]
    have hz : -1+(Real.log S+(Real.log P+1)-theta+(Real.log G-Real.log D))=
        Real.log S+Real.log P+(-theta)+(Real.log G-Real.log D) := by ring
    rw [hz,Real.exp_add,Real.exp_add,Real.exp_add,Real.exp_sub,
      Real.exp_log hS,Real.exp_log hP,Real.exp_log hG,Real.exp_log hD]
  calc
    _ = D*f*(S*P*Real.exp (-theta)*(G/D))*(a/G) := by field_simp
    _ = _ := by rw [←he]; ring

theorem gaussian_restoration_log_error (S P f theta a G D E r : ℝ)
    (hS : 0<S) (hP : 0<P) (hf : 0≤f) (hG : 1≤G) (hD : 0<D)
    (hr : 0≤r) (ha : |a-G|≤r)
    (hz : |Real.log S+(Real.log P+1)-theta+(Real.log G-Real.log D)|≤E) (hE : E≤1) :
    |S*P*f*Real.exp (-theta)*a-Real.exp (-1)*D*f|≤
      Real.exp (-1)*D*f*(3*r+2*E) := by
  exact gaussian_restoration_absolute_error _ _ _ _ _ E r (by positivity) hG hr ha hz hE
    (gaussian_restoration_log_identity S P f theta a G D hS hP (by linarith) hD)

end TournamentHamiltonian
