import TournamentHamiltonian.SmallScoreProducts
import Mathlib.Analysis.Complex.Exponential

namespace TournamentHamiltonian

theorem relative_gaussian_error_le (a G r : ℝ) (hG : 1≤G) (hr : 0≤r) (ha : |a-G|≤r) :
    |a/G-1|≤r := by
  have hGp : 0<G := by linarith
  have he : a/G-1=(a-G)/G := by field_simp
  rw [he,abs_div,abs_of_pos hGp]
  exact (div_le_iff₀ hGp).mpr (ha.trans (by simpa using mul_le_mul_of_nonneg_left hG hr))

theorem relative_exponential_product_error (a G z E r : ℝ)
    (hG : 1≤G) (hr : 0≤r) (ha : |a-G|≤r) (hz : |z|≤E) (hE : E≤1) :
    |Real.exp z*(a/G)-1|≤3*r+2*E := by
  have he := Real.abs_exp_sub_one_le (hz.trans hE)
  have hexp : Real.exp z≤3 := by
    have h := le_abs_self (Real.exp z-1)
    linarith
  have heprod := abs_add_le (Real.exp z*(a/G-1)) (Real.exp z-1)
  have hEq : Real.exp z*(a/G)-1=Real.exp z*(a/G-1)+(Real.exp z-1) := by ring
  rw [hEq]
  apply heprod.trans
  rw [abs_mul,abs_of_pos (Real.exp_pos z)]
  exact add_le_add (mul_le_mul hexp (relative_gaussian_error_le a G r hG hr ha)
    (abs_nonneg _) (by norm_num : (0 : ℝ)≤3))
      (he.trans (mul_le_mul_of_nonneg_left hz (by norm_num)))

theorem gaussian_restoration_absolute_error (H H0 a G z E r : ℝ)
    (hH0 : 0≤H0) (hG : 1≤G) (hr : 0≤r) (ha : |a-G|≤r) (hz : |z|≤E) (hE : E≤1)
    (hrestore : H=H0*Real.exp z*(a/G)) :
    |H-H0|≤H0*(3*r+2*E) := by
  have he : H-H0=H0*(Real.exp z*(a/G)-1) := by rw [hrestore]; ring
  rw [he,abs_mul,abs_of_nonneg hH0]
  exact mul_le_mul_of_nonneg_left (relative_exponential_product_error a G z E r hG hr ha hz hE) hH0

end TournamentHamiltonian
