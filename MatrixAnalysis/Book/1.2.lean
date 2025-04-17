import Mathlib
import MatrixAnalysis.Data.Polynomial.Basic
import MatrixAnalysis.Data.Matrix.Eigenvalues

namespace MatrixAnalysis

/- The characteristic polynomial of a matrix A is |sI-A|. -/

def char_poly {n : ℕ} (A : ℂ^{n²}) (s : ℂ) := (s•1 - A).det

/- # Observation 1.2.4a
   The characteristic polynomial is degree (at most) n -/

theorem char_poly_coeff {n : ℕ} {A : ℂ^{n²}} {s : ℂ}
  : ∃ p : Poly ℂ n, p.apply s = char_poly A s := sorry

/- # Observation 1.2.4b
   The roots of the characteristic polynomial form the spectrum of A -/

theorem cp_to_spectrum {n : ℕ} {A : ℂ^{n²}}
  : spectrum A = { s | char_poly A s = 0 } := by
  simp_all[spectrum,char_poly,is_eigenvalue]
  apply Set.eq_of_subset_of_subset
  . intro s hs
    simp_all
    obtain ⟨ v, ⟨ hnz, hv ⟩ ⟩ := hs
    sorry
  . intro s hs
    simp_all
    sorry

end MatrixAnalysis
