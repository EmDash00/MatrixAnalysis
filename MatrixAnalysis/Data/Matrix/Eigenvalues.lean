import Mathlib
import Mathlib.Data.Matrix.Mul
import MatrixAnalysis.Data.Matrix.Basic

namespace MatrixAnalysis

open Matrix

def is_eigenvalue {n:ℕ} (A : ℂ^{n²}) (s : ℂ) :=
  ∃ v : ℂ^{n}, v ≠ 0 ∧ A *ᵥ v = s • v

def is_eigen_pair
  {n:ℕ} (A : ℂ^{n²}) (s : ℂ) (v : ℂ^{n}) :=
  v ≠ 0 ∧ A *ᵥ v = s • v

def spectrum {n:ℕ} (A : ℂ^{n²}) := { s : ℂ | is_eigenvalue A s}

/- The next two theorems are straightforward helpers for certain proof situations. -/

@[simp]
theorem is_eigenvector_for_simp
  {n:ℕ} {A : ℂ^{n²}} {s : ℂ} {v : ℂ^{n}}
  : is_eigen_pair A s v ↔ v ≠ 0 ∧ A *ᵥ v = s • v := by
    rw[is_eigen_pair]

#print  is_eigenvector_for_simp

theorem eigen_value_from_pair
  {n:ℕ} (A : ℂ^{n²}) (s : ℂ) (v : ℂ^{n})
  : is_eigen_pair A s v → is_eigenvalue A s := by
    intro h
    use v
    simp_all

end MatrixAnalysis
