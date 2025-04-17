import Mathlib

notation α "^{" n "}" => Fin n → α
notation α "^{" m","n "}" => Matrix (Fin m) (Fin n) α
notation α "^{" n"²" "}" => Matrix (Fin n) (Fin n) α

theorem matrix_eq_all {n m: ℕ} {A B : ℂ^{m,n}}
  : A = B ↔ ∀ i j, A i j = B i j := by
  constructor
  . intro h i j
    exact congrFun (congrFun h i) j
  . exact Matrix.ext

theorem matrix_neq_exists {n m : ℕ} {A B : ℂ^{n,m}}
  : A ≠ B ↔ ∃ i j, A i j ≠ B i j := by
  simp[matrix_eq_all]
