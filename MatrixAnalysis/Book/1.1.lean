import Mathlib
import MatrixAnalysis.Data.Polynomial.Basic
import MatrixAnalysis.Data.Matrix.Basic
import MatrixAnalysis.Data.Matrix.Eigenvalues
import MatrixAnalysis.Data.Matrix.Determinant


open MatrixAnalysis
open Matrix

set_option maxHeartbeats 100000000

/- # 1.1 The eigenvalue-eigenvector equation

We define a property to capture the definition of an eigenvalue of a square matrix. It asserts the existence of an non-zero vector that solves Av = λv. We use s instead of λ, since in Lean λ means something else.

One tricky thing to keep in mind is that in Lean A*v is matrix multiplication, whereas s•v is scalar multiplication of v by s. This will be a bit inconvenient, but we'll work around it (see the discussion below about polynomials). ∀

We also define a property to capture when s and v are eigenvalue, eigenvector pairs. And we define the spectrum of a matrix to be the set of all eigenvalues. All of these definitiions can be found in `MatrixAnalysis.Data.Matrix.Eigenvalues` -/

/- # Exercise (p35): Every non-zero scalar multiple of an eigenvector is an eigenvector.

Proving this amounts to unfolding the definitions, and then refolding with an arbitrary scalar multiple. -/

theorem eigenvector_scalar_multiple
  {n:ℕ} (A : ℂ^{n²}) (s : ℂ) (v : ℂ^{n})
  : is_eigen_pair A s v → ∀ (t : ℂ), t ≠ 0 → is_eigen_pair A s (t•v) := by
    intro h t tnz
    simp_all[is_eigen_pair, h, Matrix.mulVec_smul]
    rw[smul_comm]


/- # Example (p36): Verify the eigenvalues of a given matrix.

In the example below, we wish to start with a specific 2 × 2 matrix A and verify it has certain eigenvalue/eigenvector pairs. In the proofs, we need to show the eigenvalue equation holds, and show that the eigenvectors we choose are non-zero. The latter bit is harder than it should be. Two theorems we put in Data.Matrix.Basic can be used as helpers.
  - matrix_eq_all
  - matrix_neq_exists
These are both about the equality of two matrices. The first one says that two matrices are equal if they are equal at all locations. Now we can do the examples for a specific matrix. -/

namespace Example

  def A : Matrix (Fin 2) (Fin 2) ℂ := !![7,-2; 4,1]

  example : is_eigen_pair A 3 ![1, 2] := by
    unfold is_eigen_pair
    constructor
    . simp
    . funext i
      fin_cases i <;> rw[A] <;> norm_num

  example : is_eigen_pair A 5 ![1, 1] := by
    constructor
    . simp
    . funext i
      fin_cases i <;> rw[A] <;> norm_num


end Example

/- # Polynomials acting on matrices

Given a polynomial p, there is a simple relationship between the eigenvalues of A and p(A): if s is an eigenvalue of A, then p(s) is an eigenvalue of p(A).

To get to this theorem, we have to either use Mathlib's polynomials or invent our own. Here, we take the latter approach, coming up with a very simple version of polynomials that hopefully work for most purposes in this book. We simply define a polynomial as function taking degrees i to coefficients pᵢ. The definition is in

  import MatrixAnalysis.Data.Polynomials.Basic

Then we define what it means to apply a polynomial to a given element. Note that in the code below, the element we apply a polynomial to can be from any ring. This allows us to use our polynomials with scalars and matrices, as required in this book. -/

/- Before we state the theorem, we first prove a helper theorem that describes the relationship between the eigenvalues of s of A and the eigenvalues sᵏ of Aᵏ. -/

theorem eig_eqn_pow
  {n : ℕ} {A : ℂ^{n²}} {s : ℂ} {v : ℂ^{n}} (k : ℕ)
  : is_eigen_pair A s v → A^k *ᵥ v = s^k • v := by
    intro h
    unfold is_eigen_pair at h
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        A ^ (k + 1) *ᵥ v  = (A * A ^ k) *ᵥ v  := by rw [pow_succ']
        _ = A *ᵥ (A ^ k *ᵥ v)      := by rw [mulVec_mulVec]
        _ = A *ᵥ (s ^ k • v)       := by rw [ih]
        _ = s ^ k • (A *ᵥ v)       := by rw [mulVec_smul]
        _ = s ^ k • (s • v)        := by rw [h.right]
        _ = (s ^ k * s) • v        := by rw [smul_smul]

/- Next, we need to address a bit of a problem. When using a matrix in the definition of apply, above, we have the expression (p k) * (x^k.val) where x is a matrix. But we haven't defined multiplication * for a scalar times a matrix, only scalar multiplication • of a scalar times a matrix. And we can't change the definition to use •, because we might want to use the polynomial with other types. We can fix this by declaring an instances of HMul for scalars and matrices. Since we will just want to simplify this out in proofs, we add it to the simplifier so we can (hopefully) forget about it. -/

@[simp]
instance hmul_smul_inst {n m:ℕ} :
  HMul ℂ (Matrix (Fin n) (Fin m) ℂ) (Matrix (Fin n) (Fin m) ℂ)
  := ⟨ λ s A => s • A ⟩

/- # Theorem 1.16 : Eigenvalues of a Polynomial

Now we can state the theorem about eigenvalues of polynomials of matrices. Note that p.apply A would not typecheck without the above instance. -/

theorem mulVec_sum {m n α β : Type*} [NonUnitalSemiring α] [Fintype m] [Fintype n]
  (s : Finset β) (f : β → Matrix m n α) (x : n → α) :
    (∑ a ∈ s, f a) *ᵥ x = ∑ a ∈ s, f a *ᵥ x :=
  map_sum (mulVec.addMonoidHomLeft x) f s

theorem eigen_pair_of_poly {n m:ℕ} {A : ℂ^{n²}}
                            {s : ℂ}
                            {v : ℂ^{n}}
                            (p : Poly ℂ m)
  : is_eigen_pair A s v → is_eigen_pair (p.apply A) (p.apply s) v  := by

    intro h
    simp_all only[is_eigen_pair, Poly.apply]

    constructor
    . exact h.left

    . simp only[mulVec_sum, h]  -- Distribute *ᵥ and use eigenvector property
      rw [Finset.sum_smul]       -- Bring summation outside scalar multiplication
      apply Finset.sum_congr rfl -- sums are equal if jjterms are equal
      intro k _
      rw[←smul_smul]
      simp[←eig_eqn_pow k h, smul_mulVec_assoc]



/- We can also define the eigenvalue property without the eigenvector, for convenience. -/

theorem eigen_val_of_poly {n m:ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
                            {s : ℂ}
                            (p : Poly ℂ m)
  : is_eigenvalue A s → is_eigenvalue (p.apply A) (p.apply s) := by
    intro ⟨v, hv⟩
    refine eigen_value_from_pair (p.apply A) (p.apply s) v ?_
    apply eigen_pair_of_poly
    exact hv

/- # Example (p36) : Example polynomial of a matrix

Using our new tactic, we can prove a simple concrete example. -/

example {A : Matrix (Fin 2) (Fin 2) ℂ}
  : is_eigenvalue A (-1) → is_eigenvalue A 2
  → (is_eigenvalue (A^2) 1 ∧ is_eigenvalue (A^2) 4) := by

    intro h1 h2
    let p : Poly ℂ 3 := ![0,0,1]
    have g1 : p.apply A = A^2 := by small_poly p

    apply And.intro

    . have g0 := eigen_val_of_poly p h1
      have g2 : p.apply (-1) = 1 := by small_poly p
      simp_all[g1,g2]

    . have g0 := eigen_val_of_poly p h2
      have g2 : p.apply 2 = 4 := by
        small_poly p
        ring
      simp_all[g1,g2]

/- # Exercise (p36) : The eigenvalues of a diagonal matrix -/

@[simp]
def MatrixRow
  {n m : ℕ} (A : ℂ^{n,m}) (k : Fin n)
  : Matrix (Fin 1) (Fin m) ℂ
  := Matrix.of (λ _ j => A k j)

@[simp]
def MatrixCol {n m : ℕ} (A : ℂ^{n,m}) (k : Fin m) : ℂ^{n,1}
  := Matrix.of (λ i _ => A i k)

@[simp]
def std_basis (n: ℕ) (k : Fin n) : ℂ^{n} := fun i ↦ if i = k then 1 else 0

example {n : ℕ} (k : Fin n)
  : MatrixRow (1 : ℂ^{n²}) k = (MatrixCol 1 k).transpose := by
  simp[MatrixRow, MatrixCol, Matrix.transpose, Matrix.one_apply, eq_comm]

-- 1. Define the conversion function
@[simp]
def Matrix.toVec {R : Type*} [Semiring R] {n : ℕ} (A : R^{n, 1}) : R^{n} :=
  fun j => A j 0  -- Extract the single row

-- 2. Create the coercion instance
instance {R : Type*} [Semiring R] {n : ℕ} : Coe (R^{n,1}) (Fin n → R) where
  coe := Matrix.toVec

theorem std_basis_col_id {n:ℕ} {k:(Fin n)}
  : (MatrixCol (1 : ℂ^{n²}) k).toVec = std_basis n k := by
  unfold std_basis Matrix.toVec
  simp[MatrixCol,Matrix.one_apply,Matrix.transpose]

theorem mul_std_basis
   {n:ℕ} {A : ℂ^{n²}} {k : Fin n}
   : A *ᵥ std_basis n k = (MatrixCol A k).toVec := by
   simp[←std_basis_col_id,col]
   funext i
   unfold Matrix.toVec
   simp [Matrix.mulVec, dotProduct]
   change ∑ x, (A i x) * (if x = k then 1 else 0) = A i k
   simp [Finset.sum_ite]


lemma zero_vector {n : ℕ} {v : ℂ^{n}} : v = 0 ↔ ∀ i, v i = 0 := by
  apply Iff.intro
  . intro hmp i
    by_contra h_vi_nonzero
    simp only[←ne_eq] at h_vi_nonzero
    have : v i = 0 := by
      apply congr_fun
      exact hmp
    contradiction
  . intro hmpr
    ext i
    simp
    exact hmpr i

lemma std_basis_nonzero {n : ℕ} {i : Fin n} : std_basis n i ≠ 0 := by
  intro h
  simp[zero_vector] at h


theorem diag_eig_sys
  {n:ℕ} (A : ℂ^{n²})
  : Matrix.IsDiag A → ∀ i , is_eigen_pair A (A i i) (std_basis n i) := by
  intro hdiag i
  constructor
  . exact std_basis_nonzero

  . simp[mul_std_basis]     -- show standard basis vector is an eigenvector
    ext x : 1
    simp
    split
    next h =>
      subst h
      rfl
    next h =>
      apply hdiag
      simp[ne_eq, not_false_eq_true]
      exact h

/- # Observation 1.17 : Having a zero eigenvalue is equivalent to being singular -/

def singular
  {n:ℕ} (A : ℂ^{n²})
  := ∃ x : ℂ^{n}, x ≠ 0 ∧ A *ᵥ x = 0

def nonsingular
  {n:ℕ} (A : ℂ^{n²}) := ∀ x : ℂ^{n}, A *ᵥ x = 0 ↔ x = 0

theorem nonsingular_is_not_singular
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
  : (¬singular A) ↔ (nonsingular A) := by
  simp[singular,nonsingular]
  constructor
  . intro h x
    apply Iff.intro
    . intro hmp
      exact not_imp_not.mp (h x) hmp
    . intro hmpr
      rw[hmpr]
      exact mulVec_zero _
  . intro h x hx hna
    exact hx ((h x).mp hna)

theorem eig_zero_to_non_sing
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
  : is_eigenvalue A 0 ↔ singular A := by
    constructor
    . intro ⟨v, ⟨he, hz⟩⟩
      simp at hz
      use v
    . intro ⟨ v, ⟨ hz, hv ⟩ ⟩
      exact ⟨ v, ⟨ hz, by simp; exact hv ⟩  ⟩

/- # Exercise 1 : Eigenvalues of the inverse -/

lemma mul_both_sides {n:ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} {u v: Matrix (Fin n) (Fin 1) ℂ}
 : A * u = v → B * A * u = B * v := by
   intro h
   rw[←h,Matrix.mul_assoc]

theorem eigen_inv
  {n:ℕ} {A: ℂ^{n²}} [hia : Invertible A] {s:ℂ}
  : is_eigenvalue A s → is_eigenvalue A⁻¹ s⁻¹ := by
  intro ⟨ v, ⟨ v_nonzero, hv ⟩ ⟩
  have snz : s ≠ 0 := by
    intro h
    rw[h,zero_smul] at hv
    have h1 : A⁻¹ *ᵥ A *ᵥ v = A⁻¹ *ᵥ (0 : ℂ^{n}) := by rw[hv]
    have h2 : A⁻¹ *ᵥ (0 : ℂ^{n}) = 0 := by exact Matrix.mulVec_zero A⁻¹
    rw[h2] at h1
    simp at h1
    contradiction
  use v
  constructor
  . exact v_nonzero
  . have : A⁻¹ *ᵥ A *ᵥ v = A⁻¹ *ᵥ (s • v) := by rw[hv]
    have : v = s • (A⁻¹ *ᵥ v) := by
      simp[mulVec_smul] at this
      exact this

    have : s⁻¹ • v = (A⁻¹ *ᵥ v) := by exact (inv_smul_eq_iff₀ snz).mpr this
    exact id (Eq.symm this)

/- # Exercise 2 : If the sum of each row is 1, then 1 is an eigenvalue -/

theorem sum_rows_one {n:ℕ} {A : ℂ^{(n + 1)²}}
  : (∀ i : Fin (n + 1), ∑ j : Fin (n + 1), A i j = 1) → is_eigenvalue A 1 := by
    intro hi
    use (λ _ => (1 : ℂ))
    constructor
    . simp[zero_vector]
    . ext i
      simp[mulVec, dotProduct]
      exact hi i

/- # Exercise 3 : Todo -/

/- # Exercise 4 : Todo -/

/- # Exercise 5 : Idempotent Matrices and their eigenvalues -/

example : (2 • ![3, 4, 5]) 0 = 6 := by
  simp [Matrix.smul_cons]  -- Proof that first entry is 2*3=6

lemma smul_left_inj {n: ℕ} {a b : ℂ} {v : ℂ^{n}} (hnz : v ≠ 0)
  : a • v = b • v ↔ a = b := by
  apply Iff.intro
  . intro hmp
    have : ∃ i, v i ≠ 0 := by
      by_contra not_h_nonzero
      push_neg at not_h_nonzero
      have : v = 0 := by
        ext i
        exact not_h_nonzero i
      contradiction

    obtain ⟨i, hi⟩ := this

    have : (a • v) i = (b • v) i := by apply congr_fun hmp
    simp only [Pi.smul_apply, smul_eq_mul] at this
    field_simp[hi] at this
    exact this

  . intro hmpr
    rw[hmpr]


  --rw[matrix_neq_exists] at hnz
  --have ⟨i, ⟨ j, hij ⟩ ⟩ := hnz
  --have : j = 0 := by exact Fin.fin_one_eq_zero j
  --rw[this] at hij
  --have h_eq : (a • v) i 0 = (b • v) i 0 := by rw [h]
  --simp [Matrix.smul_apply, hij] at h_eq
  --apply Or.elim h_eq
  --. exact id
  --. intro hv
    --simp_all

theorem idempotent_zero_one {n:ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (s : ℂ)
  : A*A = A → is_eigenvalue A s → (s = 0 ∨ s = 1) := by

  intro h ha
  apply eq_zero_or_one_of_sq_eq_self
  rw[pow_two]

  let p : Poly ℂ 3 := ![0,0,1]
  obtain ⟨ v, ⟨ hnzv, hv ⟩ ⟩ := ha
  have hep : is_eigen_pair A s v := And.intro hnzv hv
  apply eigen_pair_of_poly p at hep
  have h1 : p.apply A = A*A  := by small_poly p; exact pow_two A
  have h2 : p.apply s = s*s  := by small_poly p; exact pow_two s
  simp[h1,h2] at hep
  obtain ⟨_, h4 ⟩ := hep
  simp[h,hv] at h4
  apply Eq.symm
  exact (smul_left_inj hnzv).mp h4


/- # Exercise 6 : Nilpotent Matrices and their eigenvalues -/

def monomial {R: Type*} [Ring R] (q:ℕ) : Poly R (q+1) :=
  λ i => if i < q then 0 else 1

lemma eigenval_of_power {n:ℕ} {A : ℂ^{n²}} {s : ℂ} {v: ℂ^{n}} (q:ℕ)
  : is_eigen_pair A s v → is_eigen_pair (A^q) (s^q) v := by
  intro h
  constructor
  . exact h.left
  . let p : Poly ℂ (q+1) := monomial q

    have h3 : p.apply A = A^q := by -- TODO: this have and the next
      unfold p Poly.apply monomial  -- should be done via a lemma
      simp[Fin.sum_univ_castSucc]
      have : ∀ x : Fin q, x.castSucc < Fin.last q := by
        exact fun x ↦ Fin.castSucc_lt_last x
      simp[this]

    have h4 : p.apply s = s^q := by
      unfold p Poly.apply monomial
      simp[Fin.sum_univ_castSucc]
      have : ∀ x : Fin q, x.castSucc < Fin.last q := by
        exact fun x ↦ Fin.castSucc_lt_last x
      simp[this]

    apply eigen_pair_of_poly p at h
    simp[p,h3,h4] at h

    exact h.right

theorem nilpotent_zero_one {n:ℕ} {A : ℂ^{n²}} (s : ℂ)
  : (∃ q : ℕ , A^q = 0) → is_eigenvalue A s → s = 0 := by
    intro ⟨ q, hq ⟩ hs
    obtain ⟨ v, ⟨ hnzv, hv ⟩ ⟩ := hs

    have hep : is_eigen_pair A s v := And.intro hnzv hv
    apply eigenval_of_power q at hep

    obtain ⟨ h3, h4 ⟩ := hep
    have : (0 : ℂ^{n²}) *ᵥ v = (0 : ℂ) • v := by simp
    rw[hq, this] at h4
    have : s^q = 0 := by exact ((smul_left_inj hnzv).mp h4).symm
    exact pow_eq_zero this

/- # Exercise 7 : Todo -/

/- # Exercise 8 : Infinite dimensional example with no eigenvalues -/
-- Maybe this one is out of scope for this project?

/- # Exercise 9 :Todo -/
