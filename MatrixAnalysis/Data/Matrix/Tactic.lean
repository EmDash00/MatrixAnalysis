import Lean
import Lean.Expr
import Lean.Meta

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection

open Lean Elab Term Meta Matrix


def add_ten (x : Nat) : Nat :=
  x + 10

simproc reduceFoo (add_ten _) :=
  fun e => do
    unless e.isAppOfArity ``add_ten 1 do
      return .continue
    /- `Nat.fromExpr?` tries to convert an expression into a `Nat` value -/
    let some n ← Nat.fromExpr? e.appArg!
      | return .continue
    return .done { expr := Lean.mkNatLit (n+10) }

example (x : ℕ) : x + add_ten 2 = 12 + x := by
  simp +arith


def buildMatrix (α : Expr) (entries : Array (Array Expr)) : MetaM Expr := do
  -- Get the dimensions
  let m := entries.size
  let n := if m > 0 then entries[0]!.size else 0

  let finN ← mkAppM ``Fin #[mkNatLit n] -- Fin n
  let finN_to_α := mkForall `_ .default finN α -- Fin n → α

  -- Declare matrix : Fin 0 → Fin n → α
  let mut matrix ← mkAppOptM ``Matrix.vecEmpty #[finN_to_α]

  for row in entries.reverse do
    -- Declare rowExpr: Fin 0 → α
    let mut rowExpr ← mkAppOptM ``Matrix.vecEmpty #[α]

    -- Append each entry in the row
    for elem in row.reverse do
      rowExpr ← mkAppM ``Matrix.vecCons #[elem, rowExpr]

    matrix ← mkAppM ``Matrix.vecCons #[rowExpr, matrix]
  return matrix


-- Test case for a 2x3 matrix
def testBuildMatrix : MetaM Unit := do
  -- Create test data [[1, 2], [3, 4], [5, 6]]
  let entries : Array (Array Expr) := #[
    #[mkNatLit 1, mkNatLit 2],
    #[mkNatLit 3, mkNatLit 4],
    #[mkNatLit 5, mkNatLit 6]
  ]

  -- Build the matrix
  let matrix ← buildMatrix (mkConst ``Nat) entries

  -- Inspect results
  logInfo m!"Built matrix expression: {matrix}"

def destructureRow (n : ℕ) (rowExpr : Expr) : MetaM (Array Expr) := do
  match n with
    | Nat.succ nPredecessor =>
      match rowExpr.getAppFnArgs with
        | (``Matrix.vecCons, #[_, _, entryExpr, tailExpr]) =>
          let tail ← destructureRow nPredecessor tailExpr
          return tail.push entryExpr
        | _ => throwError ""
    | Nat.zero => return #[]

def getVectorLength? (vectorExpr: Expr) : MetaM (Option ℕ) := do
  let rowTypeExpr ← inferType vectorExpr
  match rowTypeExpr with
    | .forallE _ (.app (.const ``Fin _) (.app (.const ``Nat.succ _) nExpr) ) _ _ =>
      let some n ← getNatValue? nExpr | failure
      return some (n + 1)
    | _ => return none

-- Given Matrix.vecCons Fin n → α, _, head, tail, extracts n and α
def getMatrixType (matrixExpr : Expr) : MetaM (Option (ℕ × ℕ × Expr)) := do
  logInfo m!"Inferirng vecCons type of: {matrixExpr.getAppFnArgs}"
  match matrixExpr.getAppFnArgs with
  | (``Matrix.vecCons, #[matrixTypeExpr, _, rowExpr, _]) =>
    match matrixTypeExpr with
      | .forallE _ (.app (.const ``Fin _) nExpr) elementTypeExpr _ =>
        let some m ← getNatValue? nExpr | failure
        let some n ← getVectorLength? rowExpr | failure
        return some (m, n, elementTypeExpr)
      | _ => return none
  | _ => return none

def destructureMatrix' (m n : ℕ) (matrixExpr : Expr) : MetaM (Array Expr) := do
  match m with
    | Nat.succ mPredecessor =>
     match matrixExpr.getAppFnArgs with
      | (``Matrix.vecCons, #[_, _, rowExpr, tailExpr]) =>
        let row ← destructureRow n rowExpr
        logInfo m!"Row: {row}"
        let tail ← destructureMatrix' mPredecessor n tailExpr
        return tail ++ row
      | _ => throwError "DIE POTATO. Noooooooooo. -- asdf movie N for some N ∈ ℕ"
    | Nat.zero => return #[]

def destructureMatrix (matrixExpr : Expr) : MetaM (Expr × ℕ × ℕ × Array Expr) := do
  let some (m, n, elemType) ← getMatrixType matrixExpr | failure
  logInfo m!"dims: {m}, elemType: {elemType}"
  let elemsArray ← destructureMatrix' m n matrixExpr
  return (elemType, m, n, elemsArray.reverse)

def transposeMatrixExpr (matrixExpr : Expr) : MetaM Expr := sorry

-- Adds this as a rule to the simplifier.
-- can be called as simp[Matrix.of_transpose_of_fin]
-- Tells the simplifier to apply this rule on things of the form Matrix.transpose _
simproc Matrix.of_transpose_of_fin (Matrix.transposeᵣ _) :=
  fun e => do
    -- Check if this is a transpose....
    unless e.isAppOfArity ``Matrix.transposeᵣ 4 do
      return .continue

    -- Get the argument (the matrix being transposed)
    let e := e.appArg!.consumeMData
    -- First try to handle direct Matrix.of case
    if e.isAppOfArity ``Matrix.of 3 then
      return .done { expr := e }

    -- Some weird what the hell stuff goin' on idk
    -- Handle DFunLike.coe
    else if e.isAppOfArity ``DFunLike.coe 6 then
      let matrixExpr := e.getArg! 5

      unless matrixExpr.isAppOfArity ``Matrix.vecCons 4 do
        return .continue

      logInfo m!"Original matrix {matrixExpr}"
      let a ← destructureMatrix matrixExpr
      logInfo m!"Destructured a: {a}"
      -- Transpose here?

      return .done { expr := e }
    return .continue

def A := !![1, 2, 3; 4, 5, 6; 7, 8, 9]

example : Aᵀ = !![1, 4, 7; 2, 5, 8; 3, 6, 9] := by
  simp only[A, ←transposeᵣ_eq]
  simp only[Matrix.of_transpose_of_fin]



