import Cube.Simple.Basic

namespace Cube.Simple.Expr

partial def betaReduce (expr : Expr) : Expr :=
  match expr with
  | .app fn arg =>
    let newArg := betaReduce arg
    match fn with
    | .lam _ body =>
      let newBody := body.instantiate arg
      betaReduce newBody
    | _ => .app (betaReduce fn) newArg
  | .lam t body => .lam t (betaReduce body)
  | .bvar idx => .bvar idx
  | .fvar fvarId => .fvar fvarId
  | .const name => .const name

#eval betaReduce [stlc| (λ f : ℕ → ℕ. f 12) (λ x : ℕ. x)]
#eval betaReduce [stlc| (λ f : ℕ → ℕ. g (f 12)) (λ x : ℕ. x)]

def etaExpand (expr : Expr) (ty : Ty) : Expr :=
  -- TODO: Optimize, etaExpand is called from betaEtaNormalForm
  -- which already computes lamLen and tyLen
  let lamLen := lambdaLength expr
  let tyLen := typeLength ty
  if lamLen == tyLen then
    expr
  else
    let relevantTy := getNthType! ty (tyLen - lamLen)
    go expr relevantTy
where
  go (expr : Expr) (relevantTy : Ty) : Expr :=
    match expr with
    | .lam t body => .lam t (go body relevantTy)
    | _ => .lam relevantTy (.app (raiseIndices expr 1) (.bvar 0))

def betaEtaNormalForm (expr : Expr) (ty : Ty) : Expr :=
  let betaNormalForm := betaReduce expr
  let n := lambdaLength expr
  let m := typeLength ty
  let len := m - n
  -- TODO: Optimize, we can also eta expand m - n at once
  len.fold (init := betaNormalForm) (fun _ expr => etaExpand expr ty)


end Cube.Simple.Expr
