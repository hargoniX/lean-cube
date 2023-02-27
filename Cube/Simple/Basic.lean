import Cube.Util
import Cube.Context

import Lean

open Lean

namespace Cube.Simple

inductive Ty where
| nat
| fun (pre : Ty) (image : Ty)
deriving Repr, DecidableEq, Inhabited, Hashable

def Ty.telescope (ty : Ty) : Array Ty :=
  go ty #[]
where
  go (ty : Ty) (acc : Array Ty) :=
    match ty with
    | .nat => acc.push .nat
    | .fun t1 t2 => go t2 (acc.push t1)

def Ty.ofTelescope (telescope : Array Ty) : Ty :=
  telescope[:telescope.size - 1].foldr (init := telescope[telescope.size - 1]!) (fun arg acc => .fun arg acc)

inductive Ast where
| var (name : String)
| const (name : String)
| lam (var : String) (ty : Ty) (body : Ast)
| app (func : Ast) (arg : Ast)
deriving Repr

inductive Expr where
| bvar (idx : Nat)
| fvar (name : FVarId)
| lam (orig : String) (ty : Ty) (body : Expr)
| const (name : String)
| app (func : Expr) (arg : Expr)
deriving Repr, DecidableEq, Inhabited, Hashable

abbrev TranslationEnv := List String

def Ast.toExpr : Ast → TranslationEnv → Expr
| var name, vs =>
  match vs.findIdx? (name = ·) with
  | some idx => .bvar idx
  | none => .fvar ⟨name, 0⟩
| const name, _ => .const name
| app func arg, vs => .app (toExpr func vs) (toExpr arg vs)
| lam x ty body, vs => .lam x ty (toExpr body <| x :: vs)

def Expr.toAst : Expr → TranslationEnv → Option Ast
| bvar idx, vs => do
  let x ← vs[idx]?
  return .var x
| fvar fvarId, _ => some <| .var fvarId.name
| lam name ty body, vs => do
    let body ← toAst body <| name :: vs
    return .lam name ty body
| const name, _ => some <| .const name
| .app func arg, vs => do
    let funcAst ← toAst func vs
    let argAst ← toAst arg vs
    return .app funcAst argAst

declare_syntax_cat stlc
declare_syntax_cat stlcTy
syntax "ℕ" : stlcTy
syntax stlcTy "→" stlcTy : stlcTy
syntax "(" stlcTy ")" : stlcTy

syntax ident : stlc
syntax num : stlc
syntax stlc:10 stlc:11 : stlc
syntax "λ " ident ":" stlcTy " . " stlc : stlc
syntax "(" stlc ")" : stlc

syntax "[stlcTy|" stlcTy "]" : term
syntax "[stlcA|" stlc "]" : term
syntax "[stlc|" stlc "]" : term
#check String.Pos
macro_rules
  | `([stlcTy| ℕ]) => `(Ty.nat)
  | `([stlcTy| $a → $b]) => `(Ty.fun [stlcTy| $a] [stlcTy| $b])
  | `([stlcTy| ($x)]) => `([stlcTy| $x])

  | `([stlcA| $x:ident]) =>
    let strId := x.getId.toString
    let first := strId.get ⟨0⟩
    if first.isUpper then
      `(Ast.const $(quote <| strId))
    else
      `(Ast.var $(quote strId))
  | `([stlcA| $n:num]) => `(Ast.const $(quote n.getNat.repr))
  | `([stlcA| λ $x : $ty . $b]) => `(Ast.lam $(quote x.getId.toString) [stlcTy| $ty]  [stlcA| $b])
  | `([stlcA| $f $x]) => `(Ast.app [stlcA| $f] [stlcA| $x])
  | `([stlcA| ($x)]) => `([stlcA| $x])
  | `([stlc| $t ]) => `(Ast.toExpr [stlcA| $t] [])

#eval [stlcTy| (ℕ → ℕ → ℕ) → ℕ → ℕ] == (Ty.ofTelescope [stlcTy| (ℕ → ℕ → ℕ) → ℕ → ℕ].telescope)

theorem Ast.toExpr_inv_toAst (a : Ast) (xs : List String) : Expr.toAst (Ast.toExpr a xs) xs = some a := by
  induction a generalizing xs with
  | var name =>
    simp only [Ast.toExpr]
    split
    case var.h_1 idx h =>
      simp only [Expr.toAst,Bind.bind, Option.bind, Pure.pure]
      have h2 := List.findIdx?_bounds h
      simp only [getElem?, h2, congrArg, List.getElem_eq_get, Option.some.injEq, var.injEq]
      have h3 := List.findIdx?_prop h
      simp [of_decide_eq_true h3]
    case var.h_2 => simp [Expr.toAst]
  | const name => simp[Expr.toAst, Ast.toExpr]
  | lam var ty body ih =>
    simp[Expr.toAst, Ast.toExpr, Bind.bind, Option.bind, Pure.pure, ih]
  | app func arg fih xih =>
    simp[Expr.toAst, Ast.toExpr, Bind.bind, Option.bind, fih, xih, Pure.pure]

theorem Ast.macro_correct (a : Ast) : Expr.toAst (Ast.toExpr a []) [] = some a := toExpr_inv_toAst a []

#eval [stlc| λ x : ℕ . (λ y : ℕ → ℕ . (free y) x)]

namespace Expr

-- From I'm not a number I'm a free variable
def abstract (expr : Expr) (target : FVarId) (idx : Nat := 0): Expr :=
  match expr with
  | .fvar name =>
    if target = name then
      .bvar idx
    else
      .fvar name
  | .app fn arg => .app (abstract fn target idx) (abstract arg target idx )
  | .lam orig ty body => .lam orig ty (abstract body target (idx + 1))
  | .const name => .const name
  | .bvar idx => .bvar idx

def instantiate (expr : Expr) (image : Expr) (targetIdx : Nat := 0) : Expr :=
  match expr with
  | .bvar idx =>
    if idx = targetIdx then
      image
    else
      .bvar idx
  | .app fn arg => .app (instantiate fn image targetIdx ) (instantiate arg image targetIdx )
  | .lam orig ty body => .lam orig ty (instantiate body image (targetIdx + 1))
  | .fvar name => .fvar name
  | .const name => .const name

def substitute (expr : Expr) (fvarId : FVarId) (image : Expr) : Expr :=
  expr.abstract fvarId |>.instantiate image

abbrev Context := Cube.Context Ty
abbrev Env := Cube.Env Ty
abbrev Substitution := Cube.Substitution Expr
abbrev SimpleT (m : Type → Type) := ReaderT Env (StateT Context (ExceptT String m))
abbrev SimpleM := SimpleT Id

def getCtx : SimpleM Context := do return (← get)
def getEnv : SimpleM Env := do return (← read)
def SimpleM.run' (x : SimpleM α) (env : Env) (ctx : Context) : Except String α :=
  x.run env |>.run' ctx

partial def infer (expr : Expr) : SimpleM Ty := do
  match h:expr with
  | .bvar idx => throw s!"Unbound variable index: {idx}"
  | .app fn arg => 
      if let .fun t1 t2 ← infer fn then
        let t3 ← infer arg
        if t1 = t3 then
          return t2
        else
          throw s!"Arg type mismatch in {repr expr}, argument should have type {repr t1} but has type {repr t3}"
      else
        throw s!"Function type mismatch in {repr expr}, function should have function type"
  | .lam _ t1 body =>
    let newFVar := FVar.fresh (← getCtx)
    let newBody := body.instantiate (.fvar newFVar)
    let ctx ← getCtx
    modify (fun ctx => ctx.insert newFVar t1)
    try
      let t2 ← infer newBody
      return .fun t1 t2
    finally
      set ctx
  | .fvar fvarId =>
    if let some typ := (← getCtx).find? fvarId then
      return typ
    else
      throw s!"FVarId: {repr fvarId} not found in context"
  | .const name => 
    if let some typ := (← getEnv).find? name then
      return typ
    else
      throw s!"Constant: {name} not found in environment"


partial def betaReduce (expr : Expr) : Expr :=
  match expr with
  | .app fn arg =>
    let newArg := betaReduce arg
    match fn with
    | .lam _ _ body =>
      let newBody := body.instantiate arg
      betaReduce newBody
    | _ => .app (betaReduce fn) newArg
  | .lam orig t body => .lam orig t (betaReduce body)
  | .bvar idx => .bvar idx
  | .fvar fvarId => .fvar fvarId
  | .const name => .const name

#eval betaReduce [stlc| (λ f : ℕ → ℕ. f 12) (λ x : ℕ. x)]
#eval infer [stlc| (λ f : ℕ → ℕ. f 12) (λ x : ℕ. x)] |>.run' (Env.empty.insert "12" .nat) {}
#eval betaReduce [stlc| (λ f : ℕ → ℕ. g (f 12)) (λ x : ℕ. x)]
#eval infer [stlc| (λ f : ℕ → ℕ. g (f 12)) (λ x : ℕ. x)] |>.run' (Env.empty.insert "12" .nat) (Context.empty.insert ⟨"g", 0⟩ [stlcTy| ℕ → ℕ])

def applySubst (subst : Substitution) (expr : Expr) : Expr :=
  subst.toList.foldl (init := expr) (fun expr (fvarId, image) => expr.substitute fvarId image)

def lambdaLength (expr : Expr) (n : Nat := 0) : Nat :=
  match expr with
  | .lam _ _ body => lambdaLength body (n + 1)
  | _ => n

def typeLength (ty : Ty) : Nat :=
  match ty with
  | .nat => 0
  | .fun _ t2 => 1 + typeLength t2

def getNthType! (ty : Ty) (idx : Nat) : Ty :=
  match ty, idx with
  | .nat, 0 => .nat
  | .fun t1 _, 0 => t1
  | .nat, _ + 1 => panic! "Invalid index"
  | .fun _ t2, n + 1 => getNthType! t2 n

-- TODO: I think this is a locally nameless anti pattern?
def raiseIndices (expr : Expr) (n : Nat) : Expr :=
  match expr with
  | .app fn arg => .app (raiseIndices fn n) (raiseIndices arg n)
  | .lam orig t body => .lam orig t (raiseIndices body n)
  | .bvar idx => .bvar (idx + n)
  | .fvar fvarId => .fvar fvarId
  | .const name => .const name

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
    | .lam orig t body => .lam orig t (go body relevantTy)
    | _ => .lam "eta" relevantTy (.app (raiseIndices expr 1) (.bvar 0))

def betaEtaNormalForm (expr : Expr) (ty : Ty) : Expr :=
  let betaNormalForm := betaReduce expr
  let n := lambdaLength expr
  let m := typeLength ty
  let len := m - n
  -- TODO: Optimize, we can also eta expand m - n at once
  len.fold (init := betaNormalForm) (fun _ expr => etaExpand expr ty)

-- TODO: These produce unbounded bvars...
def lambdaTelescope (expr : Expr) : Array Ty × Expr :=
  go expr #[]
where
  go (expr : Expr) (binders : Array Ty) : Array Ty × Expr :=
    match expr with
    | .lam _ t1 body => go body (binders.push t1)
    | _ => (binders, expr)

def abstractArgs (body : Expr) (args : Array Ty) : Expr :=
  args.foldr (init := body) (fun ty body => .lam "abstract" ty body)

def appTelescope (expr : Expr) : Array Expr × Expr :=
  let (revArgs, remainder) := go expr #[]
  (revArgs.reverse, remainder)
where
  go (expr : Expr) (args : Array Expr) : Array Expr × Expr :=
    match expr with
    | .app fn arg => go fn (args.push arg)
    | _ => (args, expr)

def mkApp (fn : Expr) (args : Array Expr) : Expr :=
  args.foldl (init := fn) (fun fn arg => .app fn arg)

#eval mkApp (.const "1") #[.const "2", .const "3"] == [stlc| (1 2) 3] 

-- TODO: Maybe it is worth it to have a seperate data type for βη normalized exprs
namespace Unify

inductive Head where
| const (name : String)
| bvar (idx : Nat)
| fvar (fvarId : FVarId)
deriving DecidableEq, Hashable, Inhabited, Repr

structure BetaEtaNormalExpr where
  binder : Array Ty
  head : Head
  args : Array Expr
deriving DecidableEq, Hashable, Inhabited, Repr

def BetaEtaNormalExpr.ofNormalExpr (expr : Expr) : BetaEtaNormalExpr :=
  let (binder, body) := lambdaTelescope expr
  let (args, head) := appTelescope body
  let head := match head with
    | .const name => .const name
    | .bvar idx => .bvar idx
    | .fvar fvarId => .fvar fvarId
    | _ => panic! "Not in correct normal form"
  { binder, head, args }

def BetaEtaNormalExpr.ofExpr (expr : Expr) (ty : Ty) : BetaEtaNormalExpr :=
  .ofNormalExpr <| betaEtaNormalForm expr ty

def Head.toExpr (head : Head) : Expr :=
  match head with
  | .const name => .const name
  | .bvar idx => .bvar idx
  | .fvar fvarId => .fvar fvarId

def BetaEtaNormalExpr.toExpr (expr : BetaEtaNormalExpr) : Expr :=
  let body := mkApp expr.head.toExpr expr.args
  abstractArgs body expr.binder
 
inductive Flexibility where
| rigid
| flexible

def BetaEtaNormalExpr.flexibility (expr : BetaEtaNormalExpr) : Flexibility :=
  match expr.head with
  | .fvar .. => .flexible
  | _ => .rigid

theorem BetaEtaNormalExpr.False_of_rigid_fvar {expr : BetaEtaNormalExpr} (h1 : expr.flexibility = .rigid) (h2 : expr.head = .fvar fvarId) : False := by
  unfold flexibility at h1
  rw [h2] at h1
  simp at h1

def BetaEtaNormalExpr.headType (expr : BetaEtaNormalExpr) : SimpleM Ty := do
  match expr.head with
  | .const name => return (← read).find! name
  | .fvar fvarId => return (← get).find! fvarId
  | .bvar idx => return expr.binder.get! (expr.binder.size - idx)

def inhabitant (ty : Ty) : Expr :=
  match ty with
  | .nat => .const "0"
  | .fun t1 t2 => .lam "inhab" t1 (inhabitant t2)

def BetaEtaNormalExpr.headFVarId (expr : BetaEtaNormalExpr) (h : expr.flexibility = .flexible) : FVarId :=
  match h2:expr.head with
  | .fvar fvarId => fvarId
  | .bvar idx | .const name => by simp [flexibility, h2] at h

def BetaEtaNormalExpr.applySubst (normalExpr : BetaEtaNormalExpr) (subst : Substitution) : SimpleM BetaEtaNormalExpr := do
  let expr := normalExpr.toExpr
  let substExpr := expr.applySubst subst
  let ty ← infer substExpr
  return BetaEtaNormalExpr.ofExpr substExpr ty 
 
abbrev DisagreementPair := BetaEtaNormalExpr × BetaEtaNormalExpr
abbrev DisagreementSet := HashSet DisagreementPair
structure UnifyNode where
  disagreement : DisagreementSet
  substitution : Substitution

def DisagreementPair.apply (pair : DisagreementPair) (subst : Substitution) : SimpleM DisagreementPair :=
  return (← pair.fst.applySubst subst, ← pair.snd.applySubst subst)

def DisagreementSet.apply (set : DisagreementSet) (subst : Substitution) : SimpleM DisagreementSet :=
  set.foldM (init := HashSet.empty) (fun new pair => do return new.insert (← pair.apply subst))

def UnifyNode.apply (node : UnifyNode) (subst : Substitution) : SimpleM UnifyNode := do
  return ⟨← node.disagreement.apply subst, node.substitution.compose subst⟩

-- https://www21.in.tum.de/teaching/sar/SS20/5.pdf
partial def unify (e1 e2 : Expr) : SimpleM Substitution := do
  let t1 ← infer e1 
  let t2 ← infer e2
  if t1 == t2 then
    let e1Normal := BetaEtaNormalExpr.ofExpr e1 t1
    let e2Normal := BetaEtaNormalExpr.ofExpr e2 t1
    go [⟨HashSet.empty.insert (e1Normal, e2Normal), {}⟩]
  else
    throw "Types don't match"
where
  go (state : List UnifyNode) : SimpleM Substitution := do
    match state with
    | [] => throw "Gave up after exhaustive search"
    | node :: rest =>
      match ← simplify node with
      | none => go rest
      | some (.inl subst) => return subst
      | some (.inr node) =>
        match findMatcherTarget node.disagreement with
        | some (lhs, rhs) =>
          let candidates ← matcher lhs rhs
          let newNodes ← candidates.mapM node.apply
          go <| rest.append newNodes
        | none => go <| rest.append [node]

  simplify (node : UnifyNode) : SimpleM (Option (Substitution ⊕ UnifyNode)) := do
    let mut newSet := HashSet.empty
    let mut newSubst := node.substitution
    for pair in node.disagreement do
      match ← simplifyPair pair newSubst with
      | none => return none
      | some (.inl subst) => newSubst := subst
      | some (.inr set) => newSet := newSet.merge set
    if newSet.isEmpty then
      return some <| .inl newSubst
    else
      return some <| .inr ⟨newSet, newSubst⟩

  simplifyPair (pair : DisagreementPair) (subst : Substitution) : SimpleM (Option (Substitution ⊕ DisagreementSet)) := do
    let lhs := pair.fst
    let rhs := pair.snd
    dbg_trace s!"{repr lhs} =?= {repr rhs}"
    match hlflex:lhs.flexibility, hrflex:rhs.flexibility with
    | .rigid, .rigid =>
      dbg_trace s!"Rigid, Rigid"
      if lhs.binder != rhs.binder || lhs.head != rhs.head then
        return none
      else
        let newProblems := lhs.args.zip rhs.args
        let folder := fun set (newLhs, newRhs) =>
          let newLhs := BetaEtaNormalExpr.ofNormalExpr newLhs
          let newRhs := BetaEtaNormalExpr.ofNormalExpr newRhs
          let newPair := ⟨{newLhs with binder := lhs.binder.append newLhs.binder}, {newRhs with binder := rhs.binder.append newRhs.binder}⟩
          dbg_trace s!"RR new: {repr newPair}"
          set.insert newPair
        let newDisagreements := newProblems.foldl (init := .empty) folder
        return some <| .inr newDisagreements
    | .flexible, .flexible =>
      dbg_trace s!"Flex, Flex"
      let lhsVal := inhabitant (← lhs.headType)
      let rhsVal := inhabitant (← rhs.headType)
      let subst := subst.insert (lhs.headFVarId hlflex) lhsVal
        |>.insert (rhs.headFVarId hrflex) rhsVal
      return some <| .inl subst
    | .flexible, .rigid => dbg_trace s!"Flex, Rigid" return some <| .inr <| HashSet.empty.insert (lhs, rhs)
    | .rigid, .flexible => dbg_trace s!"Rigid, Flex" return some <| .inr <| HashSet.empty.insert (rhs, lhs)

  findMatcherTarget (set : DisagreementSet) : Option ({ e : BetaEtaNormalExpr // e.flexibility = .flexible} × { e : BetaEtaNormalExpr // e.flexibility = .rigid}) := do
    for (lhs, rhs) in set do
      match hlflex:lhs.flexibility, hrflex:rhs.flexibility with
      -- simplify already turned .rigid, .flexible this way around
      | .flexible, .rigid => return (⟨lhs, hlflex⟩, ⟨rhs, hrflex⟩)
      | _, _ => pure ()
    none

  matcher (flex : { e : BetaEtaNormalExpr // e.flexibility = .flexible}) (rig : { e : BetaEtaNormalExpr // e.flexibility = .rigid}) : SimpleM (List Substitution) := do
    let targetFVar := flex.val.headFVarId flex.property
    let targetFVarTyTelescope := (← getCtx).find! targetFVar |>.telescope
    match hhead:rig.val.head with
    | .bvar idx => throw "not implemented" -- projection
    | .const name =>
      -- imitation
      dbg_trace "imitation"
      let mut candidates := []
      let mut hs := #[]
      let constTy := (← getEnv).find! name
      let constTyTelescope := constTy.telescope
      for hResTy in constTyTelescope[:constTyTelescope.size - 1] do
        let hTyTelescope := targetFVarTyTelescope.set! (targetFVarTyTelescope.size - 1) hResTy
        let hTy := Ty.ofTelescope hTyTelescope
        let args := (hTyTelescope.size - 1).fold (init := #[]) (fun idx args => args.push (.bvar idx))
        let hFVar ← FVar.freshM hTy
        let hTerm := mkApp (.fvar hFVar) args
        hs := hs.push hTerm
      let replacer := abstractArgs (mkApp (.const name) hs) (targetFVarTyTelescope[:targetFVarTyTelescope.size - 1])
      candidates := (Substitution.empty.insert targetFVar replacer) :: candidates
      -- TODO: Projection
      return candidates
    | .fvar .. => nomatch BetaEtaNormalExpr.False_of_rigid_fvar rig.property hhead

#eval show IO _ from do
  let testPairs := #[
    -- flexible, flexible
    ([stlc| λ a : ℕ . f a], [stlc| λ b : ℕ . x], Env.empty, (Context.empty.insert ⟨"f", 0⟩ (.fun .nat .nat) |>.insert ⟨"x", 0⟩ .nat)),
    -- rigid, rigid
    ([stlc| λ f : ℕ → ℕ . f x], [stlc| λ g : ℕ → ℕ . g x], Env.empty, (Context.empty.insert ⟨"x", 0⟩ .nat)),
    -- flexible, rigid const
    ([stlc| λ x : ℕ . f x], [stlc| λ y : ℕ . 0], (Env.empty.insert "0" .nat), (Context.empty.insert ⟨"f", 0⟩ (.fun .nat .nat))),
    ([stlc| λ x : ℕ . f x], [stlc| λ y : ℕ . C y], (Env.empty.insert "C" (.fun .nat .nat)), (Context.empty.insert ⟨"f", 0⟩ (.fun .nat .nat)))
  ]
  for (expr1, expr2, env, ctx) in testPairs do
    let subst := unify expr1 expr2 |>.run' env ctx
    match subst with
    | .ok subst => 
      let expr1' := expr1.applySubst subst |>.betaReduce
      let expr2' := expr2.applySubst subst |>.betaReduce
      IO.println s!"{repr expr1'}"
      IO.println s!"{repr expr2'}"
      IO.println ""
    | .error e => IO.println s!"unification failure: {e} \n"

end Unify

end Expr

end Cube.Simple

