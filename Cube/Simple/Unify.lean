import Cube.Simple.Basic
import Cube.Simple.Infer
import Cube.Simple.Eval

namespace Cube.Simple.Expr

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
  | .fun t1 t2 => .lam t1 (inhabitant t2)

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
    match hlflex:lhs.flexibility, hrflex:rhs.flexibility with
    | .rigid, .rigid =>
      if lhs.binder != rhs.binder || lhs.head != rhs.head then
        return none
      else
        let newProblems := lhs.args.zip rhs.args
        let folder := fun set (newLhs, newRhs) =>
          let newLhs := BetaEtaNormalExpr.ofNormalExpr newLhs
          let newRhs := BetaEtaNormalExpr.ofNormalExpr newRhs
          let newPair := ⟨{newLhs with binder := lhs.binder.append newLhs.binder}, {newRhs with binder := rhs.binder.append newRhs.binder}⟩
          set.insert newPair
        let newDisagreements := newProblems.foldl (init := .empty) folder
        return some <| .inr newDisagreements
    | .flexible, .flexible =>
      let lhsVal := inhabitant (← lhs.headType)
      let rhsVal := inhabitant (← rhs.headType)
      let subst := subst.insert (lhs.headFVarId hlflex) lhsVal
        |>.insert (rhs.headFVarId hrflex) rhsVal
      return some <| .inl subst
    | .flexible, .rigid => return some <| .inr <| HashSet.empty.insert (lhs, rhs)
    | .rigid, .flexible => return some <| .inr <| HashSet.empty.insert (rhs, lhs)

  findMatcherTarget (set : DisagreementSet) : Option ({ e : BetaEtaNormalExpr // e.flexibility = .flexible} × { e : BetaEtaNormalExpr // e.flexibility = .rigid}) := do
    for (lhs, rhs) in set do
      match hlflex:lhs.flexibility, hrflex:rhs.flexibility with
      -- simplify already turned .rigid, .flexible this way around
      | .flexible, .rigid => return (⟨lhs, hlflex⟩, ⟨rhs, hrflex⟩)
      | _, _ => pure ()
    none

  projection (binder : Array Ty) (targetFVar : FVarId) (z : Nat) (zTelescope : Array Ty) : SimpleM Substitution := do
    let mut hs := #[]
    -- TODO this opt should be possible below as well
    let args := (zTelescope.size - 1).fold (init := #[]) (fun idx args => args.push (.bvar idx))
    -- TODO Dedup with projection
    for hResTy in zTelescope[:zTelescope.size - 1] do
      let hTyTelescope := binder.push hResTy
      let hTy := Ty.ofTelescope hTyTelescope
      let hFVar ← FVar.freshM hTy
      let hTerm := mkApp (.fvar hFVar) args
      hs := hs.push hTerm
    let replacer := abstractArgs (mkApp (.bvar z) hs) zTelescope
    let candidate := (Substitution.empty.insert targetFVar replacer)
    return candidate

  projections (e : BetaEtaNormalExpr) (targetFVar : FVarId) (targetFVarTyTelescope : Array Ty) (resultTy : Ty) : SimpleM (List Substitution) := do
    let mut substs := []
    for i in [0:targetFVarTyTelescope.size - 1] do
      let iTy := targetFVarTyTelescope[i]!
      let iTyTelescope := iTy.telescope
      let iResultTy := iTyTelescope[iTyTelescope.size - 1]!
      if resultTy == iResultTy then
        substs := (← projection e.binder targetFVar i iTyTelescope) :: substs
    return substs

  matcher (flex : { e : BetaEtaNormalExpr // e.flexibility = .flexible}) (rig : { e : BetaEtaNormalExpr // e.flexibility = .rigid}) : SimpleM (List Substitution) := do
    let targetFVar := flex.val.headFVarId flex.property
    let targetFVarTyTelescope := (← getCtx).find! targetFVar |>.telescope
    match hhead:rig.val.head with
    | .bvar idx => projections flex.val targetFVar targetFVarTyTelescope (rig.val.binder.get! (rig.val.binder.size - idx))
    | .const name =>
      -- imitation
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
      let candidates := (Substitution.empty.insert targetFVar replacer) :: (← projections flex.val targetFVar targetFVarTyTelescope (constTyTelescope.get! (constTyTelescope.size - 1)))
      -- TODO: Projection
      return candidates
    | .fvar .. => nomatch BetaEtaNormalExpr.False_of_rigid_fvar rig.property hhead

#eval show IO _ from do
  let testPairs := #[
    -- flexible, flexible
    ([stlc| λ a : ℕ . f a], [stlc| λ b : ℕ . x], Env.empty, (Context.empty.insert ⟨"f", 0⟩ (.fun .nat .nat) |>.insert ⟨"x", 0⟩ .nat)),
    -- rigid, rigid
    ([stlc| λ f : ℕ → ℕ . f x], [stlc| λ g : ℕ → ℕ . g x], Env.empty, (Context.empty.insert ⟨"x", 0⟩ .nat)),
    -- flexible, rigid
    ([stlc| λ y : ℕ . x], [stlc| λ y : ℕ . 0], (Env.empty.insert "0" .nat), (Context.empty.insert ⟨"x", 0⟩ .nat)),
    ([stlc| λ x : ℕ . f x], [stlc| λ y : ℕ . 0], (Env.empty.insert "0" .nat), (Context.empty.insert ⟨"f", 0⟩ (.fun .nat .nat))),
    ([stlc| λ x : ℕ . f x], [stlc| λ y : ℕ . C y], (Env.empty.insert "C" (.fun .nat .nat)), (Context.empty.insert ⟨"f", 0⟩ (.fun .nat .nat))),
    ([stlc| λ x : ℕ . f (C (f x))], [stlc| λ x : ℕ . C x], (Env.empty.insert "C" (.fun .nat .nat)), (Context.empty.insert ⟨"f", 0⟩ (.fun .nat .nat)))
  ]
  for (expr1, expr2, env, ctx) in testPairs do
    let subst := unify expr1 expr2 |>.run' env ctx
    match subst with
    | .ok subst => 
      let expr1' := expr1.applySubst subst |>.betaReduce
      let expr2' := expr2.applySubst subst |>.betaReduce
      IO.println s!"{repr subst}"
      IO.println s!"{repr expr1'}"
      IO.println s!"{repr expr2'}"
      IO.println ""
    | .error e => IO.println s!"unification failure: {e} \n"

end Cube.Simple.Expr.Unify
