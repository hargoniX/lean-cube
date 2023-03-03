import Cube.Simple.Basic
import Cube.Simple.Eval
namespace Cube.Simple.Krivine

mutual

inductive Closure where
| mk (term : Expr) (env : Environment)
deriving Repr

inductive Environment where
| mk (cs : List Closure)
deriving Repr

end

-- Allows for much nicer notation in the step function
instance : Coe (List Closure) Environment where
  coe cs := ⟨cs⟩

def Closure.term (c : Closure) : Expr :=
  match c with
  | .mk term _ => term

def Closure.env (c : Closure) : Environment :=
  match c with
  | .mk _ env => env

def Environment.closures (env : Environment) : List Closure :=
  match env with
  | .mk cs => cs

structure State where
  term : Expr
  stack : Environment
  environment : Environment
  deriving Repr

def State.initial (term : Expr) : State := { term, stack := .mk [], environment := .mk [] }


/-
The krivine machine basically collects arguments on a stack,
pops them into a context once it enters lambda term and substitutes
bvars there like with a normal substitution.
-/
def step (s : State) : Except String State :=
  match s.term, s.stack.closures, s.environment.closures with
  | .app fn arg , p, e => return ⟨fn, ⟨arg, e⟩ :: p, e⟩
  | .lam _ body, ⟨u, e'⟩ :: p, e => return ⟨body, p, ⟨u, e'⟩ :: e⟩
  | .bvar 0, p, ⟨t, e'⟩ :: _ => return ⟨t, p, e'⟩
  | .bvar (n + 1), p, _ :: e => return ⟨.bvar n, p, e⟩
  | _, _, _ => throw s!"Machine could not make a further step at state: {repr s}"

partial def multistep (s : State) : Except String (Expr × Environment) := do
  let res := step s
  match h:res with
  | .ok ⟨t@(.const ..), ⟨[]⟩, e⟩ | .ok ⟨t@(.lam ..), ⟨[]⟩, e⟩ =>
    return (t, e)
  | .ok next =>
    multistep next
  | .error e => throw e

#eval Expr.betaReduce [stlc| ((λ f : ℕ → ℕ . λ x : ℕ . f x) (λ x : ℕ . x)) 0]
#eval multistep (.initial [stlc| ((λ f : ℕ → ℕ . λ x : ℕ . f x) (λ x : ℕ . x)) 0])

end Cube.Simple.Krivine
