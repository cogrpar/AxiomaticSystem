-- LEAN language tour

-- 1. Basic Usage

-- 1.1 Expressions (https://leanprover.github.io/lean4/doc/expressions.html):
-- universes:
-- every type in LEAN is an expression of 'Sort u' where u is a universe level
-- universe variables are declared with either the 'universe' or 'universes'command
universe u
universes v w x

#check Sort u -- returns 'Type' of universe level 'u'
#check Sort (v + 4)
#check Sort 5
#check Sort 0
#check Sort (max u v)
#check Sort (max 3 5)
#check Sort (imax u v)
#check Sort (imax 5 2)
#check Sort (imax 5 0) -- returns universe level 0 if the second argument is 0
#check Prop -- Type universe 0
#check Type -- Type universe 1

-- expressions:
-- 'Sort u': the universe of types at universe level 'u'
-- 'c': identifier denoting a declared constant or a defined object
-- 'x': variable in the local context in which the expression is interpreted
-- '?m': metavariable in the metavariable context in which the expression is interpreted (ie. a "hole" that still needs to be synthesized)
-- '(x : α) → β': a function on 'x' of type 'α' to type 'β'
-- 's t':  the result of applying 's' to 't', where 's' and 't' are expressions
variable (α β : Sort u)
variable (s : (x : α) → β)
variable (t : α)
#check s t
-- 'fun x : α => t' or 'λ x : α => t': the function mapping any value 'x' of type 'α' to 't', where 't' is an expression
#check fun x : α => t
#check λ x : α => t
-- 'let x := t; s': local definition, denotes the value of 's' when 'x' is replaced by 't'
variable (s : α)
def local_expr_ex : α :=
  let z := (x : α) → β
  let y := z
  let x := t; s
-- 's.i': a projection, denotes the value of the i-th field of 's'
namespace projection_ex
  def d := "test"
  def e := 5
end projection_ex
#print projection_ex.d
#check projection_ex.e
-- 'lit': a natural number or string literal
-- 'mdata k s': the expression 's' decorated with metadata 'k'


-- 1.2 Declarations (https://leanprover.github.io/lean4/doc/declarations.html)
-- axioms:
-- for each 'p : Prop' there is a type 'Proof p'.  Axioms are constants of this type
variable (Proof : Prop → Type)
-- 'axiom c : α': declares a constant named 'c' of type 'α', it is postulating that 'α' is not an empty type
variable (α : Type)
axiom c₁ : α 
#check c₁
axiom c₂ (p q : Nat) : p = q
#check c₂ 2 2 -- type is '2 = 2' which is an instance of the Prop type

-- definitions:
-- 'def c : α := v': defines 'c' to denote 'v', which should have type 'α'
variable (v : α)
def c₃ : α := v
#check c₃

-- 'theorem c : p := v': similar to def, but intended to be used when 'p' is a proposition
variable (m n f: Prop)
theorem c₄ (hm : m) (hn : n) : n ∧ m := 
  And.intro hn hm -- 'And.intro' constructs a proof of 'n ∧ m' from 'hn' and 'hm'
#check c₄
#check c₄ (true) (f)
-- axioms can be used within theorems as a way of postulating the existence of an element of a given type
theorem t1 (hm : m) (hn : n) : m := hm

variable (ni : n)
def ax (p : Prop) (t : Type) (t₁ : t) : p → t := λ x : p => t₁
#check ax n Bool true ni 
def truth : Prop := 1=1
#eval ax truth Bool true 

axiom hn (b : Prop) : b
#check hn
theorem t : (m → ∃ (n : Prop), n) := t1 hn




namespace test
  variable (a b c : String)
  def d := "test"

  -- axiom
  axiom f : ∃ (x : Bool), ∃ (y : Bool), (x ∧ y)
end test

#check test.f


-- tactics
theorem t1 : q ∨ p → p ∨ q := by
  intro h
  cases h with
  | inl h_left =>
    apply Or.inr
    exact h_left
  | inr h_right =>
    apply Or.inl
    assumption
  

def main : IO Unit :=
  let str := "hello world from lean!"
  --IO.println "hello world from lean!"
  IO.println str