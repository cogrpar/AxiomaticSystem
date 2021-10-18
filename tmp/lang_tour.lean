-- LEAN language tour
/- 
The lean4 docs (https://leanprover.github.io/lean4/doc/) are 
a great resource for learning the language, but they can be 
dificult to work through, overcomplicated at times, and not yet
complete.  For that reason, I have included this file that I 
wrote as I worked through the docs, which I hope provides enough 
information to get started with the language.  It is by no means
a complete tour, but it should be sufficient to help one get 
familiar with the basics lean4.
-/

-- 1. Basic Usage

-- 1.1 Expressions (https://leanprover.github.io/lean4/doc/expressions.html):
namespace expressions
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
  -- '(x : α) → β': a function on 'x' of type 'α' mapping it to 'β', where 'β' is of type 'Sort'
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

  -- basic data types and assertions:
  -- numbers (Nat):
  def num : Nat := 5
  #check num
  #check 5
  -- booleans (Bool):
  def boolean (a : Bool) (b : Bool) : Bool :=
    a || b
  #check boolean
  #check boolean true false
  #check false
  -- pairs:
  def pair (a : Nat) (b : Bool) : Nat × Bool :=
    (a, b)
  #check pair
  #check pair 5 true
  #check (1, 2)
  -- lists:
  /- 'open list' not working currently
  open list
  def list₁ : list Nat := [1, 2, 3] 
  #check list₁
  #check (1 :: list₁) -- get index of list
  -/
  -- sets:
  /- set curly bracket notation not working currently
  def set₁ : set Nat :=
    {1, 2, 3}
  def set₂ : set Nat :=
    {x | x < 7} ∪ set₁
  #check set₁
  #check set₂
  -/
  -- strings and characters:
  #check "hello world"
  #check 'a'
  -- assertions:
  #check ∀ a b c n : Nat, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ n > 2 → a^n + b^n ≠ c^n
end expressions


-- 1.2 Declarations (https://leanprover.github.io/lean4/doc/declarations.html)
namespace declarations
  -- axioms:
  -- 'axiom c : α': declares a constant named 'c' of type 'α', it is postulating that 'α' is not an empty type
  variable (α : Type)
  axiom c₁ : α 
  #check c₁
  axiom c₂ (p q : Nat) : p = q
  #check c₂
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
  -- axioms can be used within theorems as a way of postulating the existence of an element of a given type (ie. a hypothesis or assumption of the proof of that type)
  axiom c₅ (num : Nat) : ∃ (num₁ : Nat), num = num₁
  #check c₅
  theorem uses_ax (num : Nat) : ∃ (num₁ : Nat), num = num₁ :=
    c₅ num
  #check uses_ax
  -- we can define an undound axiom postulating the existence of an element of the empty 'False' type
  axiom unsound : False
  #check unsound
  -- this can be used to show that everything follows from false
  theorem prove_anything : 1 = 0 :=
    False.elim unsound
  #check prove_anything

  -- 'constant c : α (:= v)' defines a constant 'c' of type 'α'
  -- the optional term 'v' must have type 'α' and can be viewed as a certificte that 'v' is not an empty type
  -- if no 'v' is provided, lean will try to find one automatically to ensure that 'v' is not an empty type 
  -- 'v' is not shown by the type checker, and after the declaration of 'c' it is effectively dropped by lean
  constant const₁ : Nat
  #check const₁
  constant const₂ : Nat := 5
  #check const₂

  -- 'example' simulates 'def' or 'theorem' without having to have a name or be added to the environment
  -- 'example : α := t' creates a new 'example' such that 't' has type 'α'
  variable (t : α)
  example : α := t
end declarations

-- 1.3 Inductive Types (https://leanprover.github.io/lean4/doc/declarations.html#inductive-types)
namespace inductive_types
  -- context and telescopes:
  -- the environment in lean represents the the current state at the time of a line being parsed, including any previous declarations
  -- the local context is a list of variables that is held constant while an expression is being elaborated: '(a₁ : α₁), (a₂ : α₂), ... (aₙ : αₙ)' 
  -- where each 'aᵢ' is a local constant and each 'αᵢ' is an expression of type 'Sort u' such that the universe level can be made up of elements of the enviroment, so long as the element in question has already been declared
  -- consider the following expression:
  def ex₁ (a b : Nat) : Nat → Nat := fun c => a + (b + c)
  -- the expression 'fun ex₁ => a + (b + c)' is elaborated in the context '(a : Nat), (b : Nat)'
  -- the expression 'a + (b + c)' is elaborated in the context '(a : Nat), (b : Nat), (c : Nat)'
  -- the context is sometimes refered to as telescope
  -- more generally, a telescope is a list of declarations declared relative to a given context
  universe u
  def ex₂ (a₁ : Sort u) (a₂ : Sort u) (a₃ : Sort u) /- ... -/ (aₙ : Sort u) (x : aₙ) : aₙ := -- context is '(a₁ : Sort u) (a₂ : Sort u) (a₃ : Sort u) ... (aₙ : Sort u), (x : aₙ)'
    let b₁ (x : a₁) : a₁ := x -- the following lines demonstrate telescope '(b₁ : a₁ → a₁) (b₂ : a₂ → a₂) (b₃ : a₃ → a₃) ... (bₙ : aₙ → aₙ)' relative to the context
    let b₂ (x : a₂) : a₂ := x -- note that the types of each 'bₙ' in the telescope can depend on members of the context, 'aₙ'
    let b₃ (x : a₃) : a₃ := x -- generalizing this idea, the context itself can be viewed as a telescope relative to an empty context
    /- ... -/
    let bₙ (x : aₙ) : aₙ := x
    bₙ x
  -- telescopes are often used to describe a list of arguments, or parameters, to a declaration
  -- in such cases, it is often notationally convenient to let '(a : α)' stand for a telescope rather than just a single argument

  -- inductive types:
  -- types can be defined inductively in lean according to the following format:
  inductive foo (a : α) where -- '(a : α)' is the context for this inductive type
    | constructor₁ : (b : β₁) → foo a -- each '(bₙ : βₙ)' is a telescope relative to the context
    | constructor₂ : (b : β₂) → foo a 
    /- ... -/
    | constructorₙ : (b : βₙ) → foo a
  -- suppose that in the above telescope, each '(b : βᵢ)' refers to '(b₁ : βᵢ₁) ... (bᵤ : βᵢᵤ)'
  -- each element in the telescope is either nonrecursive or recursive
  -- the inductive 'foo' represents a type that is freely generated by the constructors
  -- in declaring 'foo', the following gets added to the environment:
  -- the type former 'foo → Sort u'
  #check foo
  -- for each 'i', the constructor 'foo.constructorᵢ : (a : α) (b : βᵢ) → foo a'
  -- the telescope '(b : βᵢ)' is nonrecursive if 'βᵢ' doesn't refer to 'foo', and it is recursive if it does (ie. 'βᵢ : (d : δ) → foo')
  #check foo.constructor₁
  -- the eliminator 'foo.rec' which is a function that maps foo to a type; it takes the following arguments
  -- '(a: α)': the parameters
  -- '{C : foo a → Type u}': the motive of the elimination (the curly braces show that the 'Type u' of this expression is left to lean to determine, ie. left implicit)
  -- '(x : foo a)': the major premise (where the major premise is a statement of a general or universal nature)
  -- for each 'i', the minor premise corresponding to 'constructorᵢ' (where the minor premise is a statement regarding a particular case, related to the subject of the major premise), and returns an element of 'C (constructorᵢ a b)'
  -- returns an element of 'C x'
  #check foo.rec
  -- the eliminator represents a principle of recursion
  -- to find an element of 'C x' where 'x : foo a' (ie. to map foo to a type), it suffices to show that 'C' applies for cases where 'x' is of the form 'constructorᵢ a b' 
  -- in the case where some of the arguments to 'constructorᵢ' are recursive, we can assume that we have already constructed values of 'C y' for each value 'y' constructed at an earlier stage
  inductive natural_numbers : Type
    | zero : natural_numbers -- nonrecusrive
    | succ : (prev : natural_numbers) → natural_numbers -- recursive
  #check natural_numbers.rec -- function represents recursion because the motive of elimination applied to recursive constructors assumes that the motive of elimination has already been applied to the recursive arguments
  -- when 'C x' is of type 'Prop' (ie. when the eliminator maps foo to a proposition), 'foo.rec' represents induction
  -- in order to show '∀ x, C x', it suffices to show that 'C' applies for each constructor, so long as it is assumed that 'C' holds for the recursive inputs for said constructor (ie. the inductive hypothesis)
  inductive boolean : Prop
    | t : boolean -- nonrecursive
    | f : boolean
    | not : (input : boolean) → boolean -- recursive
  #check boolean.rec -- function representing induction 
end inductive_types

-- 1.4 Sections (https://leanprover.github.io/lean4/doc/sections.html)
namespace sections
  -- the 'variable' command can be used to declare objects of any type
  variable (new_variable : Type) -- declares variable called 'new_variable' which stays in scope until the end of the file (or the namespace in this instance)
  #check new_variable
  -- a way to limit the scope of a variable is to use the 'section' command
  section example_section
    variable (section_variable : Type) -- declares new variable limited to the 'example_section' section
    #check section_variable
  end example_section
  -- if one attempts to run '#check section_variable' outide of the section, lean will throw an error
end sections

-- 1.5 Namespaces (https://leanprover.github.io/lean4/doc/namespaces.html)
namespace namespaces
  -- namespaces can be used to group declarations into hierarchical structures
  namespace example_namespace
    def a : Nat := 5
    def f (x : Nat) : Nat := x + 7

    def fa : Nat := f a
    def ffa : Nat := f (f a)

    #check a
    #check f
    #check fa
    #check ffa
    #check example_namespace.fa

    -- namespaces can be nested
    namespace nested
      def b : Nat := 5
      #check b -- variables declared in the namespace can be referenced as normal within the namespace
    end nested
    #check nested.b -- to be referenced outside of that namespace, they must be referenced as a projection of the namespace field
  end example_namespace
  #check example_namespace.a
  #check example_namespace.nested.b -- referenced using full name outside of namespace

  -- namespaces that have been closed can later be reopened
  namespace example_namespace
    #check a
    def c : Nat := 12
  end example_namespace

  -- the 'open' command can be used to open the contents of a namespace to the current scope
  open example_namespace
  open nested
  #print a
  #print b
  #print c -- variables can now be referenced as if the commands are run from within the namespaces
end namespaces

-- 1.6 Implicit Arguments (https://leanprover.github.io/lean4/doc/implicit.html)
namespace implicit_arguments
  -- when objects are declared in lean (using def, theorem, axiom, constant, inductive, or structure), they can be declared implicitly or explicitly
  -- implicit arguments' types are inferred by lean behind the scenes
  -- explicit arguments' types are specified by the user
  -- '(x : α)': an explicit argument of type 'α'
  -- '{x : α}': an implicit argument, eagerly inserted (eagerly meaning that the expression is interpreted as soon as it is assigned to a variable)
  -- '⦃x : α⦄': or {{x : α}} : an implicit argument, weakly inserted (weakly meaning that the expression isn't interpreted as soon as it is assigned to a variable)
  -- '[x : α]': an implicit argument that should be inferred by type class resolution
  -- '(x : α := v)': an optional argument, with default value 'v'
  -- '(x : α := by tac)': an implicit argument, to be synthesized by tactic 'tac'

  -- example of a function defined with explicit arguments
  def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)
  #check compose
  -- when a function has an explicit argument, you can nonetheless ask lean's elaborator to infer the argument automatically
  -- this is done by entering it as an underscore '_'
  #check compose _ _ _ -- notice that the inferred types become holes for lean to fill
  def double (x : Nat) := 2*x
  def triple (x : Nat) := 3*x
  #check compose _ _ _ double triple _ -- infers 'Nat'
  
  -- conversely, writing '@foo' indicates that all of the arguments to be 'foo' are to be given explicitly, independent of how foo was declared
  -- take the following implicit definition for example:
  def compose₂ {α β γ : Type} (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)
  #check compose₂ -- implicitly defined
  #check @compose₂ -- explicitly defined

  -- variables can also be specified as implicit when they are declared with the 'variable' command
  variable (x : α) -- normal declaration of 'x' explicitly defined as type 'α'
  #check x 
  universe u
  variable {imp_x : Type u} -- implicit declaration of 'x'
  #check imp_x
  variable (instance_of_imp_x : imp_x)
  def ident := instance_of_imp_x
  #check instance_of_imp_x
  #check ident 
  #check ident 5
end implicit_arguments

-- 1.7 Declaring New Types (https://leanprover.github.io/lean4/doc/decltypes.html)
namespace declaring_new_types
  -- practically every type in lean can be thought of as an inductive type
  -- intuitively, for every inductive type 'foo', each constructor specifies a way of building new objects of type 'foo'
  -- the type 'foo' consists of nothing more than the objects that are constructed in this way

  -- the simplest kind of inductive type is simply a type with a finite, enumerated list of elements
  -- for example, here is an example declaring an enumerated type 'Weekday':
  inductive Weekday where
    | sunday    : Weekday
    | monday    : Weekday
    | tuesday   : Weekday
    | wednesday : Weekday
    | thursday  : Weekday
    | friday    : Weekday
    | saturday  : Weekday
  #check Weekday.sunday
  #check Weekday.thursday
  -- functions can take advantage of pattern matching
  -- here is a function that maps 'Weekday' to a natural number
  def natOfWeekday (d : Weekday) : Nat :=
    match d with
      | Weekday.sunday    => 1
      | Weekday.monday    => 2
      | Weekday.tuesday   => 3
      | Weekday.wednesday => 4
      | Weekday.thursday  => 5
      | Weekday.friday    => 6
      | Weekday.saturday  => 7
  #check natOfWeekday
  #eval natOfWeekday Weekday.thursday
  /- note that instead of writing:
      def natOfWeekday (d : Weekday) : Nat :=
        match d with
     lean allows us to write:
      def natOfWeekday Weekday -> Nat
  -/
end declaring_new_types

-- 2. Theorem Proving

-- 2.1 Axioms, Propositions, and Proofs (https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html)
namespace propositions_and_proofs
  -- Prop:
  -- 'Prop' is a type that represents propositions
  #check Prop
  -- constructors can be used to contruct new propositions from others:
  #check And -- 'Prop → Prop → Prop' ie. a function on 'Prop' that yeilds a new 'Prop'
  #check Or
  #check Not
  #check implies
  def Implies (α : Prop) (β : Prop) : Prop := -- define Implies equivalent to implies
    α → β 
  #check Implies
  -- an important principle in the dependant type theory of lean is that an object with a given type is seen as an instance of the proof of that type
  -- the implications of this are profound, and it is the mechanism by which theorems can be interpreted 
  -- while not covered here, it is important to understand dependant type theory for this (https://leanprover.github.io/lean4/doc/deptypes.html)
end propositions_and_proofs

-- 2.2 Tactics (https://leanprover.github.io/lean4/doc/tactics.html)
namespace tactics
  -- tactics are instructions that tell Lean how to construct a term or proof
  -- here is an example of a tactic:
  theorem tactic_ex : q ∨ p → p ∨ q := by
    intro h
    cases h with
    | inl h_left =>
      apply Or.inr
      exact h_left
    | inr h_right =>
      apply Or.inl
      assumption
end tactics  

-- 3. The Main Function

-- more of a footnote really, but here is an example of a main function:
def main : IO Unit := -- main function, entry point of the program
  let str := "hello world from lean!"
  --IO.println "hello world from lean!"
  IO.println str