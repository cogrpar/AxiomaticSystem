-- this file contains additional dependencies
namespace dep
  -- function that takes an object and returns its type
  def getType {α : Type u} (a : α) : Type u := α
  #check getType

  -- axList type allows for the creation of lists of axioms that can be passed into AxiomaticSystem
  inductive list (α : Type u) where
    | nil : list α
    | cons (head : α) (tail : list α) : list α

  namespace list
    def set : list α → Nat → α → list α -- function to set element of list at given index
      | cons a as, 0,          b => cons b as
      | cons a as, Nat.succ n, b => cons a (set as n b)
      | nil,       _,          _ => nil

    def length : list α → Nat -- function to get the lengh of a list
      | nil       => 0
      | cons a as => HAdd.hAdd (length as) 1

    def concat {α : Type u} : list α → α → list α -- function to concat element to the end of a list
      | nil,       b => cons b nil
      | cons a as, b => cons a (concat as b)

    def get {α : Type u} /-{inst : α}-/: (as : list α) → (i : Nat) → (inst : α) →  α
      | nil, _, inst                => inst
      | cons a as, 0, inst          => a
      | cons a as, Nat.succ i, inst => get as i inst
  end list
  
  def test_list : list Nat := (list.set (list.set (list.set list.nil 0 5) 1 3) 2 7) -- creates new list Nat [5, 3, 7]
  def first := list.get test_list 0 0
  def second := list.get test_list 1 0
  def third := list.get test_list 2 0

  def test : List Prop := []
  #check test
end dep