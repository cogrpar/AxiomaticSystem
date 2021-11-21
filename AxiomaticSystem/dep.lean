-- this file contains additional dependencies
namespace dep
  -- function that takes an object and returns its type
  def getType {α : Type u} (a : α) : Type u := α
  #check getType

  -- function that takes an axiom and returns its type (ie a sentence of type Prop)
  def getSentence {α : Prop} (ax : α) : Prop := α


  -- function that maps from a given number of axioms as input to a list of Prop containing the types of the inputs
  inductive axList where
    | init (first_element : Prop) : axList
    | inst (first_element : Prop) (rest_of_list : axList) : axList


  -- defining new notation for more easily constructing axLists
  notation:min arg "endAx"     => axList.init (getSentence arg)
  notation:min arg1 "..." arg2 => axList.inst (getSentence arg1) arg2

  -- example of new notation in use:
  axiom ax1 : 1=1
  axiom ax2 : 1<2
  axiom ax3 : 2<3 
  
  def testAxList : axList := ax1 ... ax3 ... ax3 endAx
  #check testAxList
  #check ax1 ... ax2 ... ax3 endAx
  #check axList.inst (1=1) (axList.init (1=1))

  /-
  inductive list (α : Type u) where
    | nil : list α
    | cons (head : α) (tail : list α) : list α

  namespace list
    def set : list α → Nat → (b : α) → list α -- function to set element of list at given index
      | cons a as, 0,          b => cons b as
      | cons a as, Nat.succ n, b => cons a (set as n b)
      | nil, _, b                => list b (list α)

    def length : list α → Nat -- function to get the lengh of a list
      | nil       => 0
      | cons a as => HAdd.hAdd (length as) 1

    def concat {α : Type u} : list α → α → list α -- function to concat element to the end of a list
      | nil,       b => cons b nil
      | cons a as, b => cons a (concat as b)

    def get {α : Type u} /-{inst : α}-/: (as₀ : list α) → (i₀ : Nat) → (inst : α) →  α
      | nil, _, inst                => inst
      | cons a as, 0, inst          => a
      | cons a as, Nat.succ i, inst => get as i inst
  end list

  -- notation:min "[" arg:min "]" =>  
  
  def test_list : list Nat := (list.set (list.set (list.set list.nil 0 5) 1 3) 2 7) -- creates new list Nat [5, 3, 7]
  def first := list.get test_list 0 1
  def second := list.get test_list 1 0
  def third := list.get test_list 2 0

  #eval list.length test_list -/

end dep