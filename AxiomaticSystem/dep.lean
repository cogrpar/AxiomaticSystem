-- this file contains additional dependencies
namespace dep
  -- function that takes an object and returns its type
  def getType {α : Type u} (a : α) : Type u := α
  #check getType

  -- function that takes an axiom and returns its type (ie a sentence of type Prop)
  def getSentence {α : Prop} (ax : α) : Prop := α


  -- axiomaticSystem type
  -- stores list of Prop taken from the types of axioms
  inductive axiomaticSystem where
    | init {sentence : Prop} (first_element : sentence) : axiomaticSystem
    | inst {sentence : Prop} (first_element : sentence) (rest_of_list : axiomaticSystem) : axiomaticSystem

  -- defining new notation for more easily constructing axiomaticSystems
  notation:min arg "endAx"     => axiomaticSystem.init arg
  notation:min arg1 "..." arg2 => axiomaticSystem.inst arg1 arg2

end dep

open dep
axiom ax₁ : 1=1
axiom ax₂ : 2=2

def test : axiomaticSystem := ax₁ ... ax₂ endAx