import AxiomaticSystem.dep
open dep -- open the additional dependencies used in this package

namespace AxiomaticSystem
  inductive AxiomaticSystem (axType : Prop) where
    | new : AxiomaticSystem axType
  #check AxiomaticSystem

  axiom ax₁ : ∃ (x : Nat), ∃ (y : Nat), x = y
  axiom ax₂ : ∃ (x : Nat), ∃ (y : Nat), x ≠ y
  #check getType (getType ax₁)

  #check [1, 2]
  
  def test : AxiomaticSystem Nat := [1, 2]

end AxiomaticSystem