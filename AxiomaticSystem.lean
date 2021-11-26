import AxiomaticSystem.dep
open dep -- open the additional dependencies used in this package

namespace AxiomaticSystem
  namespace axiomaticSystem
    def push {sentence : Prop} : axiomaticSystem → (Axiom : sentence) → axiomaticSystem -- function to push new axiom to the end of the axiomaticSystem stack
      | axiomaticSystem.init element, Axiom                    => Axiom ... (axiomaticSystem.init element)
      | axiomaticSystem.inst first_element rest_of_list, Axiom => Axiom ... (axiomaticSystem.inst first_element rest_of_list) -- in both cases use the ... notation to add the new axiom onto the end of the list

    -- define an empty axiom that can be used in the pop function to replace the last axiom, effectively removing it
    variable (null : Prop)
    axiom empty_ax : null -- empty axiom of type null can be interpreted as a proof that the null Prop exists
    def pop : axiomaticSystem → axiomaticSystem -- function to pop the axiom off of the end of the axiomaticSystem stack
      | axiomaticSystem.init _                          => empty_ax endAx -- trying to pop the only element of a axiomaticSystem returns an axiomaticSystem containing only the empty axiom (ei. an empty axiomaticSystem)
      | axiomaticSystem.inst first_element rest_of_list => axiomaticSystem.inst first_element (pop rest_of_list)--TODO figure this out

    def length : axiomaticSystem → Nat -- function that returns the number of elements in the list
      | axiomaticSystem.init _ => 1
      | axiomaticSystem.inst first_element rest_of_list => 1+(length rest_of_list)

    def get : axiomaticSystem → Nat → Prop -- function that takes an index and returns the Prop stored at that index in the list
      | axiomaticSystem.init element, _                                 => element -- for a single element axiomaticSystem, return the element regardless of passed index
      | axiomaticSystem.inst first_element rest_of_list, 0              => first_element -- if the index is 0 for a multi element axiomaticSystem, return the first element
      | axiomaticSystem.inst first_element rest_of_list, Nat.succ index => get rest_of_list index -- if the index is greater than 0, call the get function on the rest of the list, subtracting 1 from the index

    notation:max "def_from_axioms" name ":" type ":=" axSystem =>
      try
        let Axiom : get axSystem (length axSystem - 1)
        | _ => let name : type := Axiom; 
        getUnsolvedGoals
      catch ex =>
       if length axSystem > 0 then
         def_from_axioms name : type := pop axSystem
       else
         throw ex
      
  end axiomaticSystem

  
end AxiomaticSystem


def equality (a : String) (b : String) : Bool :=
  if Eq a b then
    true
  else 
    false

#check Eq

axiom t : 1=1
theorem test : 1=1 := 
 let s := t
 s