import AxiomaticSystem.dep
open dep -- open the additional dependencies used in this package

-- ABI functions

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

    -- private function that returns the type of an axiom stored at a given index in the axiomatic system (Prop)
    private def _get_sentence_from_index : axiomaticSystem → Nat → Prop
      | axiomaticSystem.init element, _                             => getSentence element
      | axiomaticSystem.inst first_element rest_of_list, 0          => getSentence first_element
      | axiomaticSystem.inst first_element rest_of_list, Nat.succ i => (_get_sentence_from_index (rest_of_list) i)
    -- private axiom that re-expresses the axiom stored at a given index in the axiomatic system
    private axiom _get_element_from_index (ax : axiomaticSystem) (index : Nat) (sentence : Prop := _get_sentence_from_index ax index) : sentence
    -- define notation to easily reference an axiom from the axiomatic system in an expression
    set_option quotPrecheck false
    notation:min "reference_axiom" index "from" axSystem ":" type =>
      let ax : type := _get_element_from_index axSystem index;
      ax
      
  end axiomaticSystem
end AxiomaticSystem
