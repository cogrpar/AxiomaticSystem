-- this file contains additional dependencies
namespace dep
  -- function that takes an object and returns its type
  def getType {α : Type u} (a : α) : Type u := α
  #check getType

  -- function that takes an axiom and returns its type (ie a sentence of type Prop)
  def getSentence {α : Prop} (ax : α) : Prop := α


  -- AxiomaticSystem type
  -- stores list of Prop taken from the types of axioms
  inductive AxiomaticSystem where
    | init (first_element : Prop) : AxiomaticSystem
    | inst (first_element : Prop) (rest_of_list : AxiomaticSystem) : AxiomaticSystem

  -- defining new notation for more easily constructing AxiomaticSystems
  notation:min arg "endAx"     => AxiomaticSystem.init (getSentence arg)
  notation:min arg1 "..." arg2 => AxiomaticSystem.inst (getSentence arg1) arg2

  -- example of new notation in use:
  axiom ax1 : 1=1
  axiom ax2 : 1<2
  axiom ax3 : 2<3 
  
  def testAxiomaticSystem : AxiomaticSystem := ax1 ... ax3 ... ax3 endAx
  #check testAxiomaticSystem
  #check ax1 ... ax2 ... ax3 endAx
  #check AxiomaticSystem.inst (1=1) (AxiomaticSystem.init (1=1))


  namespace AxiomaticSystem
    def push {sentence : Prop} : AxiomaticSystem → (Axiom : sentence) → AxiomaticSystem -- function to push new axiom to the end of the AxiomaticSystem stack
      | init element, Axiom                    => Axiom ... (init element)
      | inst first_element rest_of_list, Axiom => Axiom ... (inst first_element rest_of_list) -- in both cases use the ... notation to add the new axiom onto the end of the list

    -- define an empty axiom that can be used in the pop function to replace the last axiom, effectively removing it
    variable (null : Prop)
    axiom empty_ax : null -- empty axiom of type null can be interpreted as a proof that the null Prop exists
    def pop : AxiomaticSystem → AxiomaticSystem -- function to pop the axiom off of the end of the AxiomaticSystem stack
      | init _                          => empty_ax endAx -- trying to pop the only element of a AxiomaticSystem returns an AxiomaticSystem containing only the empty axiom (ei. an empty AxiomaticSystem)
      | inst first_element rest_of_list => inst first_element (pop rest_of_list)--TODO figure this out

    def length : AxiomaticSystem → Nat -- function that returns the number of elements in the list
      | init _ => 1
      | inst first_element rest_of_list => 1+(length rest_of_list)

    def get : AxiomaticSystem → Nat → Prop -- function that takes an index and returns the Prop stored at that index in the list
      | init element, _ => element -- for a single element AxiomaticSystem, return the element regardless of passed index
      | inst first_element rest_of_list, 0 => first_element -- if the index is 0 for a multi element AxiomaticSystem, return the first element
      | inst first_element rest_of_list, Nat.succ index => get rest_of_list index -- if the index is greater than 0, call the get function on the rest of the list, subtracting 1 from the index
  end AxiomaticSystem

  -- testing the above functions
  def axL1 : AxiomaticSystem := ax1 endAx
  def axL2 : AxiomaticSystem := ax1 ... ax2 endAx 
  #print axL1
  #print axL2
  -- push
  def axL3 := AxiomaticSystem.push axL1 ax2
  def axL4 := AxiomaticSystem.push axL2 ax3
  -- pop
  def axL5 := AxiomaticSystem.pop axL4
  -- length
  def len := AxiomaticSystem.length axL4
  #eval len
  -- get
  def element := AxiomaticSystem.get axL4 2
  #check element
  #print element

end dep