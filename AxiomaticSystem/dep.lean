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


  namespace axList
    def push {sentence : Prop} : axList → (Axiom : sentence) → axList -- function to push new axiom to the end of the axList stack
      | init element, Axiom                    => Axiom ... (init element)
      | inst first_element rest_of_list, Axiom => Axiom ... (inst first_element rest_of_list) -- in both cases use the ... notation to add the new axiom onto the end of the list

    -- define an empty axiom that can be used in the pop function to replace the last axiom, effectively removing it
    variable (null : Prop)
    axiom empty_ax : null -- empty axiom of type null can be interpreted as a proof that the null Prop exists
    def pop : axList → axList -- function to pop the axiom off of the end of the axList stack
      | init _                          => empty_ax endAx -- trying to pop the only element of a axList returns an axList containing only the empty axiom (ei. an empty axList)
      | inst first_element rest_of_list => inst first_element (pop rest_of_list)--TODO figure this out

    def length : axList → Nat -- function that returns the number of elements in the list
      | init _ => 1
      | inst first_element rest_of_list => 1+(length rest_of_list)

    def get : axList → Nat → Prop -- function that takes an index and returns the Prop stored at that index in the list
      | init element, _ => element -- for a single element axList, return the element regardless of passed index
      | inst first_element rest_of_list, 0 => first_element -- if the index is 0 for a multi element axList, return the first element
      | inst first_element rest_of_list, Nat.succ index => get rest_of_list index -- if the index is greater than 0, call the get function on the rest of the list, subtracting 1 from the index
  end axList

  -- testing the above functions
  def axL1 : axList := ax1 endAx
  def axL2 : axList := ax1 ... ax2 endAx 
  #print axL1
  #print axL2
  -- push
  def axL3 := axList.push axL1 ax2
  def axL4 := axList.push axL2 ax3
  -- pop
  def axL5 := axList.pop axL4
  -- length
  def len := axList.length axL4
  #eval len
  -- get
  def element := axList.get axL4 2
  #check element
  #print element

end dep