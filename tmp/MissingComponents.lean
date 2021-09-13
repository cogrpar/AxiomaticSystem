-- the current release of lean4 has some missing or broken components that this package needs to function
-- as a temporary fix, this file contains the corrected defenition of the required components

namespace missing_components

-- Op 
inductive Op : Type
| add
| mul

-- Term
inductive Term where
| ofInt  : Int → Term
| var    : Nat → Term
| varPow : Nat → Nat → Term
| app    : Op → Term → Term → Term

-- Proof [missing]
inductive Proof where
| addZero   : Term → Proof
| zeroAdd   : Term → Proof
| addComm   : Term → Term → Proof
| addCommL  : Term → Term → Term → Proof
| addAssoc  : Term → Term → Term → Proof
| mulZero   : Term → Proof
| zeroMul   : Term → Proof
| mulOne    : Term → Proof
| oneMul    : Term → Proof
| mulComm   : Term → Term → Proof
| mulCommL  : Term → Term → Term → Proof
| mulAssoc  : Term → Term → Term → Proof
| distribL  : Term → Term → Term → Proof
| distribR  : Term → Term → Term → Proof
| ofIntAdd  : Int → Int → Proof
| ofIntMul  : Int → Int → Proof
| powZero   : Nat → Proof
| powOne    : Nat → Proof
| powMerge  : Nat → Nat → Nat → Proof
| powMergeL : Nat → Nat → Nat → Term → Proof
| congrArg₁ : Op → Proof → Term → Proof
| congrArg₂ : Op → Term → Proof → Proof
| congrArgs : Op → Proof → Proof → Proof
| refl      : Term → Proof
| trans     : Proof → Proof → Proof

-- axiom [broken]

end missing_components