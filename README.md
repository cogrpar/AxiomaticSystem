# AxiomaticSystem

lean package for working with axiomatic formal systems in the lean theorem prover

### ROAD MAP:
- [ ] **AxiomaticSystem Phase 1**
  - stores list of axioms `(ax₁ : prop₁), (ax₂ : prop₂), ... (axₙ : propₙ)`
  - can be used in theorem proving as proof of expression `α` where `α` is an instance of one of the axiomatic assumptions in AxiomaticSystem `β` 
  - eg. 
    ```len
    theorem example : χ := -- where 'β' is an AxiomaticSystem in which one of the axioms is of type 'χ' 
          α : χ := β -- the reference to AxiomaticSystem 'β' would automatically return the axiom of type 'χ'
    ```
- [ ] **AxiomaticSystem Phase 2**
  - create a function that can deduce pseudo-random theorems from axiomatic systems, generating a new AxiomaticSystem that includes the theorem as a redundant axiom 
  - use this to generate a large dataset of groups of axiomatic systems that are reducible to each other (codename *AxStack*)
- [ ] **AxiomaticSystem Phase 3**
  - train a neural network on AxStack that takes in two AxiomaticSystem's as strings and returns a boolean value that states if they are reducible to each other (codename *AxNet1*)
  - create a function built into the AxiomaticSystem package that implements AxNet1 to determine if two AxiomaticSystem types are reducible to each other
  - this function will be of type `AxiomaticSystem → AxiomaticSystem → Bool` where true means that they are reducible and false means that they are not
- [ ] **AxiomaticSystem Phase 4**
  - create a neural network on AxStack that trains by taking in a random member of each group of reducible axiomatic systems and trains on the simplest member of that group (codename *AxNet2*)
  - AxNet2 will take an AxiomaticSystem and return the simplest AxiomaticSystem reducible to the input
  - create a function built into the AxiomaticSystem package that implements AxNet2 to find the simplest form of an AxiomaticSystem
  - this function will be of type `AxiomaticSystem → AxiomaticSystem`
