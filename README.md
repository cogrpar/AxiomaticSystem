# AxiomaticSystem

lean package for working with axiomatic formal systems in the lean theorem prover

### ROAD MAP:
- [x] **AxiomaticSystem Phase 1**
  - stores list of Props taken from the types of axioms `(ax₁ : prop₁), (ax₂ : prop₂), ... (axₙ : propₙ)`
  - can be used in theorem proving as proof of expression `χ` where `χ` is an instance of one of the axiomatic assumptions in AxiomaticSystem `β` 
  - eg. 
    ```Lean
    theorem example : χ := -- where 'β' is an AxiomaticSystem in which one of the axioms is of type 'χ' 
          reference_axiom i from β : χ -- the reference to AxiomaticSystem 'β' references the axiom of type 'χ', which must be specified to be stored at index i

- [x] **AxiomaticSystem Phase 2*
  - explore automated theorem proving by configuring OpenAI Codex to utilize AxiomaticSystem
