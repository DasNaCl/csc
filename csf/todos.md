
## CSF'24

 The bullets are loosely ordered by priority.

- [ ] Add discussion on limitations of the compositionality framework. Especially concerning the upper and lower composition. Highlight that one has to ensure that the intersections of classes do not become empty.
    - [ ] in section 4: after discussion of what intersection is, add example with sms violating tms by not deallocating a table containing bounds info
- [ ] Add emphasis that the framework works for arbitrary properties.
- [ ] Add discussion about the unified trace model vs. multiple different trace models
    - [ ] add subsection in sec 4 that discusses applicability of the framework (unified trace model, upper/lower comp, realistic compiler passes etc)
- [ ] Underline the relevance of the combined monitor and make it clearer how, why, and where it is needed (see discussion on framework).
- [ ] Rephrase introduction for clarification on why we have chosen memory safety and cryptographic constant time.
- [ ] Add paragraph on how sCCT overapproximates CCT and what kinds of programs would not satisfy sCCT while satisfying CCT.
- [ ] Add to future work section that we will look at more sophisticated optimisiation passes.
- [ ] cut semantics part (control tags etc)
- [ ] Fix the "typing" of monitor states (e.g., line 335)
- [ ] Rephrase paragraph about $L_{ms}$: the compiled code is instrumented to be memory-safe.
- [ ] fig 3 put caption on side not below
- [ ] fig 3 fix vertical lines positioning
- [ ] fig 4 caption on side
- [ ] Everywhere were we omit rules: State this explicitly.
- [ ] :chicken: do lower composition
- [x] Fixing the typos!
- [ ] ensure scct-low-authentic etc. "typecheck"
- [ ] Emphasise the role of classes and why the compositionality framework is general enough.
- [ ] Rephrase paragraph at 606.
- [ ] Fix references
- [ ] Get rid of "as you would expect", "... is straightforward", etc.
- [x] Change $\mathbb{N}_t$ to $\mathbb{N}$
- [ ] Fix layouting of `mix`. (likely remove it anyway)
- [x] Change data independent timing mode state to either `on` or `off`.
- [ ] Change descriptive text of e-set-\not\in to emphasise that no write happens. `v` is not really a "garbage" value, get rid of this confusing terminology. 
- [ ] Add hyperlinks to the Coq development of the respective proofs.
- [ ] Add quantifiers to disambiguate definitions.
- [x] Rewrite $\textbf{Any}$ to $\textbf{Leak}$.
- [x] drop 2.1
- [x] Change wording from "strikethrough edge" to "solid edge".


## Future Work

- [ ] !IMPORTANT! :chicken: when does compiler respect a property, robustly? compiler well-formedness? do we still get "our" compositionality framework out of this?
