# Author Response for submission

We thank the reviewers for their comments and questions.

==========
TODO: where are the general comments ? 
  just get rid of general points?
==========

========================================================
General Points
========================================================




Below, we address each individual review, addressing the questions for authors first, and then other questions raised in the reviews.

==========================================================================================
Reviewer 1
==========================================================================================
---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> However, the basic setup seems to be highly idealized, ... 
---------------------------------------------------------------------------------
Reply:
------

The setup of this paper is the same that many other work in correct and secure compilation use, namely a language with a notion of components, and with a trace semantics that is used to both express the security properties of interest as well as to aide the proofs.
Some simplifications regard e.g., the memory model, but these are orthogonal to the applicability of the framework and just aim to simplify the (complex) secure compilation proofs.
Since much of the language formalisation is not presented, we can add a clarification in the language section that the model is rather 'standard'. 

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> Instead, we get rather grand claims, e.g.
> - "This paper is the first to study what security properties are preserved across the composition of different secure compiler passes."
> - "From an engineering perspective, this is the desirable approach to building secure compilers."
> which are not really well supported.
---------------------------------------------------------------------------------
Reply:
------

The claims we make are factually correct, it is the first to study composition of secure compilers.
Moreover, given how compilers are built (i.e., sequences of passes), the theory we devise works with the current compiler construction approach.
We use (some) real-world compiler passes to highlight the real-world applicability of our approach, but we are happy to add explanatory text as 

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
>  Don't you mean "*a* whole program"?   And do you really mean *a* trace there?  I'd expect all the traces of the program to have to satisfy π.
---------------------------------------------------------------------------------
Reply:
------

We are thankful for identifying this typo.
To be clear -- besides the typo -- notion we are using is the canonical definition for program behaviour, as taken from Compcert and other similar work.

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> Many languages have some kind of nondeterminism, e.g. to loosely specify the evaluation order.  That too has to be taken into account in the notion of correctness, and a priori it's quite unclear how one could specify that a compiler for such a language prevents information flow leakage via the resolution of those nondeterministic choices. Again I see no mention of this in the paper.
---------------------------------------------------------------------------------
Reply:
------

Section 4.3 presents extensions to the framework that allow to take undefinedness, non-determinism, resource exhaustion, and similar settings into account.
Here, it is crucial to find a suitable cross-language trace relation `~`.
Example instantiations of `~` are in section 1 in the paper `An Extended Account of Trace-relating Compiler Correctness and Secure Compilation` by Abate et al., 2021.
Thus, our framework supports reasoning about that kind of behaviour. We do not take that into account in our evaluation study because we focus on security properties, whose preservation does not rely on exploiting undefined behaviour.

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> 226 Is Use l n supposed to be an access to the first n bytes from l?  That's not realistic - many accesses will be to non-prefixes of allocations.
---------------------------------------------------------------------------------
Reply:
------

It's a random access of a single value at (intuitively) location `l + n`, where `l` is an abstract memory address.

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> - why insist that there is a Dealloc?  A program that runs indefinitely using a persistent allocation does not intuitively have a temporal memory safety violation.
---------------------------------------------------------------------------------
Reply:
------

We agree that whether TMS covers existence of a Dealloc event is debatable.
========
-TODO: is there existing work that uses this? i think our MSWasm paper perhaps
               no, the monitor in mswasm does not enforce this.
               we may as well get rid of the requirement. But alas, we are able to show something more interesting...
========
However, this debate is orthogonal to the main goal of the work, since this enforcement of Dealloc events does not affect the usage of the compositionality framework at large.
However, it does complicate the case-study in the sense that the static semantics of `L_{tms}` enforces this requirement.

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> - are locations l supposed to be concrete addresses, or unique allocation IDs, or combinations of the two?
---------------------------------------------------------------------------------
Reply:
------

Given the sandboxed setting, a location only makes sense together with an appropriate tag that witnesses the kind of heap this location points to.
Then, the location represents a concrete location in the respective heap.

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> If they're concrete addresses, it's again weird, as any real implementation will reallocate at the same address.
---------------------------------------------------------------------------------
Reply:
------

Monotonic buffer allocators do not reallocate at the same address and are arguably the most simple allocator, yet very useful in practice, e.g., for hot loops that allocate each iteration.
We would like to point out that the concrete allocation strategy is orthogonal to the main line of work of this paper. 
The case-study is simple enough to keep the workload for the proofs not relevant to the grand-scheme of the compositionality framework, but relevant to the intricate technical setup to make use of it.
While an extension to support a more involved allocator - or even polymorphic memory allocators - does add a great amount of possibly interesting technical detail, the key theorems in the paper would not change at all from an observers perspective. (of course, the proof does change given the cross-language relations need to be patched accordingly, but existing work has already shown how to do this kind of complex proofs)

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> In all of this section, it's unclear where the security tag information is supposed to come from.  Are we supposed to imagine an annotated operational semantics that propagates sensitive tags?   If so, are control-flow choices on a sensitive value supposed to infect all later computation?
> [...]
> The idea that any access in compiled code can be uniquely associated to either the component or context also seems naive: in reality there'll be a nontrivial calling convention, with both caller-save and callee-save registers; how are those accesses supposed to be labelled?  Are we presuming that there's no inlining or other optimisation that crosses those boundaries?
---------------------------------------------------------------------------------
Reply:
------

The case-study of our work needs a bit of setup to fulfill the assumptions of the framework, e.g., that the compilers used in the case-study are secure.
This setup is proven with standard techniques and, thus, uninteresting for the sake of presentation of this work.

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> 252 "sCCT may seem overly strict" - yes, it does.
---------------------------------------------------------------------------------
Reply:
------

We would like to point out - as done in the paper as well - that modern processors have a data-independent timing mode that, when turned on, aims to provide a guarantee that a certain set of instructions runs in constant-time, just like sCCT.

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> Do the monitors exactly characterize the properties?   You state only one direction of implication.  If not, why are they useful?
---------------------------------------------------------------------------------
Reply:
------

Focussing on the case-study, the secure compilation statements used here talk about traces satisfying a property by being an element of that property.
The established implications allow to lift this to the monitor-level, where inductive reasoning is much more useful than on just traces, and thus the other direction of the implication is not necessary.

==========================================================================================
Reviewer 2
==========================================================================================

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> The main weakness of this work is that the form of composition is limited. It requires the compilers (or compiler passes) to use the same trace model and are robustly safe, which limit the applicability of the results.
> The framework set up here may not be suitable for studying composition of other forms of properties (e.g., hyper-properties) or not robustly safe compiler composition.
---------------------------------------------------------------------------------
Reply:
------

Wrt the first point, we'd like to to point out that section 4.3 discusses this and shows how to extend the framework to support variying trace-models between languages. Given the security relevance and applicability of the framework without the extension (as witnessed by the case study), we chose to investigate this extension from a case study perspective in future work.

Nothing in the general compositionality theory we develop prevents considering compilers that preserve hyperproperties though. In fact, the framework supports reasoning about the composition of compilers preserving hyperproperties but the paper does not demonstrate this in the case-study since the proofs would be more involved.
Because of this, we overapproximate a well-known hyperproperty, i.e., cryptographic constant-time, using an ordinary trace property, i.e., strict cryptographic constant-time, which yields more manageable proofs.
This is also a common technique for the verification of hyperproperties.

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> Finally, the Coq formalization is not complete. It is unclear if there are fundamental difficulties in completing the proofs, or it is due to the limitation of time.
---------------------------------------------------------------------------------
Reply:
------

TODO -> focus on the pros!
   already done?
The Coq proofs concern the main technical results (section 4, parts of sections 5 and 6 as well as 3), and these results are all completely covered by the Coq development.
What is missing in terms of Coq proofs is the secure compilation proofs, each of which can easily take 20klocs per proof, as demonstrated by the work of El-Korashy et al, CSF'22.
We plan to study the modularisation of these proofs in future work, but since they follow a known pattern (albeit very complex to mechanise), we do not believe the lack of this mechanisation to be a significant drawback.

==========================================================================================
Reviewer 3
==========================================================================================

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> I was particularly puzzled by the composition property.  Naively, it seemed straightforward to me that if a pass preserves A and B, then it preserves A; and if two passes preserve A, then their composition preserves A; given this, it seems straightforward that composition preserves (at least) the intersection of properties.  I'm sure there is something more to the results in the paper, but I wasn't entirely sure what; a clarification would be very helpful.
---------------------------------------------------------------------------------
Reply:
------

Your intuition is entirely correct and we agree that the results can seem intuitive to expert readers.
Despite their intuitiveness, as the other reviewers acknowledge as well, the results are important, and their importance can be demonstrated in a concrete setting, where the framework is applied and the paper contains a case-study that does this.
Also, an intuition that may be harder to convey is: what does it mean to perform the intersection of 2 properties *in practice*? A reason we have to provide such a rich case study is also to give a better intuition of this fact.
We can clarify this point in the related section.

TODO: drop next sentence?
From a technical standpoint, instantiations of the compositionality framework are non-trivial in the sense that secure compilation proofs need quite a lot of technical setup, as demonstrated by the case-study from the paper, which takes the vast majority of space in our supplementary material.

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> I would in particular like to understand this better from the perspective of theorems 12 and 13.  What is really going on in these two, and can you sketch the proof?  It seems that the theorem here would say that /any/ function that is MS would, when composed with the lowering to Lscct, also be Lscct; is that the case?
---------------------------------------------------------------------------------
Reply:
------

The theorems do not talk about any function/compiler γ, but about concrete instances that have been set-up in the case-study.
But, most of their definitions are left out given their straightforwardness, e.g., the beginning of section 6.4 shows what the compiler has to do to enforce scct, but leaves out all the "recolorings" from yellow to red.

The proof for theorem 12 is a standard secure compilation proof that uses a trace-based backtranslation technique to get a source-level context that behaves similar to a given target-level adversary.
The proof of theorem 12 is entirely similar in structure to theorems 6, 7, 9, and 10. 
As for theorem 13, this uses previous results from the compositionality framework and is, thus, more interesting from the perspective of your question.
With hopes to make it more readable, we decompose `γ^{L_{tms}}_{L_{scct}}` as follows:
 - `γA` is `γ^{L_{tms}}_{L}` 
 - `γB` is `γA` composed with `γ^{L}_{L_{ms}}` 
 - `γC` is `γB` composed with `γ_{CF}` 
 - `γD` is `γC` composed with `γ_{DCE}` 
 - `γE` is `γD` composed with `γ^{L_{ms}}_{L_{scct}}` 
The proof now works as follows:

 - Unfold the definition and simplify:
     - Let `π` be an element of `ms ∩ scct` and `p_{tms}` an `L_{tms}` component.
     - (H1) Assume that `p_{tms}` robustly satisifies `ms ∩ scct`.
     - Goal is `γE (p_{tms})` robustly satisfies `ms ∩ scct`.
- Apply Theorem 12 on the goal, changing it to `γD (p_{tms})` robustly satisfies `ms ∩ scct`.
- Apply Theorem 9 on the goal, changing it to `γC (p_{tms})` robustly satisfies `ms ∩ scct`.
- Apply Theorem 10 on the goal, changing it to `γB (p_{tms})` robustly satisfies `ms ∩ scct`.
- Apply Theorem 8 on the goal, changing it to `p_{tms}` robustly satisfies `ms ∩ scct`.
  -> solved by assumption (H1)

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
> The definition of strncpy is not the one I'm used to; the one I know pads `dst` with 0s.
---------------------------------------------------------------------------------
Reply:
------

We admit that the paper presents a more naive version of strncpy for sake of presentation.
We will add a note for this.


