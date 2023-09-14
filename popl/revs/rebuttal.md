
# Author Response for Submission 67: Secure Composition of Robust and Optimising Compilers

First of all, we would like to sincerely thank every reviewer for putting in their hard work.
We are pleased about the high-quality of the reviews and appreciate both your suggestions and questions, which we address for each reviewer below.
Prior to that, we want to explain some general concerns applying to all reviews.

- The main results of our paper are about the compositionality of secure compilers, which we have Coq'd up at the time of submitting the paper. Missing Coq proofs mainly involve the case-study, but the paper does not claim to have Coq'd the language definitions, their properties, etc.
- The compositionality scales to arbitrary properties, not just trace properties. Classes of properties are kept as general as possible and there is no restriction being made on the shape of a class without talking about a concrete one. This should also entail hyperproperties, since they are classes themselves and enjoy closedness on intersections, i.e., intersecting hyperproperties yields other hyperproperties.
- The optimisations chosen, namely Dead-Code Elimination (dce) and Constant Folding (cf), are traditional compiler optimisations. While they are simpler to define in comparison to other optimisations, we have no reason to believe that the compositionality framework breaks apart when scaling this to other passes.


## Reviewer A

We think it is important to not get lost in theory and appreciate your critical thinking about whether our theoretical framework is applicable to practical compilers.
This is a big concern for us as well.
Unfortunately, developing a compiler with formal methods is a task that has a huge workload (see CompCert).
While there is no existing "practical", formally secure compiler, we believe that our framework allows to incrementally build such a thing, because of the separation of concerns that one gets from the compositionality framework.

### General comments

> However, the approach does not study the optimizations of any real compiler and hence it is not clear if the approach would be applicable in state-of-the-art compiler development. 

The paper studies dead-code elimination (dce) as well as constant folding (cf) in the setting of (formally) secure compilers.
So far, the only practical compiler that involves formal methods is CompCert, but it is not proven secure.
Nevertheless, CompCert, as well as not-formally proven compilers, such as gcc or clang, perform dce and cf.
dce and cf are foundational compiler optimisations that any optimising compiler makes use of.
Therefore, we believe our approach is as applicable as formal methods when it comes to state-of-the-art compiler development.

> Undefined behaviors play a key role in developing optimizations in the state-of-the-art compilers. I wonder if these behaviors would affect the compositionality properties. 
> It is possible that the individual components are compiled following different sequences of optimizations and linked later. 

We believe this is a very interesting point that is, however, a little outside the scope of the paper.
For the framework presented in the paper, undefined behavior would be encoded in the property/-ies of interest and, therefore, be preserved in the intersection of property classes.
We are planning to do a follow-up paper where we investigate more aggressive, realistic optimising compiler passes that (1) may exploit undefined behavior, (2) reorder code - and thereby reorder events on the trace, (3) memory layout reording, and so on.

> You have chosen constant time cryptography and memory safety. It would be useful to discuss the motivation behind selecting these two security properties with their similarities and differences.
We believe that the paper addresses this in the introduction: They are key security properties for ensuring confidentiality.

### Questions

> (1) Is it possible to model the optimizations in GCC or LLVM in your approach?

Yes, the paper does this for dce and cf, which both GCC and LLVM do.
We would appreciate further clarification about particular optimising transformations that you've had on your mind.
While it is unlikely that we can extend the formalisation in the given time-frame to account for another optimisation, we do think this space warrants future work.

> (2) Is your approach applicable to or can be extended for in hyperproperty based security properties? 

Yes, classes are simply sets of properties.
We verified that the proof of the sequential composition theorem also works for classes of sets of hyperproperties.
We agree that the paper should be rephrased to improve the description of classes and why the formulation is general enough, i.e., why the sequential composition theorem supports any set whatsoever (even liveness).

> (3) Do you handle dynamic languages with managed runtime? Particularly, managed runtime systems use garbage collection to deallocate memory. Does it impact your compositionality scheme?

While we haven't done an analysis of something like this explicitly, our intuition is that our compositionality framework is general enough to capture this.

### What will change

- Add to future work section that we will look at more sophisticated optimisiation passes.

## Reviewer B

While we do not agree with the reasoning for the decision to strongly reject our submission, we strongly appreciate parts of your criticism and will improve the paper as outlined below.

### General comments

> While this work sets out to study an important problem: the compositional properties of secure compilation; the technical development is straightforward and the case studies are simplistic.
> The contribution is incremental given existing work in secure compilation.

From our literature review, we were not able to identify work that discusses the composition of (formally) secure compilers.
The compositionality of secure compilers has not been discussed before, and, as you said, it is an important problem to look at.

> The properties examined is a subset of the properties that secure compilation aims to preserve. 

Note that, while the universal quantification in the sequential composition theorem restricts properties to be part of a certain class (=set of properties), the class is arbitrarily fixed.
For example, in the case-study, it is fixed to the class of memory safety properties which is later composed with the class of strictly cryptographic constant timeness.

> The composition is sequential composition only. 

The paper also discusses "upper" as well as "lower" composition, which fascilitates multi-language reasoning on secure compilation.
This is something we don't get from just sequential composition and allows to build more practical secure compilers incrementally.

> In terms of sequential composition, it would be interesting to show the result of composing a compilation pass that violates a certain property pi and a later pass hardens the target to ensure that property. 

We strongly agree that this is an interesting point and intend to improve our submission with regards to this.
While, under the given time-frame, we cannot change the formalisation of the case-study, we will add a paragraph discussing this by two example compiler passes used in practice.
Briefly, if the second compiler generates programs that always violate the property that the first ensures, then the preserved class of properties is actually empty, since the intersection is disjoint!
So, the theorem as stated still works, i.e., it is *not* unsound, but it may trivialize, which should better be emphasized in the paper.

> Similar to the above comment, another important form of composition not considered by this work is composing/linking components that are compiled  through different compilation pass. Especially when these components have shared state.   

The robust preservation criterion universally quantifies the contexts and considers a single program component, so the framework encompasses contexts that result from different compilation passes, different compilers, or from writing them by hand.
We are unsure how the presented compositionality framework seems to fail to handle this and we would need further clarification.

> Sections 5 and 6 set up toy languages and compiler passes, which made the proofs straightforward. What are the challenges of establishing the theorems? Are there interesting proof techniques used?

Since the case-study serves as motivating example for the compositionality framework, we think it is important to discuss the framework in more detail instead of the formalisations of more-or-less standard programming languages.

> Definition 3.1, "at most one Alloc/Dealloc l;t;sigma" is imprecise. This could allow two Alloc/Deallocs of the same location, with different tag. If read strictly, it does not allow memory reuse, which is commonly done in low-level languages. 

We believe the concrete formalisation of memory addresses is orthogonal to the goals of the paper/the case-study and merely an implementation detail.
The main interest of study is the compositionality of secure compilers, not how to make a memory-safe programming language.

> The Rule tms-trans seems to allow the same location to be allocated twice. Is this correct? 

`tms-refl`, `tms-ign-trans`, as well as `tms-trans` define the reflexive-transitive closure of the TMS-monitor step, while filtering empty events.
They do not talk about locations at all.
Maybe you meant `tms-alloc`, which has premises that ensure an address is not allocated already, i.e., it cannot happen that there is an allocation for the same location.
Due to the sandboxing (see line 645 in the paper), the work models memory addresses as number + tag indicating what heap the address lies on.
The technical development can be extended to allow re-allocation of the same memory location, but this complicates the proofs unneccessarily, since the main goal is not to build a memory-safe lanugage, but to investigate compositionality of secure compilers.

> The monitor composition simply runs both monitors, which is not optimal. 

While optimality may be interesting, it is also orthogonal to the goal of the paper, which cares about doing the correct thing.
Subsequent work can optimize this, if necessary.

> Why is the monitor composition interesting? It is also unclear how the monitor connects tightly to later sections of the paper.

The composition of temporal and spatial memory safety monitors requires the monitor composition to get a monitor for memory safety (intersection of tms and sms).
We agree that this could be made more explicit in the paper.


> The rules on page 14, the return values seem arbitrary for rules of operations with ill-defined behavior. For example, when setting a memory location that doesn't exist, why return the value of the expression to be written to memory? Similarly, why deletion return 0? Why deletion does not check for existing of the location, like the set rules? It may not handle double free properly. 

The purpose of the case-study is to allow memory-unsafe behavior, i.e., execution should not get stuck if there is some kind of, e.g., memory-safety violation.
While we fail to see how the `e-dealloc` rule does not check for the existence of memory locations like the `e-set-*`/`e-get-*` rules, we do want to emphasize that `e-dealloc` does not need to change or check the heap(s) in any way, since it/they is/are modeled as one big arena.
One could instead add the data the pointer points to into Δ instead of describing a two separate heaps. However, our formalisation models sandboxing more faithfully.

> The coloring of the paper is distracting. 

We want to note that past iterations of POPL already have several papers that make extensive use of color.
Nevertheless, removing color is a minor change that should not influence the acceptance of the paper.

> Figure 1, allowing $\varepsilon$ events to be arbitrarily inserted does not account for timing behavior. Is this intended? 

Yes, this is intended, since this precise timing is abstracted away by the data independent timing mode + techniques used in the FaCT paper (Cauligi et al., 2019. https://doi.org/10.1145/3314221.3314605).

> Definition 3.6, the monitor semantics is not introduced at this point. 

The paper has several monitor semantics and Definition 3.6 generically introduces what monitor satisfaction for each of the defined monitors means.
To not re-introduce this definition several times (for tms, sms, ms, scct, and scct+ms monitors), we introduce it here and give an intuitive characterization of the definition in the underlined text, e.g., the star-squiggly-arrow corresponds to "[...] monitor can step to [...]".

### Questions

> can the theorem be applied to the case where one pass violating a property and another pass re-establishes it?

Yes, see earlier discussion. In short, one has to be careful that the intersection does not become empty, but the theorem is nonetheless applicable and sound.
It's been proven in Coq.

> What's challenging?

The compositionality framework is simple enough to appear as straightforward, which is a good thing.
The catch is that building (formally verified) secure compilers is notoriously difficult, as backed up by an extensive number of secure compilation literature.
With the presented compositionality framework, the burden of proving the composed compiler of secure compilation passes as secure is reduced dramatically.

### What will change

- Emphasize the role of classes and why the compositionality framework is general enough.
- Undermine the relevance of the combined monitor and make it clearer how, why, and where it is needed.
- Incomporate an example where a second secure compilation pass introduces violations to the property the first pass secured against.

## Reviewer C

### General Comments

### Questions

### What will change


## Reviewer D

### General Comments

### Questions

### What will change
