
# Author Response for Submission 67: Secure Composition of Robust and Optimising Compilers

First of all, we would like to thank every reviewer for putting in their hard work.
We really appreciate the high-quality of the reviews and your insightful suggestions and questions.
We address the latter, for each reviewer, below.
Prior to that, we want to address some general concerns that are shared amongst different reviews.

- **Mechanisation and Incrementality of the Results** (reviewer B, C)

The main results of our paper, which is presented in Section TODO, are about the compositionality of secure compilers. All these results have been Coq'd up at and they can be found in the supplementary material. Neither of these results do [TODO ] rely on Admits.
While it is true that we use the theory (and the Coq formalisation) of Abate et. al. [TODO cite number], we do not believe this work can be considered incremental. After all, no existing work tackles the problem of identifying what security property is preserved by the composition of secure compilers (despite the secure compilation community, and the reviewers as well, identify this as an interesting problem).
The missing Coq proofs mainly involve the case-study, but we'd like to point out that the paper does not put forth this claim. 

- **Limitations of the Composition Theory** (reviewer A, D)

The compositionality property of Theorem [TODO] is presented for arbitrary classes of properties, not just trace properties. Classes of properties are kept as general as possible and so the theory works for hypersafety, hyperproperties, relational hyperproperties, and so forth. 
We will make this clearer in the presentation of the main results.
An interesting point is that since hyperproperties enjoy closedness on intersections, intersecting classes of hyperproperties yields other hyperproperties. We will clarify this point further as well.

- **Real-world Application of the Results** (reviewer A, C)

The optimisations chosen, namely Dead-Code Elimination (dce) and Constant Folding (cf), are traditional compiler optimisations. While they are simpler to define in comparison to other optimisations, we have no reason to believe that the compositionality framework breaks apart when scaling this to other passes.
Individual secure compilation proofs for these more realistic passes will (naturally) get more involved.


## Reviewer A
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

Yes, we believe so, and this is the reason why in the paper we chose DCE and CF, which both GCC and LLVM do.
We would appreciate further clarification about particular optimising transformations that you've had on your mind.

Some optimisations may break security properties.
For example, by relying on undefined behavior, a necessary security check may be removed by an optimising compiler.
Even (a more sophisticated) DCE could lead to confidentiality violations when it removes code that would override secret memory. 
The investigation of these pecularities is outside the scope of this work, whose main goal is to provide a tool for composing compilation passes.


> (2) Is your approach applicable to or can be extended for in hyperproperty based security properties? 

Yes, as mentioned in the general points above, classes are simply sets of properties.
We verified that the proof of the sequential composition theorem also works for classes of sets of hyperproperties.
We agree that the paper should be rephrased to improve the description of classes and why the formulation is general enough, i.e., why the sequential composition theorem supports any kind of property (even liveness).

> (3) Do you handle dynamic languages with managed runtime? Particularly, managed runtime systems use garbage collection to deallocate memory. Does it impact your compositionality scheme?

While we haven't done an analysis of something like this explicitly, our intuition is that our compositionality framework is general enough to capture this.

### What will change

- Add to future work section that we will look at more sophisticated optimisiation passes.

## Reviewer B

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
One could instead add the data the pointer points to into Δ instead of describing two separate heaps. However, our formalisation models sandboxing more faithfully with this separation.

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
The catch is that building (formally verified) secure compilers is notoriously difficult, as backed up by an extensive number of secure compilation literature, so it can be quite involved to fulfill the assumptions of the compositionality theorems, as demonstrated in the case-study.

### What will change

- Emphasize the role of classes and why the compositionality framework is general enough.
- Undermine the relevance of the combined monitor and make it clearer how, why, and where it is needed.
- Incomporate an example where a second secure compilation pass introduces violations to the property the first pass secured against.

## Reviewer C

### General Comments

> - The work is very foundational, granted, but the examples are very small and are not realistic compilers, so the main contribution that remains (if the formal proof is not really finalized, and if the concrete compiler only deals with toy languages) is the formal framework to talk about these results.

We agree with this.
While the programming languages in the case-study are quite restricted, we do have - at least on paper - a full proof that the compilers are secure.
As of now, we are not aware of a practical implementation of a secure compiler that is formalized all the way (i.e., you can *run* the formalised version of the compiler), but MSWasm (Michael et al, 2023. https://doi.org/10.1145/3554344) comes close.
We anticipate that our compositionality framework allows for an easier, incremental development of more realistic compilers.

> - 211: I think an important notion that you do not highlight is that the language of traces must be the same for the source and target

This may seem like a restriction, but using standard techniques from the secure compilation literature (Abate et al., 2021. https://doi.org/10.1145/3554344), the theory can be lifted without much friction to account for different trace models.

> - 503: are you reversing the traditional order of the composition operator?

Yes. Unfortunately, there are two communities that use either the one or the other order and view it as "the traditional" order.
We are not opposed to simply swapping this, or maybe just add a footnote detailling how this composition should be interpreted. (it becomes clear from the color, but having it explicit is likely better)

> - 512: you have a little bit of space left, so it would've been good to give an intuition of what exactly is difficult
> - 547: same thing, I'm left wondering whether this is a deep result at all

We agree that more discussion improves both presentations dramatically.

> - 623: what is the $t$ in $\mathbb N_t$?

$\mathbb{N}_t$ is the "concrete" syntax of the type.
We thought it may make sense to disambiguate the type of natural numbers from the set of natural numbers.
However, looking at the submmission again, this appears to just add clutter to the presentation.

> - 666: I think you need to make it clear that some rules are omitted (e-get-\not\in, and e-set-\in) -- it took me a while to figure out what's going on

Agreed, it should be stated explicitly that only a fraction of the rules are presented and that the interested reader can find the full picture in the technical report.

> - you say e-set-\not\in returns a garbage value, in this case... v? why is it garbage? why not unit? (assignments in C return the assigned value, so this seems perfectly non-garbage)

You are right that the word "garbage" is not fitting and we will adapt the text accordingly.
We use the word in an attempt to convey the intuition that no write to memory actually happened, even though it appears so (because the rule yields `v`).

> - 767: I never understood how the addition of L_ms enhanced readability

Fair criticism.
We should rephrase this paragraph and write that we want to make the fact explicit that the compiled code of $L_{ms}$ is instrumented to be memory-safe.

> - 790: why not change the original get and set and add an additional argument to these events?

That is another option. If the presentation is better with the additional argument instead of the hat $\widehat{\cdot}$, we'll gladly change it.

> - 805: do you mean INactive?
> - 805: text is confusing, because the rule that emits Binop n is not shown -- make it clear this is omitted; another nit: you have two styles for switching over whether the CPU mode is enabled; in one you use 0 in the conclusion of the rule, in the other, you use m \neq 0 in the premise; it would be clearer to use two constant on and off

Yes, it should be *in*active and we think the presentation of this benefits from using `on` and `off` instead of $m\neq 0$ and $0$.


### Questions

> - Clarify novelty of monitors and the trace projections

The monitors use standard techniques to identify unsafe traces.
In most existing work, monitors are used to define the property at hand and monitor satisfaction is exactly the same as trace satisfaction, in this case.
In our work, while the techniques for monitors are not novel, the way they are used in order to do property composition and reason about this in the context of secure compilation is novel to that area of research.
The way the projections of one trace model to another are set up enables definitions and satisfaction proofs of properties in a modular fashion.
Moreover, we were unable to identify existing work that proves that monitor satisfaction implies trace satisfaction, where the property is defined with just some condition instead of the monitor.

> - Clarify what was difficult in the proofs and explain where the subtleties are -- right now it seems like some of the results might not be stating anything very deep (I might be under this impression because your paper is very well written!)

The proofs for the compositionality framework are easy, even in Coq.
Proving a compiler secure (i.e. robustly preserving) is notoriously difficult, as seen by numerous works in the secure compilation area.
So, in order to fulfill the assumptions one needs at least two formally secure compilers.
The presented framework allows to incrementally build more and more complicated compilers by focussing on the security of just an individual compilation pass.
While the result may not be difficult or "deep", it is most certainly of great use to scale secure compilers to more practical applications.

> - Give a status report on the Coq proof; surely you must've made progress since the submission, where are you at now?

The compositionality framework is formally verified in Coq.
While it is most certainly nice to also formally verify all parts of our case-study, we don't believe this is a necessity for acceptance of our submission (the most important results, the compositionality parts, are Coq'd).
We have paper proofs for the case-study and it merely serves a motivation to show that our compositionality framework actually works and is of use in practice.

> - Discuss applicability to more involved compilers.

We think the submission may benefit from adding this discussion.
Anyhow, our case-study shows that our framework scales to compilers with many passes as well as compilers with optimising passes, whose order may be swapped.
The concrete complexity of any compilation pass involved in a composition is orthogonal to our work.
Nevertheless, we strongly believe that secure, more complex/realistic compilers can be developed much faster with our framework.
Without it, one would have to prove the whole compilation chain end-to-end, while our framework allows for modular, more localized reasoning.

### What will change

- Fixing the typos!
- Add more discussion about the compositionality theorems.
- Change $\mathbb{N}_t$ to $\mathbb{N}$
- Everywhere were we omit rules: State this explicitly.
- Change descriptive text of e-set-\not\in to emphasize that no write happens. `v` is not really a "garbage" value, get rid of this confusing terminology. 
- Rephrase paragraph about $L_{ms}$: the compiled code is instrumented to be memory-safe.
- Change data independent timing mode state to either `on` or `off`.
- Add discussion on applicability of the framework.
- Add hyperlinks to the Coq development of the respective proofs.



## Reviewer D

### General Comments

> This paper studies the composition of robust safety properties and of robustly safe compilers. 

While our examples are only looking at safety properties, the compositionality framework itself is general enough to cover arbitrary properties.

> While the paper does formalize "a theory of composition of secure compilers", focusing exclusively on robust preservation of properties, it  does not include any discussion about the limitations of this approach. 

This is most certainly true.
In particular, it is interesting to discuss what happens if the second compilaton pass introduces vulnerabilities that the first pass fixes, as also pointed out by reviewer B.

> More specifically, the framework in the paper requires that all security properties and their monitors be defined on the same trace model.

We believe this has been thoroughly investigated in the secure compilation literature (Abate et al., 2021. https://doi.org/10.1145/3554344).
Allowing different trace models, one can apply the techniques presented in there to make our framework applicable.

> in particular, the languages selected are quite close with many shared definitions (see Sec 5.1).

While we agree that the languages are syntactically very similar, this is merely an artifact to keep the proofs small.
The complexity/"uniqueness" of the concrete languages have no impact on the presented compositionality framework.

> - The choice to focus on sCCT instead of CCT is troubling. Of course, CCT is a hypersafety property so the paper's strategy of using monitors for checking would not have worked. But switching to Strict CCT, which requires that no secret _ever_ appear in a trace, seems too restrictive and it feels like the choice was made just so we can use monitors for checking.

sCCT is one possible overapproximation of CCT which can be made less restrictive.
If done so, the concrete details of the proofs for the CCT preservation - of course - change.
However, the usage of the presented composition framework would stay exactly the same.

> - The paper claims upper and lower composition as a contribution (and the lack thereof as a weakness of prior work, end of Sec 7.1). But the paper spends very little time motivating why these forms of composition are important or challenging. 

We agree and will add an appropriate discussion of this.

> - There are some questionable decisions about which formalism to include and which to exclude. For a paper about secure compilation, there is not so much detail about the compilers (and the type systems) themselves. This seems especially concerning for the very first pass, from $L_{TMS}$ to $L$, 
> since the type system is not standard and dynamic enforcement is not necessarily straightforward.
> [...]
> If a piece of formalism is indeed obvious, the authors should consider trading that space to treat the content that is _not_ straightforward.

We do have the impression that the precise language definitions are not interesting enough to warrant inclusion in the paper, i.e., that it is enough to mention the high-level properties that, e.g., could in parts be established by any work on memory-safety instrumentations or CCT work. 
The most important aspect of our submission is the compositionality framework and the concrete details of the case study can be looked up in the technical report.

> - 213: Why use the powerset class of $\pi$ instead of the singleton class $\{\pi\}$?

In short, the equivalent hyperproperty/class of a property is its powerset.
If the class is a singleton, the intersection will very likely be empty and the compositionality framework would be rather useless.
For details, refer to Clarkson and Schneider, 2008. https://doi.org/10.1145/3554344

> - 221: Consider showing the code exercising the bug;  describing the code in prose makes it sound more complex than it is.

We show the code and explain it. Do you argue for omitting the explanation to enhance clarity?

> - 261: Isn't requiring deallocation a liveness property?

This is a technicality, but yes. However, since the considered programs terminate, it is possible to check this.
Nevertheless, since leaking memory is not a memory safety violation, it may improve the presentation to remove this requirement.
Note that we've verified that the tms-monitor satisfaction implies the satisfaction of the presented tms property, with the deallocation requirement.


> - 335: Should the type of allocated and freed be $\wp(L \times t)$?
>  The use of $\in, \notin$ on 345, 348, 353 suggest so.

We admit the confusion that comes from a slight abuse of notation.

> - 455: $\textbf{Any}$ is not really any event, just the private ones,
>   so a label like $\textbf{Leak}$ might be more suggestive.

We agree that changing the name from $\textbf{Any}$ to $\textbf{Leak}$ conveys the semantics in a more meaningful way.


> - 492: Have the results in *Sec. 4* been proven over arbitrary trace models,
>   or only over the model described in *Sec. 3*?

The results here work for arbitrary trace models, there is no connection to the case study or Section 3, i.e., this works for any kind of property and the quantification on classes is arbitrary.

> - 594: $\vdash \gamma^{L}_{L + L} : \mathbb{C}_{1} \cap \mathbb{C}_{2}$ doesn't typecheck.

We do not see why this does not "typecheck".

> - 605: What precisely does it mean for the languages to assume CCT holds?

There is no leakage at all.

> - 606: I find the messaging in this paragraph to be a touch inconsistent.
>   It starts by saying that programmers shouldn't be thinking about CCT,
>   and they don't have to, thanks to timing-independent hardware.
>   But the paragraph finishes by emphasizing that 
>   $L_{scct}$ allows the programmer to *disable* CCT protections,
>   which disagrees with the previous suggestion.
>   I suspect that these are intended to be different types of programmers,
>   but perhaps that distinction should be made clear in a transition.

You are right that this paragraph talks about different types of programmers and we do have to rephrase it to enhance clarity.

> - 688: "... have two cases": meaning, each has an *additional* case not shown in the figure, correct?

Yes, the concrete details can be looked up in the technical report.

> - 703: After `Call ? foo v`, should we have `Return ! v` instead of `Return ? v`?

No, this is not a typo. The `?` signals the switch from context to component, while the `!` signals the switch from component to context.
However, there is a typo in line 704, where the `Return ? v` should be a `Return ! v`.

> - 759: "If the array bound to `x` was allocated ...": should this say "deallocated"?

Yes

> - 780: Is it really that the languages always have timing independence turned on, or is it that those languages don't even have a notion of timing independence? There is nothing in the semantics of the languages that mentions timing or secrecy. It is just one implementation (i.e., the compiler in *Sec. 6.4*) that establishes the assumption.

You are right that it is one possible implementation and in line 780 we provide an intuition for that implementation.

> - 874: Is a "strikethrough edge" the same as a solid edge?

Yes

> - 904: This compilation strategy seems sensible for simple functions,
> but since no details about $L_{tms}$ or its type system are given,
> it is hard to assess whether it should hold in general.

The concrete details are uninteresting for the sake of the presentation here and the interested reader can look them up in the technical report.
We are nevertheless going to address your questions here:
> > Are there higher-order functions? 

No

> > How are capabilities (assuming the types really are inspired by L3) compiled

No, the type system is more restrictive and this renders the proofs simpler. 

> > and checked dynamically?

L_tms is checked statically, anything else has (explicit, i.e., the programmer has to insert them) dynamic typechecks.

> > Or is there a restriction on function types?

Pointers cannot be passed. Otherwise, they would need to be mershalled to allow transfer from one sandbox to another. Moreover, the type system would indeed need an extension that tracks capabilities.

We are aware that this is a very restrictive setting, but it nevertheless allows memory unsafe behavior that allows for an interesting case-study.


> - 1113: While upper and lower compositions are claimed as a contribution,
> their importance was not sufficiently motivated.

We strongly agree that they need more explanation and discussion.

> > Why are these forms of composition important?

They allow modular extension of secure compilers to model compiler frameworks like LLVM.

> > Do you suspect that they were provable in prior work but never studied,
> > or was there a fundamental limitation that your framework has lifted?

We have not seen this studied in prior work, so our framework does not lift an existing limitation, it rather presents a novel approach.


### Questions

> What are the limitations of this approach?

Devising secure compilers is notoriously difficult and takes a lot of time.
Moreover, one has to be careful that the intersection of classes does not become empty, which can happen if the first compilation pass secures against property A, but the second pass introduces source-code instrumentations that violate A.
We'll add more detailed discussion about this in the paper.

> How should one approach designing the common "target" trace language?

In similar fashion to (Abate et al., 2021. https://doi.org/10.1145/3554344)

> Does one need to know ahead of time which properties will be of interest?

Yes and no.
Yes, because for the composition itself, you do need concrete instances of classes that apply to your setting, but this class could be arbitrarily large.
No, because it is not a roadblock to extend the models at a later point in time.

> Are there any subtleties in either the type system or compilation of $L_{tms}$?

No, we believe our work there is entirely standard and, because of this, did not bother to present the details in the paper, but keep them for the technical report.


### What will change

- Add emphasis that the framework works for arbitrary properties.
- Add discussion on limitations of the compositionality framework. Especially concerning the upper and lower composition. Highlight that one has to ensure that the intersections of classes do not become empty.
- Get rid of "as you would expect", "... is straightforward", etc.
- Add quantifiers to disambiguate definitions.
- Add paragraph on how sCCT overapproximates CCT and what kinds of programs would not satisfy sCCT while satisfying CCT.
- Fix the "typing" of monitor states (e.g., line 335)
- Rewrite $\textbf{Any}$ to $\textbf{Leak}$.
- Rephrase paragraph at 606.
- Fix typos.
- Change wording from "strikethrough edge" to "solid edge".
