
This is a living document served for internal documentation.
Some helpful definitions:

- `γ` is a compiler, i.e., a *syntactic* translation from one language into another
- `π` is a set of traces, i.e., a property
- `Π` and `Ξ` are sets of properties, i.e., a hyperproperty. We may also refer to it as a class, in particular when we use the metavar `Ξ`
- `w` are whole programs
- `p` and `C` are partial programs
- `whole p` is a syntactic check that `p` is whole
- `link(C,p)` is a syntactic "glue" operation. May fail, otherwise yields a new partial program
- `sat(w,π)` is `behav(w) ⊆ π`
- `Rsat(p,π)` is `∀ C w`, if `link C p = Ok w` and `whole w`, then `sat(w, π)`
- `hsat(w,Π)` is `behav(w) ∈ Π`
- `Rhsat(p,Π)` is `∀ C w`, if `link C p = Ok w` and `whole w`, then `hsat(w, Π)`
- `TP(γ, π)` is `∀w`, if `sat(w, π)`, then `sat(γ w, π)`
- `HP(γ, Π)` is `∀w`, **iff** `hsat(w, Π)`, then `hsat(γ w, Π)`
- `CTP(γ, Ξ)` is `∀π ∈ Ξ`, `TP(γ, π)`
- `RTP(γ, π)` is `∀p`, if `Rsat(w, π)`, then `Rsat(γ w, π)`
- `RHP(γ, Π)` is `∀p`, **iff** `Rhsat(w, Π)`, then `Rhsat(γ w, Π)`
- `RCTP(γ, Ξ)` is `∀π ∈ Ξ`, `RTP(γ, π)`

- `~` is a cross-language trace relation
- `σ_~(π)` is an induced relation based on `~` from target to source properties. Defined as `{ s | ∀t, if s ~ t, then t∈π }`  
- `τ_~(π)` is an induced relation based on `~` from source to target properties. Defined as `{ t | ∃s, s ~ t and s∈π }`  
- Both `σ` and `τ` have a straightforward mapping into hyperproperties: `σ(Π) = {σ(π) | π∈Π}` (dito for `τ`)

Note that literature commonly focuses on compiler properties, such as TP/RTP, with `π` universally quantified.
Also note the `iff` in the hyperproperty-cases. (see Abate et al., 2021)

# Things that work

## ...and are relevant
1.	composition is relevant for specific properties (which are singletons or subsets)

 

## ...and are "irrelevant"
This section sketches results that are "irrelevant".
Either they are deemed as trivial by reviewers or don't help in practice.

A. if `(∀ π, RTP(γ1, π))` and `(∀ π, RTP(γ2, π))`, then `(∀ π, RTP(γ1 ∘ γ2, π))`
	- "trivial" imo
	- This holds for any other characterization above, i.e., `TP`, `HP`, `CTP`, `RHP`, and `RCTP`
	- Coq'd
A'. if the first compiler is RTP and the second is SP, then the composition is SP
	- ?
B. if `RCTP(γ1, Ξ1)` and `RCTP(γ2, Ξ2)`, then `RCTP(γ1 ∘ γ2, Ξ1 ∩ Ξ2)`   (same spiel with `CTP`)
	- "trivial" by multiple reviews
	- somewhat valuable: If you only consider a subset of all safety properties for one and full safety for the other, composed compiler preserves that subset
	- Lifting a property `π` to a class `Ξ` works by using the powerset on π. 
		The equivalent hyperproperty then composes well under `RCTP`, but composition with `RHP(γ', Some Π)` is unclear (or `RTP` for that matter).
	- `RCTP` itself is not used in practice for anything more specific than "Safety"
	- Coq'd
C. `RTP` without `~` means the compiler is entirely uninteresting, as it never changes anything on the trace.
	The only thing such a compiler is allowed to do is forget/filter traces, but not manipulate the trace itself. Manipulation of the trace itself is very common in practice; see compcert undef behav or basic static typechecking to dynamic typechecking translation


# Things that do/may not work

- `RCTP(γ, Ξ)` does NOT imply RTP or RHP
- `RCTP/CTP` for hyperproperties.
    - One can naively use sets of hyperproperties as classes and similar composition result holds, but composition on that level is uninteresting. Considering all `Π ⊆ Ξ` is weird as hell, especially for non-subset-closed `Ξ`


# Things that may work/Other Suspicions

- `~` for just traces may not be enough for hyperproperties, and we need a 'set'-level relation
	- We have an example of why `~` does not suffice for HP-level reasoning


# Story

- we focus on secure compilation because correct compilation is a corollary of sec comp
- when composing compilers, we often take the Journey definitions and specialise them to a property of interest
- the property of interest is a singleton behaviour or a set-behaviour that is a subset of its class
	`RSSP` preserves `SS`, which is a set of behaviours that is a subset of all Safety
- we identify the conditions for composing compilers and what is the resulting composed property
	- we need the hypothesis: the second compiler respects the first property
	- this fact is trivial when the first and the second property coincide
	- this fact may be trivial when one of the two properties is a strict subset of the other
		if 1 preserves `RTP` and 2 preserves `SP`, the composition preserves `SP` (`RTP ∩ SP`)
	- this fact is not trivial when the two properties are not correlated, which happens in practice:
		`TMS` / `SMS` / (optimization passes are corr comp results) / `RCT` / `RSS`
		we need results about the trace relation: `well-formedness` result
			- if the properties are subsets of a certain class (e.g., safety) then the well-formedness proof may be easier
			- when we don't have a cross-language trace relation, then the results are trivial (and meaningless)
			- [CONJECTURE] well-formedness for hyperproperties requires a set-level relation

- can we integrate the discussion about classes?
	- not relevant ?



# Examples -- food for thought

IF
	`G1 : RTP ~1`
	`G2 : RSP ~2`
	`WF ~2, RTP ∩ RSP`
THEN
	`G1 * G2 : RTP ∩ RSP` ==
	`G1 * G2 : RSP`



