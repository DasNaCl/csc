# Plan: Updating Theorem 4 (Robust TMS Preservation) to Use σ-based Composition

## 1. Summary of the Problem

### Current State in `old_tech/`

The framework **already has** the σ/τ infrastructure in `compositionality.tex`:
- `σ_∼(π)` (Definition 3): Universal image - pulls back target property to source
- `τ_∼(π)` (Definition 4): Existential image - pushes forward source property to target
- `\rtpsigma`, `\rtptau`, `\rtp` - three variants of robust preservation

The cross-language trace relation `∼` is defined in `tms-compiler.tex` (lines 190-270) via `\xlangtraceeq` and `\xlangeventeq`.

### The Problem

**Theorem 4** (Robust TMS Preservation, `tms-compiler.tex` line 2192) currently uses the simplified notation that doesn't explicitly use σ.

### What We Want

State and prove the theorem using σ directly on the **property** `tmssafe` (no lifting to classes).

---

## 2. Files to Modify

| File | Lines | Description |
|------|-------|-------------|
| `old_tech/tms-compiler.tex` | 2177-2254 | Theorem 4 statement and proof |

---

## 3. New Theorem Statement

### 3.1. Current Statement (lines 2185-2189)

```latex
\begin{goals}
  \item $\vdash\mmlAmmlAtcomp{\bullet}:\operatorname{tmssafe}$
\end{goals}
```

### 3.2. New Statement (σ-based, no lifting)

```latex
\begin{goals}
  \item $\forall\src{p}\in\src{\partials},\
        \rsat{\src{p}}{\sigma_{\sim}(\operatorname{tmssafe})}
        \implies \rsat{\mmlAmmlAtcomp{p}}{\operatorname{tmssafe}}$
\end{goals}
```

Or using the existing notation from `compositionality.tex`:

```latex
\begin{goals}
  \item $\rtpsigma[\sim]{\mmlAmmlAtcomp{\bullet}}{\operatorname{tmssafe}}$
\end{goals} use this
```

Where `\rtpsigma[\sim]{C}{π}` is defined for a **single property** π (not a class).

**Note:** If `\rtpsigma` currently requires a class, we may need to either: it dosen't
1. Add a property-level variant, or
2. Just write out the definition explicitly as above

---

## 4. The Proof (Rigorous Plain-Words Version)

### 4.1. Setup

**Given:**
- Source partial program `p_S` (the component library `library_comp`)
- Compiler `C : L_tms → L_trg`
- Cross-language trace relation `∼` (defined by `\xlangtraceeq`)

**Assume:**
- `rsat(p_S, σ_∼(tmssafe))`

**Show:**
- `rsat(C(p_S), tmssafe)`

### 4.2. Unfolding Definitions

**What σ_∼(tmssafe) means:**
```
σ_∼(tmssafe) = { t_S | ∀t_T. t_S ∼ t_T → t_T ∈ tmssafe }
```
A source trace is in σ(tmssafe) iff ALL related target traces satisfy tmssafe.

**What the assumption gives us:**
For all source contexts `C_S` and source traces `t_S` from executing `link(C_S, p_S)`:
- For all target traces `t_T` such that `t_S ∼ t_T`, we have `t_T ∈ tmssafe`

**What we need to show:**
For all target contexts `C_T` and target traces `t_T` from executing `link(C_T, C(p_S))`:
- `t_T ∈ tmssafe`

### 4.3. Proof Steps

**Step 1: Assume an arbitrary target execution.**

Take any:
- Target context `C_T` (i.e., `library_ctx_T`)
- Target trace `t_T` from executing `link(C_T, C(p_S))`

We must show `t_T ∈ tmssafe`.

**Step 2: Apply backtranslation.**

By the backtranslation theorem (existing in tms-compiler.tex, lines 2221-2226), given `t_T`, we construct:
- A source context `C_S` (i.e., `library_ctx_S`)
- A location mapping `δ`
- A source trace `t_S` from executing `link(C_S, p_S)`

Such that:
- `t_S ∼ t_T` (the cross-language trace relation holds)

**Step 3: Apply the σ assumption.**

By our main assumption `rsat(p_S, σ_∼(tmssafe))`:
- Since `t_S` comes from executing `link(C_S, p_S)`, we have `t_S ∈ σ_∼(tmssafe)`

Unfolding σ:
- For all `t_T'`, if `t_S ∼ t_T'`, then `t_T' ∈ tmssafe`

**Step 4: Instantiate with our target trace.**

We have `t_S ∼ t_T` from Step 2.

Instantiating the universal from Step 3 with `t_T' := t_T`:
- Since `t_S ∼ t_T` holds, we conclude `t_T ∈ tmssafe`

**Step 5: Handle the memory-safety filter (technical detail).**

The `tmssafe` property is checked on filtered traces. Lemma `lem:msfiltereq` establishes that if:
- Location mappings are consistent: `δ(src_loc) = trg_loc → δ_MS(src_loc) = δ_MS'(trg_loc)`
- Traces are related: `t_S ∼ t_T`

Then filtered traces agree: `filter_MS(t_S, δ_MS) = filter_MS(t_T, δ_MS')`.

The proof constructs `δ_MS'` as `trg_loc ↦ δ_MS(δ^{-1}(trg_loc))`, requiring δ to be injective (established by backtranslation).

**QED.**

### 4.4. Summary Table

| Step | Action | Key Lemma/Definition |
|------|--------|---------------------|
| 1 | Assume target execution | Unfold rsat for goal |
| 2 | Backtranslate to source | Backtranslation correctness (lines 1426-1591) |
| 3 | Source trace ∈ σ(tmssafe) | Main assumption |
| 4 | Since t_S ∼ t_T, conclude t_T ∈ tmssafe | Definition of σ |
| 5 | Filters agree | lem:msfiltereq (line 1307) |

---

## 5. Alignment with Coq Mechanisation

The Coq definition in `/home/dasnacl/coq/Langs/Compiler.v` (lines 155-159):

```coq
Definition Compiler_RobustPreserves_TRG (γ : Compiler S T)
           (xrel : STRel TR_S TR_T) (π : @property TR_T) : Prop :=
  forall (p : Partial),
    rsat p (sigma xrel π) ->
    rsat (γ p) π.
```

This matches exactly:
- `γ` is the compiler `C`
- `π` is `tmssafe` (a property, not a class)
- The statement is `rsat(p, σ_xrel(π)) → rsat(γ(p), π)`


---

## 6. Cross-Language Trace Relation

The relation `∼` is defined in `tms-compiler.tex` lines 190-270 via:
- `\xlangtraceeq{t_S}{t_T}` - trace-level relation
- `\xlangeventeq{e_S}{e_T}` - event-level relation

Key rules:
- `empty-trace-eq`: `ε ∼ ε`
- `cons-trace-eq`: If `e_S ∉ X` (ignored events), sandbox tags match, events relate, and tails relate, then traces relate
- `ignore-cons-trace-eq`: Events in X are ignored in the source

---

## 7. Well-Formedness Condition

The composition lemma `lem:seqcompo:sigma` requires `\wfcsig{\sim}{\cC}`.

**Definition (line 70-77 of compositionality.tex):**
```latex
\wfcsig{\sim}{\trg{\cC}} := \forall \trg{\pi}\in\trg{\cC}, \sigma_{\sim}(\trg{\pi})\in\sigma_{\sim}(\trg{\cC})
```

**For a single property (not a class):** This condition is trivially satisfied or not needed. The well-formedness is for composing multiple compilers with class-level preservation. For a single property `tmssafe`, we don't need this condition.

If we later compose this theorem with another (e.g., SMS preservation), then we'd use `lem:seqcompo:sigma` with the well-formedness condition.

---

## 8. Changes to Make in tms-compiler.tex

### 8.1. Update the theorem statement (lines 2185-2189)

**From:**
```latex
\begin{goals}
  \item $\vdash\mmlAmmlAtcomp{\bullet}:\operatorname{tmssafe}$
\end{goals}
```

**To:**
```latex
\begin{goals}
  \item $\forall\src{\library_{\comp}}\in\src{\partials},\
        \rsat{\src{\library_{\comp}}}{\sigma_{\sim}(\operatorname{tmssafe})}
        \implies \rsat{\mmlAmmlAtcomp{\library_{\comp}}}{\operatorname{tmssafe}}$
\end{goals}
```

### 8.2. Update the proof (lines 2193-2254)

The existing proof structure is largely correct but needs to:

1. **Make σ explicit in the assumption:** Instead of assuming `\rsat{\src{\library_{\comp}}}{\operatorname{tmssafe}}`, assume `\rsat{\src{\library_{\comp}}}{\sigma_{\sim}(\operatorname{tmssafe})}`

2. **Add the σ instantiation step:** After backtranslation establishes `t_S ∼ t_T`, explicitly use the σ definition to conclude `t_T ∈ tmssafe`

3. **Reference the cross-language relation:** Point to the definition of `\xlangtraceeq` (lines 190-270)

The core backtranslation argument and filter equality lemma stay the same.

---

## Appendix: References to Coq Mechanisation

| Coq Name | File:Line | Corresponding TeX |
|----------|-----------|-------------------|
| `sigma` | XLang.v:39-42 | `\sigma_{\sim}` (Def 3, compositionality.tex) |
| `Compiler_RobustPreserves_TRG` | Compiler.v:155-159 | The theorem statement |
| `Compiler_RobustPreserves_XEq` | Compiler.v:139-147 | Backtranslation theorem |
| `sigma_comp_functorial` | CompComp.v:201-207 | (for future composition) |
