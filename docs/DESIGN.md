# Design decisions

This document records how the papers are turned into Isabelle/HOL, and why.
Each decision has an id (D1, D2, …) so that the plans and later discussions can
refer to it. The theories themselves do not mention these ids (D13). Each
decision has a status:

- **decided**: the theories follow it.
- **tentative**: the plan for now, to be confirmed when the theories are written.
- **open**: to be settled in a later phase.

Paper keys such as `[EPTCS69]` refer to [references.md](references.md).

## Guiding principles

1. **Stay close to the papers.** You should be able to put a paper next to the
   theory and recognise every definition.
   - When the paper's form and a more convenient Isabelle form differ, the
     paper's form is the definition and the convenient form is a proved lemma.
   - A deviation that cannot be avoided is stated explicitly in the decision
     that introduces it, and in the theory text.
2. **Grow the model the way the literature did.** Each paper extends the
   previous model. The formalisation does the same and proves that each
   extension is conservative.
3. **Check definitions on the paper's own examples** before building theorems
   on them.
4. **Proofs in the session are complete.** `sorry` and `oops` are allowed only
   in theories marked as work in progress, which the session does not build.

---

## Infrastructure

### D1. Toolchain and dependencies (decided)

- **Decision.** Isabelle2026, session `DCR` on top of `HOL`. No AFP
  dependencies for now. The session document is built with LuaLaTeX (the
  Isabelle2026 default), see D17.
- **Why.** A fixed Isabelle release is reproducible. Upgrades are deliberate:
  move to the next release, run `isabelle build -D .`, fix what breaks.
- **Automata.** The Büchi theorem of Phase 1c needs Büchi automata and
  infinite runs. The AFP has entries for transition systems and automata
  (e.g. *Transition Systems and Automata*, *Büchi Complementation*). Whether
  to depend on one of them, or to define the τ-automata of [EPTCS69] directly,
  is decided in Phase 1c (open question Q2). The DCR semantics has the shape
  of a labelled transition relation (`step G M (e, a) M'`), so connecting to an
  AFP entry later is a short wrapper.

### D2. Faithfulness and errata (decided)

- **Decision.** Definitions follow the paper's formulas as literally as Isabelle
  allows. The text before each definition cites the paper and the number of
  the definition it formalises (`\<^cite>\<open>\<open>Def. 3\<close> in EPTCS69\<close>`).
  Where the paper is ambiguous, we take the reading under which the paper's
  own claims hold, and say so in the text. Where a claim is false as stated,
  the theory:
  - proves a corrected statement;
  - gives a counterexample to the literal statement when this is cheap;
  - is listed in the "issues" section of the phase plan, so it can be
    reported back.
- **Why.** The formalisation then also checks the papers, and every result
  stays clearly tied to its source. Reading the original paper has already
  turned up several such issues; see
  [phase-1-plan.md](phase-1-plan.md), §5 and the appendix.

### D3. One model per paper, linked by conservative-extension theorems (decided)

- **Decision.** Each model is a separate Isabelle record with its own
  semantics, defined as in its paper:
  - DCR graphs as in [EPTCS69];
  - DCR graphs with milestones;
  - DCR graphs with guards, data, time;
  - and so on.

  Each extension comes with a map from the previous model and a theorem that
  the map preserves transitions, runs and acceptance: a plain graph is an
  extended graph with trivial extra structure (e.g. all guards `true`), and the
  two semantics agree on it.
- **No record schemes.** Definitions take `('event, 'action) dcr_graph`, not the
  extensible `('event, 'action, 'more) dcr_graph_scheme`. A record extension can
  only add fields; it can never change the type or meaning of existing ones.
  Most later features change the relations themselves (a guarded include is no
  longer a set of pairs) and the update of the marking, so they could not be
  record extensions anyway. Distributed graphs (Def. 5) are the one case where
  fields are added without changing the semantics; there a record extension or
  a record with the graph as a field is chosen when Def. 5 is formalised.
- **Why.** Each paper's definitions stay recognisable, and a result proved for
  one model cannot silently change meaning. The chain of embedding theorems
  becomes a formal record of how the logic evolved.
- **Alternative considered.** One general record in which later features are
  optional (empty milestone relation, no time, no data). Rejected because it
  hides which result belongs to which paper. Also, later features change the
  *state space* (time adds clocks, data adds stores, spawning changes the set
  of events), so a single record could not hold them all anyway.
- **Cost.** Some duplication. Generic infrastructure (D12) keeps it small.

## Representation

### D4. Events are a type (decided for Phase 1; revisit in Phase 3)

- **Decision.** A DCR graph is parameterised by a type variable `'event`, and
  every element of `'event` is an event. "All events" is `UNIV`. A finite
  graph is one whose event type is finite (`finite (UNIV :: 'event set)`, or
  the type class `finite`). The paper's examples become small datatypes, e.g.
  `datatype event = Prescribe | Sign | Give | DontTrust`.
- **Why.** This is the simplest way to say "`'event` is the set of events" in
  HOL. It needs no side conditions such as "this relation only relates events
  of the graph", and examples read like the paper.
- **Alternative considered.** Events come from one fixed type, and each graph
  carries its own event set, as in the Isabelle formalisation [AFP23]
  (`type_synonym event = nat` and a field `dom :: event set`). This is better
  for operations that split or combine graphs, where one event belongs to
  several graphs:
  - projection and composition (Phase 3);
  - choreographies (Phase 4);
  - spawning (Phase 6).

  The cost is well-formedness conditions everywhere. To be decided in Phase 3
  (Q1).

### D5. Relations are sets of pairs (decided)

- **Decision.** Each relation is a set of pairs, `'event rel`, which HOL defines
  as `('event × 'event) set`, exactly as in Def. 3 (`→• ⊆ E × E`).
  `e →•⇘G⇙ e'` (D14) stands for `(e, e') ∈ condition G` and keeps the paper's
  direction: "`e` is a condition for `e'`".
- **Why.** This follows principle 1. HOL's relation library works on exactly
  this type, so transitive closure (`r⁺`), well-foundedness (`wf`), images and
  compositions apply directly, e.g. for acyclicity in Phase 2. Concrete
  relations are written as set literals, e.g.
  `{(Prescribe, Sign), (Sign, Give)}`. [AFP23] uses the same representation.

### D6. Include and exclude are two separate relations (decided)

- **Decision.** There are two fields, `inclusion` and `exclusion`.
  `e →+⇘G⇙ e'` means `(e, e') ∈ inclusion G` ("`e` includes `e'`"), and
  `e →%⇘G⇙ e'` means `(e, e') ∈ exclusion G` ("`e` excludes `e'`"). They are two
  independent relations, just like condition and response.
- **Names.** `include` and `includes` are Isabelle keywords, so they cannot be
  field names. The field names are the paper's words, the "dynamic
  inclusion/exclusion relations".
- **Why.** These are the include and exclude relations of the original paper,
  and all later papers use the same form. Keeping them separate from the
  start avoids changing the representation in Phase 2.
- **About `±` in [EPTCS69] Def. 3.** The paper writes the two relations as one
  partial map `± : E × E ⇀ {+, %}`. This is only notation for the pair. It is
  unrelated to the *logical include* of the tools, which is also drawn with
  `±`. The logical include is a guarded include/exclude pair that was added
  later and comes with data (Phase 5).
- **The restriction we drop.** Because `±` is a partial map, no event can both
  include and exclude the same event. We do not keep this restriction; it is
  the property `inclusion_exclusion_disjoint`. The update of Def. 4 (v),
  `(In ∪ e→+) \ e→%`, already says what happens when both relations hold: the
  exclusion wins. Graphs that satisfy the restriction behave exactly as
  before.
- **Alternative considered.** Keep the restriction as an invariant of the type
  (a `typedef`). This matches the paper's class of graphs exactly, but every
  concrete graph would then need a proof of the invariant.
- **Later papers.** [JLAP13], [FORTE19] and [AFP23] update the included events
  with `(In \ e→%) ∪ e→+`, so there the inclusion wins. The two updates agree
  whenever `inclusion_exclusion_disjoint` holds. Phase 2 compares them as part
  of the conservative-extension theorem. With guards, the restriction itself
  changes meaning (a conflict needs both guards to hold at once), which is one
  reason for D3.

### D7. Labels are a type parameter (decided)

- **Decision.** `label :: 'event ⇒ 'action`, where `'action` is an arbitrary type.
  The examples use `string`.
- **Why.** Several events may carry the same action, and the semantics talks
  about actions: transitions are labelled `(e, a)`, and Def. 5 assigns roles to
  actions. A type parameter also covers the later variants:
  - sets of labels [JLAP13] (`'action := 'a set`);
  - interactions [FORTE19].

  Roles and principals (distributed DCR graphs) come on top of a graph, as in
  the paper (D3).

### D8. Markings are triples of sets (decided)

- **Decision.** `record 'event marking` with the fields `Ex`, `Re` and `In`, the
  paper's names: executed events, pending responses, included events. [AFP23]
  uses the same record.
- **Why `set` rather than finite sets.** The paper does not require the set of
  events to be finite, and set algebra is the easiest to reason about.
  Finiteness is an assumption only where it is needed (finite state space,
  Büchi automata). Computation on examples is handled separately (D11).

## Semantics

### D9. The transition relation exactly as in Def. 4 (decided)

- **Decision.** The transition relation `M' →(e,a) M''` of `T(G)` is *defined*
  as in [EPTCS69] Def. 4: the conjunction of items (ii)–(vi), as
  `step G M' (e, a) M''`, written `G ⊢ M' →⇘(e, a)⇙ M''` (D14). Transitions
  are labelled with pairs `(e, a)`. `step` is a `fun` with the single equation
  `G ⊢ M' →⇘(e, a)⇙ M'' ⟷ …`, so the pair pattern appears on the left as in the
  paper. Two derived notions follow the paper's own wording:
  - `enabled G M e`: items (iii)–(iv), "`e` is included and all its included
    conditions have been executed";
  - `execute G M e`: the marking `M''` given by items (ii), (v) and (vi).

  A lemma `step_iff` states that `step G M' (e, a) M''` holds iff `e` is
  enabled, `a = label G e` and `M'' = execute G M' e`.
- **Include and exclude at once.** Item (v) computes `(In ∪ e→+) \ e→%`, so an
  event both included and excluded by `e` ends up excluded. [AFP23] and later
  papers compute `(In \ e→%) ∪ e→+`. The two agree under
  `inclusion_exclusion_disjoint`; the theory text says so.
- **Why.** This follows principle 1: the definition is the paper's. Most proofs
  use the derived form, because the marking after a step is determined by
  the event.
- **History.** The first plan made `enabled ∧ M'' = execute M' e` the
  definition and the paper's items a lemma. This was reversed under
  principle 1 before any theory was written. ([AFP23] defines `enabled` and
  `execute` directly, without a transition relation.)

### D10. Runs exactly as in Def. 4 (decided)

- **Decision.** A run is defined as in the paper: the sequence of labels
  `(eᵢ, aᵢ)` of a sequence of transitions `Mᵢ →(eᵢ,aᵢ) Mᵢ₊₁` that starts in the
  graph's marking. Finite runs are lists; infinite runs are sequences indexed
  by `nat` (functions `nat ⇒ …`). Acceptance refers to the markings `Mᵢ` of
  these transitions, exactly as in Def. 4.
- **Derived forms (lemmas).**
  - Because each step is determined by its event, a run is determined by its
    events `eᵢ`. Most proofs and computations use this shorter form.
  - A finite run is accepting iff its last marking has no included pending
    response. This is [AFP23]'s definition of acceptance.
- **Why lists and sequences.** The paper says "a (finite or infinite)
  sequence". Most theorems split naturally into a finite and an infinite part
  anyway; the Büchi theorem is an example.
- **History.** The first plan defined runs as lists of events, with the
  markings computed by `execute`, i.e. the derived form. This was reversed
  under principle 1 before any theory was written.
- **Alternatives considered.** A single type of possibly-infinite sequences
  (lazy lists from the AFP entry *Coinductive*, or `stream` from HOL-Library
  for the infinite case). Uniform, but harder to work with. If an AFP automata
  entry is adopted (Q2), its notion of infinite words is used for the Büchi
  part.

### D11. Check definitions on the paper's examples (decided)

- **Decision.** Every phase encodes the paper's examples as concrete Isabelle
  values and proves the claims the paper makes about them. For instance, the
  transition system of the prescribe-medicine graph (Fig. 4 of [EPTCS69]) has
  exactly 8 reachable markings, 2 of which are accepting.
  - Small facts are proved by `simp` or `auto` with the graph's definition, as
    in the example theories now.
  - Statements like "the reachable markings are exactly these 8" are proved
    without a verified search algorithm. One shows that the 8 markings are
    closed under steps, and that each of them is reached by an explicit run.
  - Where evaluation is easier, Isabelle's code generator (`value`, `by eval`)
    computes on enumerated event types (class `enum`, with instances for
    small event types written by hand).
- **Why.** A wrong definition is cheap to fix before theorems depend on it and
  expensive afterwards. The paper's figures are a ready-made test suite.

### D12. A generic layer for runs and acceptance (tentative, for Phase 2)

- **Decision.** Acceptance depends only on two things:
  - the transitions;
  - for each state, the set of events that are pending and included
    (`Re ∩ In`).

  [FORTE19] (Def. 10) calls this a *labelled event transition system with
  responses* and proves that isomorphic ones have the same language
  (Prop. 12). We will introduce this structure, probably as a locale, once a
  second model needs it (Phase 2), define runs, acceptance and languages on it
  once, and prove that the [EPTCS69] definitions are an instance of it.
- **Why.** It avoids restating acceptance for every model, and makes results
  such as "isomorphic ⇒ same language" available for all models at once.
- **Why not in Phase 1.** In Phase 1 there is only one model, and the paper's
  own form of acceptance is easier to compare with the text.

## Theory organisation

### D13. Layout, naming and theory text (decided)

- **Layout.** One topic per theory. Each theory starts with a `section` and
  text that cites the paper (D2). Directories:

```text
Core/       Phase 1a–b: Marking, DCR_Graph, Semantics, Run, Acceptance, Distributed
Buchi/      Phase 1c: Büchi automata with τ, the construction, the theorem
Examples/   paper examples (Figs. 3–7 of [EPTCS69], …)
(later)     Milestone/  Nested/  Projection/  Choreography/  Data/  Timed/  …
docs/       plans, design decisions, references
document/   LaTeX of the session document (D17)
```

- **Naming.** Isabelle conventions: `snake_case` for constants and theorems,
  `Upper_Snake` for theory names, `CamelCase` constructors in examples. The
  [EPTCS69] model is the record `dcr_graph` with markings `marking`. Names of
  later models are chosen when they arrive.
- **Type variables are words:** `'event`, `'action` (not `'e`, `'a`).
- **Theory text stays lean.** No references to these design decisions
  (D-numbers) in the theories; they live in `docs/`. No lemmas whose only
  purpose is a trivial faithfulness check (e.g. "records are exactly
  triples").

### D14. Notation close to the papers (decided)

- **Decision.** Statements use the papers' arrows, with the graph as a
  subscript:

  | Notation | Meaning | Stands for |
  |---|---|---|
  | `e →•⇘G⇙ e'` | `e` is a condition for `e'` | `(e, e') ∈ condition G` |
  | `e •→⇘G⇙ e'` | `e'` is a response to `e` | `(e, e') ∈ response G` |
  | `e →+⇘G⇙ e'` | `e` includes `e'` | `(e, e') ∈ inclusion G` |
  | `e →%⇘G⇙ e'` | `e` excludes `e'` | `(e, e') ∈ exclusion G` |

  `⇘G⇙` means that `G` is written as a subscript. The transition relation of
  Def. 4 is written `G ⊢ M' →⇘(e, a)⇙ M''`: the graph comes first, because
  `T(G)` depends on it, and the label is a subscript of the arrow as in the
  paper's `M' →(e,a) M''`. This is mixfix syntax on the `fun` itself, not an
  abbreviation.
- **Abbreviations, so Isabelle also prints them.** The arrows are
  `abbreviation`s with mixfix syntax. Isabelle folds abbreviations back when
  printing, so goals and output show `e →•⇘G⇙ e'` rather than
  `(e, e') ∈ condition G`, without a custom printer.
- **In the source,** the arrows are the symbols `\<rightarrow>` and `\<bullet>`, and the
  subscript is `\<^bsub>G\<^esub>`. Isabelle/jEdit and Isabelle VSCode display them
  as `→•⇘G⇙`; a plain text editor shows the raw codes.
- **In the PDF,** the arrows are typeset with the inline symbols of the
  dcrgraph package (D17).

### D15. Proof hygiene (decided)

- No `sorry` or `oops` in the theories the session builds. Work in progress
  goes into theories that are not listed in `ROOT`.
- The session must build cleanly with `isabelle build -D .`, document included.
- Licence: BSD-3-Clause for the theories, as in the AFP (see `LICENSE`); the
  bundled `document/dcrgraph.sty` keeps its own LPPL licence.
- Main automation: `simp`, `auto`, `blast`, Sledgehammer in the IDE, and `eval`
  for concrete examples (D11).

### D16. How each phase proceeds (decided)

Each phase goes through these steps:

1. **Plan.** A document maps every definition and result of the paper to
   planned Isabelle names and lists the open decisions. You review it.
2. **Definitions and examples.** The paper's examples are checked (D11).
3. **Statements.** Theorems are stated, with `sorry`, in a work-in-progress
   theory outside the session.
4. **Proofs.**
5. **Wrap-up.** Update the plan and give an overview of what was done and
   which decisions were made.

### D17. The session document (decided)

- **Decision.** The session builds a PDF (`document = pdf`, output in
  `output/document.pdf`) with LuaLaTeX:
  - **Figures** of the papers' graphs are drawn with the dcrgraph package
    (https://github.com/tilzuck/DCR-Latex), in its classic notation, as
    `\<^latex>\<open>\begin{dcrgraph} … \end{dcrgraph}\<close>` blocks in the example
    theories.
  - **The relation arrows** in all theory text are typeset with dcrgraph's
    inline symbols (`\dcrcondition` etc.). `document/isa_dcr_arrows.lua` maps
    Isabelle's output of each arrow to these symbols while LuaLaTeX reads the
    generated files, so the theory sources keep plain Isabelle syntax.
  - **References** are cited with `\<^cite>` and resolved by BibTeX from
    `document/root.bib`; the keys are those of [references.md](references.md).
    The batch build checks every cited key.
- **Why.** The PDF should read like a paper and use the same notation as the
  DCR papers and tools; figures sit next to the definitions they illustrate.

---

## Open questions

| Id | Question | When |
|---|---|---|
| Q1 | How to represent graphs whose event sets differ (projection, composition, spawning): subtypes, or graphs with an explicit event set as in [AFP23] (D4)? | Phase 3 |
| Q2 | Use an AFP entry for transition systems, infinite words and Büchi automata, or define the τ-automata of [EPTCS69] directly (D1)? | Phase 1c |
| Q3 | Data: guards as HOL predicates over a store (shallow embedding), or a syntax tree of the expression language used by DCR Solutions / DCR-js (deep embedding)? A deep embedding allows importing real models; a shallow one is easier to reason about | Phase 5 |
| Q4 | Time domain: discrete `nat` as in [JLAP13], or also dense time? | timed graphs |
| Q5 | Asynchrony in DACEO: how to represent channels (queues or multisets), and how to represent ordering constraints that depend on data | Phase 7 |
