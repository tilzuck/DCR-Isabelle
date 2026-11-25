# Phase 1 plan: the original paper [EPTCS69]

**Paper.** T. T. Hildebrandt, R. R. Mukkamala, *Declarative Event-Based Workflow
as Distributed Dynamic Condition Response Graphs*, PLACES 2010, EPTCS 69,
pp. 59–73, 2011. doi:10.4204/EPTCS.69.5, arXiv:1110.4161. This plan was made
from the arXiv LaTeX source. Definition numbers follow the arXiv version.

**Scope.** Phase 1 covers DCR graphs (§3: Defs. 3–5) and the mapping to Büchi
automata (§4). The event-structure part (§2 and Props. 1–3) is left out by
decision, because later work does not build on it. Problems found while
reading it are kept in the appendix.

**Status.** Milestone 1a is in progress.
- Def. 3 is formalised in `Core/Marking.thy` and `Core/DCR_Graph.thy`.
- The graphs of Fig. 3 are in `Examples/Prescribe_Medicine.thy` and
  `Examples/Prescribe_Medicine_With_Check.thy`.
- Next: Def. 4.

The design decisions referred to as D1–D17 are in [DESIGN.md](DESIGN.md).

---

## 1. What the paper contains

| § | Content | Formal items | In Phase 1 |
|---|---|---|---|
| 2 | Prime event structures and condition response event structures (CRES) | Def. 1, Def. 2, Props. 1–2 | no |
| 3 | DCR graphs: marking, transition system, runs, acceptance; CRES as DCR graphs; distributed DCR graphs (roles, principals) | Def. 3, Def. 4, Prop. 3, Def. 5 | yes, except Prop. 3 |
| 4 | Mapping of finite DCR graphs to Büchi automata with a τ-event | Büchi automaton with τ, the construction `B(G)`, Theorem (same runs and accepting runs) | yes |

Examples: Fig. 3(a) prescribe medicine; Fig. 3(b) with "don't trust";
Fig. 4 the transition system of Fig. 3(a); Fig. 5 two runs of Fig. 3(b) with
their markings; Figs. 6–7 the Büchi automaton of Fig. 3(a).

Not formalised: §2 and Prop. 3, the graphical notation, and the SPIN
prototype and future work mentioned in the conclusion.

## 2. Definition 3, item by item

Def. 3 defines a DCR graph as the tuple `G = (E, M, Act, →•, •→, ±, l)`.
The Isabelle record `('event, 'action) dcr_graph` (in `Core/DCR_Graph.thy`) has exactly
these components:

| Def. 3 | Meaning | Isabelle |
|---|---|---|
| (i) `E` | the set of events | type variable `'event` (D4) |
| (ii) `M ∈ P(E) × P(E) × P(E)` | the marking `(Ex, Re, In)` | field `marking :: 'event marking`, a record with the fields `Ex`, `Re`, `In` (D8) |
| (iii) `Act` | the set of actions | type variable `'action` (D7) |
| (iv) `→• ⊆ E × E` | condition relation | field `condition :: 'event rel`, a set of pairs. `e' →•⇘G⇙ e` means `(e', e) ∈ condition G` (D5, D14) |
| (v) `•→ ⊆ E × E` | response relation | field `response :: 'event rel`, written `e •→⇘G⇙ e'` |
| (vi) `± : E × E ⇀ {+, %}` | dynamic inclusion/exclusion | two fields `inclusion`, `exclusion :: 'event rel`, written `e →+⇘G⇙ e'` and `e →%⇘G⇙ e'` (D6) |
| (vii) `l : E → Act` | labelling | field `label :: 'event ⇒ 'action` |

`⇘G⇙` means that `G` is written as a subscript.

**One change of form.** Item (vi) becomes two separate relations, as in all
later papers (D6). The partial map `±` also ruled out that an event both
includes and excludes the same event. We drop that restriction; for that case,
the update of Def. 4 (v) decides that the exclusion wins.

**Not in Def. 3.** There is no milestone relation yet. It arrives in Phase 2,
together with the later update `(In \ e→%) ∪ e→+`.

Further names:

| Paper | Isabelle (planned) |
|---|---|
| `M' →(e,a) M''` | `step G M' (e, a) M''`, defined item by item as in Def. 4 (D9) |
| run, accepting run | as in Def. 4: the labels `(eᵢ, aᵢ)` of a sequence of transitions (D10); names to be fixed in the Def. 4 step |

## 3. Sketch of the semantics (Def. 4)

Def. 3 is real code now (see §2). The sketch below covers the next step, Def. 4.
It is **not checked by Isabelle** yet and may change. Following principle 1 in
DESIGN.md, the transition relation is *defined* by the paper's items (i)–(vi).
The handier forms `enabled` and `execute` are derived from it, and a lemma
connects them.

```isabelle
text ‹The transition relation of T(G) [EPTCS69, Def. 4]: M' →(e,a) M''.
  (i): M' = (Ex', Re', In') is the marking before the transition.›
definition step ::
    "('event, 'action) dcr_graph ⇒ 'event marking ⇒ 'event × 'action ⇒ 'event marking ⇒ bool"
  where "step G M' ea M'' ⟷ (case ea of (e, a) ⇒
      Ex M'' = Ex M' ∪ {e}                                          ― ‹(ii)›
    ∧ e ∈ In M' ∧ label G e = a                                     ― ‹(iii)›
    ∧ {e'. e' ∈ In M' ∧ e' →•⇘G⇙ e} ⊆ Ex M'                          ― ‹(iv)›
    ∧ In M'' = (In M' ∪ {e'. e →+⇘G⇙ e'}) - {e'. e →%⇘G⇙ e'}          ― ‹(v)›
    ∧ Re M'' = (Re M' - {e}) ∪ {e'. e •→⇘G⇙ e'})"                     ― ‹(vi)›

text ‹e is enabled in M: items (iii)–(iv).›
definition enabled ::
    "('event, 'action) dcr_graph ⇒ 'event marking ⇒ 'event ⇒ bool"
  where "enabled G M e ⟷ e ∈ In M ∧ {e'. e' ∈ In M ∧ e' →•⇘G⇙ e} ⊆ Ex M"

text ‹The marking after executing e: items (ii), (v), (vi).›
definition execute ::
    "('event, 'action) dcr_graph ⇒ 'event marking ⇒ 'event ⇒ 'event marking"
  where "execute G M e =
    ⦇Ex = Ex M ∪ {e},
     Re = (Re M - {e}) ∪ {e'. e •→⇘G⇙ e'},
     In = (In M ∪ {e'. e →+⇘G⇙ e'}) - {e'. e →%⇘G⇙ e'}⦈"

text ‹The derived form: a transition is an enabled event and its effect.›
lemma step_iff:
  "step G M' (e, a) M'' ⟷ enabled G M' e ∧ a = label G e ∧ M'' = execute G M' e"
```

A paper-style notation for `step` (e.g. `G ⊢ M' →⇘(e,a)⇙ M''`) can be added
in the same step, as for the relations (D14).

Runs (D10), as in Def. 4:
- A finite run is a list of labels `(eᵢ, aᵢ)` together with markings
  `M₀ … Mₙ`, such that `M₀` is the graph's marking and
  `Mᵢ →(eᵢ,aᵢ) Mᵢ₊₁` for every `i`.
- An infinite run is the same with sequences indexed by `nat`.
- Acceptance, exactly as in Def. 4, uses the markings of the run:
  `∀ i, ∀ e ∈ Reᵢ, ∃ j ≥ i, e = eⱼ ∨ e ∉ Inⱼ`.
- Derived form (a lemma): a run is determined by its events, and its
  markings are obtained with `execute`.

## 4. Paper → Isabelle map

### §3 DCR graphs (milestones 1a and 1b)

| Paper item | Planned Isabelle | File |
|---|---|---|
| Def. 3: marking, `M(G) = P(E)³` | record `'event marking` (done) | `Core/Marking.thy` |
| Def. 3: DCR graph | record `('event, 'action) dcr_graph`, item by item as in §2 (done) | `Core/DCR_Graph.thy` |
| Def. 4: transition system `T(G)`, items (i)–(vi) | `step`, defined item by item (D9) | `Core/Semantics.thy` |
| Def. 4: items (iii)–(iv), "`e` is enabled" | `enabled` (derived) | same |
| Def. 4: items (ii), (v), (vi), the new marking | `execute` (derived); `step_iff` connects both to `step` | same |
| basic properties, used throughout | transitions are deterministic; executed events stay executed; an event stops being pending only by being executed | same |
| "finite state if the graph is finite" | finitely many markings when the type `'event` is finite | same |
| Def. 4: runs | finite runs (lists) and infinite runs (sequences indexed by `nat`): the labels `(eᵢ, aᵢ)` of a sequence of transitions (D10) | `Core/Run.thy` |
| Def. 4: accepting runs | acceptance for finite runs (literal; see §5, point 1) and for infinite runs | `Core/Acceptance.thy` |
| remark after Def. 4: for finite runs, accepting = no included pending response at the end | a lemma | same |
| Def. 5: distributed DCR graph `(G, Roles, P, as)` | a record with the underlying graph as a field, `graph :: ('event, 'action) dcr_graph`, plus roles, principals and the role assignment, split into a principal–role and an action–role relation (§5, point 2). Alternatively a record extension of `dcr_graph`; decided when Def. 5 is formalised (see §8) | `Core/Distributed.thy` |
| Def. 5: transitions `(e, (p, a, r))`, runs, acceptance | the distributed transition relation; acceptance taken from the underlying graph | same |

### §4 Büchi automata (milestone 1c)

| Paper item | Planned Isabelle | File |
|---|---|---|
| Büchi automaton with τ-event; runs (τ removed) and acceptance | our own definition, or the automata of an AFP entry (Q2 in DESIGN.md) | `Buchi/Buchi_Tau.thy` |
| the construction `B(G)`, `rank`, `min` | the paper's "fixed order" is an enumeration of the finite type of events | `Buchi/Construction.thy` |
| Theorem: `B(D)` has the same runs and accepting runs as `D` | split into finite and infinite runs | `Buchi/Correctness.thy` |

The paper defines `B(D)` for distributed graphs. We first prove the theorem
for plain graphs, with transitions labelled `(e, l(e))`, and then extend it to
distributed graphs. This works because the role conditions on a distributed
transition (`p as r` and `a as r`) do not depend on the marking.

The paper only states the theorem; it gives no proof. The proof must show that
the rank and the flag `j` together guarantee fairness: no included pending
response is ignored forever. It is the main theorem of Phase 1.

## 5. Points to settle while formalising §3–4

**1. Index ranges for finite runs in acceptance (Def. 4).**
- *The paper:* `∀i, e ∈ Reᵢ. ∃j ≥ i. (e = eⱼ ∨ e ∉ Inⱼ)` is written for
  infinite runs. A run of length `n` has markings `M₀…Mₙ` but events only
  `e₀…eₙ₋₁`.
- *Our reading:* `i` and `j` range over `0…n`, and `e = eⱼ` requires `j < n`.
  Under this reading the paper's remark holds: a finite run is accepting iff
  `Reₙ ∩ Inₙ = ∅`. The reason is that an event stays pending until it is
  executed.

**2. Role assignment, a modelling note (Def. 5).**
- The abstract speaks of "assigning roles to events". Def. 5 actually
  assigns roles to *actions* and principals (`as ⊆ (P ∪ Act) × Roles`). We
  follow Def. 5.
- In HOL, `P` and `Act` are different types, so `as` is split into two
  relations. This is equivalent.

**3. Typo.** Def. 4 writes `→ ⊆ M(G) × (E × Act) × (G)`; it should end in
`M(G)`.

## 6. Checking the definitions on the paper's examples (D11)

- **Fig. 3(a), prescribe medicine.**
  - Relations: `pm →• s`, `pm •→ s`, `pm •→ gm`, `s →• gm`.
  - Roles: D for `pm` and `s`, N for `gm`.
  - Check: exactly 8 markings are reachable, and 2 of them (`s0` and `s4` in
    Fig. 4) have no included pending response.
  - Proof method: show that the 8 markings are closed under steps, and that
    each is reached by an explicit run.
- **Fig. 3(b), with "don't trust" (`dt`).**
  - Additional relations: `s →+ gm`, `s →• dt`, `s →+ dt`, `dt •→ s`,
    `dt →% gm`, `gm →% dt`.
- **Fig. 5.** Two runs of Fig. 3(b). Each frame of the figure gives, for every
  event, whether it is executed, pending, excluded or blocked. We check every
  frame. A hand calculation already agrees with all six frames of the second
  run.
- **Figs. 6–7.** The Büchi automaton of Fig. 3(a), checked in milestone 1c.

## 7. Order of work

| Milestone | Content | Done when |
|---|---|---|
| **1a** | Marking, graph, `step`, `enabled`, `execute`, basic properties, runs, acceptance, `step_iff`, the lemma on finite acceptance, finiteness; examples of Figs. 3–5 | all checks of §6 pass; no `sorry` or `oops` |
| **1b** | Distributed graphs (Def. 5) | definitions and the roles of the example done; acceptance is that of the underlying graph |
| **1c** | Büchi automata with τ, `B(G)`, the theorem; decide Q2 | theorem proved for finite and infinite runs, for plain and distributed graphs; Figs. 6–7 checked |

1a comes first because everything else depends on it. 1b is small. 1c is the
main theorem of Phase 1.

## 8. Decisions taken with you

- §2 of the paper (event structures, CRES, Props. 1–3) is out of scope.
- Include and exclude are two separate relations, as in later papers (D6).
- The item-by-item table for Def. 3 (§2 of this plan) is approved.
- Statements use paper-style notation, e.g. `e →•⇘G⇙ e'` (D14).
- Definitions follow the paper's form; convenient forms are derived lemmas
  (principle 1 in DESIGN.md).
- Type variables are written as words: `'event`, `'action`.
- Theories carry no references to design decisions (D-numbers); these stay in
  `docs/`.
- No record schemes for now: definitions take `('event, 'action) dcr_graph`,
  not `('event, 'action, 'more) dcr_graph_scheme`. Reason: a record extension
  can only add fields, never change existing ones, and most later features
  change the relations and the semantics, not just add fields.
- **Extensions are separate formalisms, connected by conservativity lemmas.**
  Later features (milestones, guards on relations, data, time, nesting) each
  get their own record and semantics, following the paper that introduces
  them. For example, guarded include/exclude relations change the type of
  `inclusion`/`exclusion`, the update of the marking, and the meaning of
  `inclusion_exclusion_disjoint` (with guards, a conflict needs both guards
  to hold at once). Each extension comes with a lemma that it is conservative:
  a plain graph is an extended graph with trivial extra structure (e.g. all
  guards `true`), and the two semantics agree on it.
- Def. 5 (distributed graphs) adds fields without changing the semantics of
  the underlying graph. It is the one case where a record extension (or a
  record with the graph as a field) fits; the choice is made when Def. 5 is
  formalised.

---

## Appendix: issues in §2 and Prop. 3 (not pursued)

These were found while reading, by hand. They are not formalised because §2 is
out of scope. They are kept here in case they are useful, e.g. as errata.

- **A1. Runs of event structures may repeat events (Def. 1).** Nothing in the
  definition requires the events of a run to be distinct. With one event `a`,
  the sequence `a, a, a, …` is a run.
- **A2. The definition of maximal runs (Def. 1) is too weak.**
  - The hypothesis `e↓ ⊆ (eᵢ↓ ∪ {eᵢ})` only looks at the causes of a single
    `eᵢ`. An event with two independent causes `a` and `b` is missed: the run
    `a, b` counts as maximal although the event is enabled after it.
  - The empty run counts as maximal by default.
  - Intended meaning: the configuration of the run is maximal.
- **A3. Reflexive causality as the response relation (Prop. 2).** Prop. 2 uses
  the reflexive `≤` as the response relation. Then every executed event is a
  response to itself and must happen again, so no non-empty run is accepting.
  The strict order `<` is needed. Def. 2's requirement that `→• ∪ •→` be
  acyclic has the same problem.
- **A4. Prop. 3 (CRES as DCR graphs).**
  - With the reflexive `≤` as the condition relation, `e →• e` holds for every
    `e`, so no event is ever enabled.
  - Even with `<`, there is a counterexample. Take two concurrent events `a`
    and `b` and the single response `b •→ a`:
    - The run `a, b` is not accepting in the CRES, because `a` would have to
      happen again after `b`.
    - In the DCR encoding, `a` excluded itself when it was executed, so its
      pending response is ignored and the run is accepting.
  - Possible repairs:
    - restrict responses to causal successors or conflicting events;
    - or let an earlier occurrence satisfy a response.
