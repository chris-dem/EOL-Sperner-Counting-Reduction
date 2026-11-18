# Choosing `simp` and `grind`

Start with **`simp` for simplification**, **`grind` for combining facts**, and
**an explicit lemma or induction for the main mathematical argument**.

## Using a tactic versus registering a lemma

`by simp` runs a tactic in one proof. `@[simp]` registers a theorem for future
calls; it does not prove the theorem. The same applies to `grind`.

Try `simp [some_lemma]` or `grind [some_lemma]` locally first. Use
`exact some_lemma ...` when it already proves your goal, or `rw [some_lemma]`
for a particular rewrite. Register a global attribute when that use is useful
across many proofs.

## Choosing an attribute

| Attribute | When it helps | Example in this project |
| --- | --- | --- |
| `@[simp]` | Rewrite to a simpler, consistent form, or discharge a routine property. | A constructed sequence's head is its starting vertex. |
| `@[grind =]` | Let the solver add an equality when it encounters a term matching its left-hand side. | `path_max_seq_head`, projection lemmas, and `Opp_Opp`. |
| `@[grind →]` | Derive consequences from known hypotheses. | Validity plus a source head implies `vs.nodup`. |
| `@[grind ←]` | Instantiate a theorem by matching terms from its conclusion. | Supply validity or maximality for a constructed sequence already appearing in the proof. |

`@[simp, grind =]` makes an equality available to both tactics.

Two optional simp modifiers:

- `←` uses the theorem in reverse, e.g. to remove an opposite graph.
- `↓` runs before simplifying subexpressions. Use it when ordinary ordering
  prevents matching, as happens with our source/sink filter predicates.

Thus `@[simp ↓ ←]` does both.

**The arrows differ:** `simp ←` reverses a rewrite; `grind ←` selects matching
patterns from the conclusion. It does not reverse an implication.

## A small example using your definitions

This block can be copied into a Lean file in this project:

```lean
import PPADParsimoniousReductions.Defs.Opp

open EOLGraph EOLSequence

variable {α : Type*} [Nonempty α] [Fintype α] [DecidableEq α]
variable (G : EOLGraph α)

-- Simplification: replace the head by the starting vertex.
-- Uses path_max_seq_head, tagged @[simp, grind =].
example (u : α) (hs : u ∈ ▷(G)) :
    (path_max_seq u hs).head = u := by
  simp

-- Reasoning: combine validity and the source hypothesis.
-- Uses maximal_source_seq_acyclic, tagged @[grind →].
example (vs : VertexSeq α) (hw : InVertexSeqInEOL G vs)
    (hs : vs.head ∈ ▷(G)) : vs.nodup := by
  grind

-- Simplification in reverse: remove the opposite graph.
-- inverse_set_source is stated in the reverse direction,
-- and registered with @[simp ↓ ←].
example (u : α) : u ∈ ◁(Gᵒᵖ) ↔ u ∈ ▷(G) := by
  simp
```

## When to leave a lemma explicit

- **Recursive algorithms:** prove their specifications by functional induction;
  register small consequences instead of globally unfolding `path_max_seq`.
- **Witness-producing lemmas:** use `obtain` with `exists_pred_of_mem_ne_head`
  when you need a predecessor.
- **Bundled specifications:** use `path_max_seq_spec` explicitly for several
  properties together; its components serve automation.
- **Unfinished proofs:** leave inverse-law templates unregistered until proved.
  Their round-trip equalities can then use `@[simp, grind =]`.

Choose one simplification direction: here, projections reduce to their values
and opposite graphs reduce to the original graph. Do not register both
directions as simp rules, since they can repeatedly undo one another.
