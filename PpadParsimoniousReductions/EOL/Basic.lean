/-
Copyright (c) 2026 Christos Demetriou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christos Demetriou
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic

/-!
# EndOfLine Definition

In this file we introduce the `Tree` data structure and its basic operations.
-/

set_option tactic.hygienic false
open Finset

variable {N : Type*} [Nonempty N] [Fintype N] [DecidableEq N]

abbrev Edge (N : Type*) := N × N

structure EOLGraph (N : Type*) [Nonempty N] [Fintype N] where
  esucc : N → N
  epred : N → N
  zeroPoint : ∃ p: N,   (epred ∘ esucc) p = p ∧ (esucc ∘ epred) p ≠ p

namespace EOLGraph

abbrev vertexSet (_ : EOLGraph N) : Finset N  := Finset.univ

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => vertexSet G


abbrev isNext (G : EOLGraph N) (u v : N) : Prop := G.esucc u = v ∧ G.epred v = u
abbrev isPrev (G : EOLGraph N) (u v : N) : Prop := G.epred u = v ∧ G.esucc v = u
abbrev hasNext (G : EOLGraph N) (u : N) : Prop := (G.epred ∘ G.esucc) u = u
abbrev hasPrev (G : EOLGraph N) (u : N) : Prop := (G.esucc ∘ G.epred) u = u

/-- `⊤(G, u)` denotes the prop if u has next -/
scoped notation "⊤(" G "," u ")" =>  hasNext G u

/-- `⊥(G, u)` denotes the prop if u has prev -/
scoped notation "⊥(" G "," u ")" =>  hasPrev G u


scoped notation "▷(" G ")" =>  Finset.univ.filter (fun p => ⊤(G, p) ∧ ¬⊥(G, p))
scoped notation "◁(" G ")" =>  Finset.univ.filter (fun p => ⊥(G, p) ∧ ¬⊤(G, p) )

abbrev IsEdge (G : EOLGraph N) (u v : N) : Prop
    := u ≠ v ∧ esucc G  u = v ∧ epred G v = u

/-- `s(G, u, v)` denotes the prop if u,v ∈ E -/
scoped notation "s(" G "," u "," v ")" => IsEdge G u v

abbrev edgeSet (G : EOLGraph N) : Finset (N × N) := Finset.univ.product Finset.univ
  |> .filter (fun e => s(G, e.1, e.2))

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => edgeSet G

abbrev IncidentEdgeSet (G : EOLGraph N) (s : N) : Finset N := 
    {v | ∃ e ∈ E(G),⟨s, v⟩ = e ∨ ⟨v, s⟩ = e}

/-- `δ(G,v)` denotes the `edge-incident-set` of a vertex `v` in `G`. -/
scoped notation "δ(" G "," v ")" => IncidentEdgeSet G v

/-- `deg(G)` denotes the `degree` of a graph `G`. -/
scoped notation "deg(" G "," v ")" => #δ(G,v)


/-- `▵(G)` returns all starts and ends of a line -/
scoped notation "▵(" G ")" =>  ◁(G) ∪ ▷(G)

/-- `▵(G)` returns all solutions of an instance --/
scoped notation "𝒮(" G ")" => ▵(G) \ {0}

/-- `Γ(G)` returns all line vertices (deg_in = deg_out = 1) -/
scoped notation "⋄(" G ")" => Finset.univ.filter  (fun v => ⊤(G,v) ∧ ⊥(G, v))

/-- `⊙(G)` returns all lone vertices (deg = 0) -/
scoped notation "ω(" G ")" => Finset.univ.filter  (fun v => ¬ ⊤(G,v) ∧  ¬⊥(G, v))


end EOLGraph
