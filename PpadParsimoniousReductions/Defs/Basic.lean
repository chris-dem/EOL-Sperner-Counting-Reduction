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
open Fin Nat Finset

variable {ν : ℕ} [NeZero ν]

abbrev Vertex (ν : ℕ) := Fin ν
abbrev Edge (ν : ℕ) := Fin ν × Fin ν

structure EOLGraph (ν : ℕ) [NeZero ν] where
  esucc : Fin ν → Fin ν
  epred : Fin ν → Fin ν
  zeroPoint : (epred ∘ esucc) 0 = 0 ∧ (esucc ∘ epred) 0 ≠ 0

namespace EOLGraph

abbrev vertexSet (_ : EOLGraph ν) : Finset (Fin ν) := Finset.univ

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => vertexSet G


abbrev hasNext (G : EOLGraph ν) (u : Fin ν) : Prop :=  (G.epred ∘ G.esucc) u = u
abbrev hasPrev (G : EOLGraph ν) (u : Fin ν) : Prop :=  (G.esucc ∘ G.epred) u = u

/-- `⊤(G, u)` denotes the prop if u has next -/
scoped notation "⊤(" G "," u ")" =>  hasNext G u



/-- `⊥(G, u)` denotes the prop if u has prev -/
scoped notation "⊥(" G "," u ")" =>  hasPrev G u


scoped notation "▷(" G ")" =>  Finset.univ.filter (fun p => ⊤(G, p) ∧ ¬⊥(G, p))
scoped notation "◁(" G ")" =>  Finset.univ.filter (fun p => ⊥(G, p) ∧ ¬⊤(G, p) )

abbrev IsEdge (G : EOLGraph ν) (u v : Vertex ν) : Prop
    := u ≠ v ∧ esucc G  u = v ∧ epred G v = u

/-- `s(G, u, v)` denotes the prop if u,v ∈ E -/
scoped notation "s(" G "," u "," v ")" => IsEdge G u v

abbrev edgeSet (G : EOLGraph ν) : Finset (Edge ν) := Finset.univ.product Finset.univ
  |> .filter (fun e => s(G, e.1, e.2))

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => edgeSet G

abbrev IncidentEdgeSet (G : EOLGraph ν) (s : Vertex ν) :
  Finset (Vertex ν) := {v | ∃ e ∈ E(G),⟨s, v⟩ = e ∨ ⟨v, s⟩ = e}

/-- `δ(G,v)` denotes the `edge-incident-set` of a vertex `v` in `G`. -/
scoped notation "δ(" G "," v ")" => IncidentEdgeSet G v

/-- `deg(G)` denotes the `degree` of a graph `G`. -/
scoped notation "deg(" G "," v ")" => #δ(G,v)


/-- `▵(G)` returns all starts and ends of a line -/
scoped notation "▵(" G ")" =>  ◁(G) ∪ ▷(G)

/-- `Γ(G)` returns all line vertices (deg_in = deg_out = 1) -/
scoped notation "⋄(" G ")" => Finset.univ.filter  (fun v => ⊤(G,v) ∧ ⊥(G, v))

/-- `⊙(G)` returns all lone vertices (deg = 0) -/
scoped notation "ω(" G ")" => Finset.univ.filter  (fun v => ¬ ⊤(G,v) ∧  ¬⊥(G, v))

end EOLGraph
