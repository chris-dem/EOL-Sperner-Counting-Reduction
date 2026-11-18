import AlgoLib.Theory.Graph.Structures.VertexSeq.Basic
import AlgoLib.Theory.Graph.Structures.SimpleWalk
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import PPADParsimoniousReductions.EOL.Basic
import PPADParsimoniousReductions.EOL.Sequences

/-!
# Reversing an End-of-Line graph

## Automation

The normal form removes `Opp`: projections swap successor and predecessor, and
two reversals cancel. These reductions use `[simp, grind =]`.

The `inverse_*` lemmas are stated from the original graph to its opposite, so
`simp ←` registers them in reverse, removing the opposite graph. The two membership
rules also use `↓` to run before simplification changes the filter predicate inside
the notation. For `grind`, the projection equalities provide the rewrite facts:
membership notation hides the graph inside a filter predicate, which is not a
useful matching pattern.

The full `Opp` constructor is not an automation rule; the projection lemmas
expose its data without exposing the construction of its zero-point proof.
-/

set_option tactic.hygienic false

variable {α : Type*} [Nonempty α] [Fintype α] [DecidableEq α]
open EOLSequence

namespace EOLGraph
def Opp (G : EOLGraph α) : EOLGraph α := {
  esucc := G.epred
  epred := G.esucc
  zeroPoint := by
      obtain ⟨p,  hp,hr⟩ := G.zeroPoint
      have hp : p ∈ ▷(G) := by
        grind
      let p_op := EOLSequence.path_max_seq p hp
      have h_op := EOLSequence.path_max_mem_sinks p hp
      use (EOLSequence.path_max p hp)
      grind
}

scoped  postfix:max "ᵒᵖ" => Opp

/-- Rewriting this projection exposes only the reversed successor function. -/
@[simp, grind =] theorem Opp_esucc (G : EOLGraph α) : Gᵒᵖ.esucc = G.epred := rfl

/-- Rewriting this projection exposes only the reversed predecessor function. -/
@[simp, grind =] theorem Opp_epred (G : EOLGraph α) : Gᵒᵖ.epred = G.esucc := rfl

/-- Both tactics cancel two graph reversals instead of introducing new reversals. -/
@[simp, grind =] theorem Opp_Opp (G : EOLGraph α) : (Gᵒᵖ)ᵒᵖ = G := rfl

/-- Reverse edges correspond to forward edges in the original graph.
The reversed simp rule removes `Opp`; grind uses the projection lemmas above. -/
@[simp ←] theorem inverse_edge (G : EOLGraph α) (u v : α) :
      G.isNext u v ↔ Gᵒᵖ.isPrev u v := by 
      grind

/-- Normalize sink membership in the opposite graph to source membership in `G`.
`simp ↓ ←` removes `Opp` before simplifying the filter predicate; grind uses the
successor/predecessor projections. -/
@[simp ↓ ←] theorem inverse_set_source (G : EOLGraph α) (u : α) :
      u ∈ ▷(G) ↔  u ∈ ◁(Gᵒᵖ) := by 
      grind

/-- Normalize source membership in the opposite graph to sink membership in `G`.
`simp ↓ ←` removes `Opp` before simplifying the filter predicate; grind uses the
successor/predecessor projections. -/
@[simp ↓ ←] theorem inverse_set_sink (G : EOLGraph α) (u : α) :
      u ∈ ◁(G) ↔  u ∈ ▷(Gᵒᵖ) := by 
      grind

def sink_to_source (G : EOLGraph α) (u : α) (h_sink : u ∈ ◁(G)) :
    ▷(G) := {
  val := EOLSequence.path_max (G:= Gᵒᵖ) u (by grind)
  property := by 
    have h1 := path_max_mem_sinks  (G:= Gᵒᵖ)  u h_sink
    grind 
  }

/-- Normalize the map's underlying vertex to the endpoint search in the opposite
graph. Both annotations match the projection, rather than unfolding recursion. -/
@[simp, grind =] theorem sink_to_source_val (G : EOLGraph α) (u : α) (h_sink : u ∈ ◁(G)) :
    (sink_to_source G u h_sink).1 =
      EOLSequence.path_max (G := Gᵒᵖ) u ((inverse_set_sink G u).mp h_sink) := rfl



omit [DecidableEq α] in
/-- Remove the first vertex of a nontrivial valid sequence, recording its first
edge and how to reconstruct its reversal. -/
private theorem split_valid_head (H : EOLGraph α) (b : VertexSeq α) (hb : InVertexSeqInEOL H b)
    (hpos : b.length ≠ 0) :
    InVertexSeqInEOL H b.dropHead ∧ H.isNext b.head b.dropHead.head ∧
      b.reverse = b.dropHead.reverse.cons b.head := by
  induction hb with
  | singleton x => exact (hpos rfl).elim
  | cons w x hw ha ih =>
      cases w with
      | singleton v => exact ⟨.singleton x, ha, rfl⟩
      | cons w v =>
          obtain ⟨hd, he, hr⟩ := ih (by change 1 + w.length ≠ 0; omega)
          exact ⟨.cons _ x hd (by simpa using ha), he,
            congrArg ((VertexSeq.singleton x).append) hr⟩

/-- The forward and opposite searches produce sequences in reverse order. -/
@[grind =] theorem source_to_sink_inverse_seq (G : EOLGraph α) (u : α) (h_source : u ∈ ▷(G)) :
    path_max_seq u h_source =
      (path_max_seq (G := Gᵒᵖ) (source_to_sink G ⟨u, h_source⟩) (by grind)).reverse := by
  -- Generalize the comparison so the induction hypothesis also applies after
  -- removing the last vertex of a and the first vertex of b.
  have match_sequences (a b : VertexSeq α)
      (ha : InVertexSeqInEOL G a) (hb : InVertexSeqInEOL Gᵒᵖ b)
      (hsource : a.head ∈ ▷(G)) (hstop : IsMaximalSeq Gᵒᵖ b)
      (hjoin : a.tail = b.head) : a = b.reverse := by
    induction ha generalizing b with
    | singleton x =>
        -- The opposite sequence cannot leave a source of G.
        have hzero : b.length = 0 := by
          by_contra hpos
          obtain ⟨_, hedge, _⟩ := split_valid_head Gᵒᵖ b hb hpos
          grind
        rw [VertexSeq.eq_singleton_of_length_zero b hzero]
        grind
    | cons w x hw hstep ih =>
        have hpos : b.length ≠ 0 := by
          intro hz
          have := VertexSeq.head_eq_tail_of_length_zero b hz
          grind
        obtain ⟨hb', hedge, hreverse⟩ := split_valid_head Gᵒᵖ b hb hpos
        -- Remove the matching last/first vertices, then use the induction hypothesis.
        have heq := ih b.dropHead hb' hsource (by grind) (by grind)
        grind
  apply match_sequences _ _ (by simp) (by simp) (by simpa using h_source) (by simp)
  simp only [path_max_seq_head, source_to_sink_val, path_max]

end EOLGraph
