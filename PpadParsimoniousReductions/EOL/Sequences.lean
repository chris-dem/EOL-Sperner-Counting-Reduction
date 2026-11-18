import AlgoLib.Theory.Graph.Structures.Basic
import AlgoLib.Theory.Graph.Structures.VertexSeq.Basic
import AlgoLib.Theory.Graph.Structures.SimpleWalk
import Mathlib.Data.Fintype.Card
import PPADParsimoniousReductions.EOL.Basic

/-!
# Source sequences and their maximal extensions

## Automation

* `simp` uses the proved properties of a constructed sequence and projections of
  endpoint maps. Endpoint membership uses `simp ↓` to run before simplification
  changes the filter predicate in the source/sink notation. The recursive
  functions themselves are not simp rules.
* `grind →` propagates known validity, source, and maximality hypotheses to
  acyclicity and sink membership.
* `grind ←` indexes properties of constructed results by their conclusions, so
  automation uses a result already mentioned in the goal or context.
* The worker specification and existential predecessor lemma remain explicit:
  they are proof tools, rather than rules for expanding the search automatically.
-/

open EOLGraph SimpleWalk


variable {α : Type*} [Nonempty α] [Fintype α]

/-- A sequence whose consecutive vertices follow the graph's successor relation.
The inductive `grind` registration supplies structural constructor/case reasoning. -/
@[grind] inductive InVertexSeqInEOL (G : EOLGraph α) : VertexSeq α → Prop
  | singleton v : InVertexSeqInEOL G (.singleton v)
  | cons (w : VertexSeq  α) (u: α)
      (hw: InVertexSeqInEOL G w)
      (ha: G.isNext w.tail u) : InVertexSeqInEOL G (w.cons u)


/-- No valid successor exists at the tail. The existing `grind` registration
unfolds only this one-step predicate, without unfolding the path search. -/
@[grind] def IsMaximalSeq [DecidableEq α] (G : EOLGraph α) (vs : VertexSeq α)
    : Prop :=  ¬ G.hasNext vs.tail

namespace EOLSequence


/-- A nontrivial maximal source sequence ends at a sink.

`grind →` derives endpoint membership from the structural hypotheses. This is
not a simp rule: its purpose is to combine hypotheses, rather than normalize a term. -/
@[grind →] theorem maximal_source_seq_ends_sink [DecidableEq α] (G : EOLGraph α) (vs : VertexSeq α)
    (hin : InVertexSeqInEOL G vs) (hmax : IsMaximalSeq G vs) :
      vs.head ∈ ▷(G) →  vs.tail ∈ ◁(G) := by
    intro h_head
    simp only [hasPrev]
    grind

@[grind →] theorem maximal_source_seq_gt_1 [DecidableEq α] (G : EOLGraph α) (vs : VertexSeq α)
    (hin : InVertexSeqInEOL G vs) (hmax : IsMaximalSeq G vs) :
      vs.head ∈ ▷(G) → vs.length >= 1 := by
    intro h
    by_contra h_cc
    push Not at h_cc
    simp only [Nat.lt_one_iff] at h_cc
    cases vs with
      |singleton u =>
        simp [IsMaximalSeq] at hmax
        simp at h
        grind
      |cons  =>
        simp [VertexSeq.length] at h_cc







/-- Every vertex other than the head has a predecessor before the final vertex.

This lemma is used explicitly, since its existential conclusion introduces a new
vertex witness instead of simplifying an existing expression. -/
theorem exists_pred_of_mem_ne_head (G : EOLGraph α) (vs : VertexSeq α)
    (hw : InVertexSeqInEOL G vs) {v : α} (hv : v ∈ vs) (hne : v ≠ vs.head) :
    ∃ u ∈ vs.dropTail, G.isNext u v := by
  induction hw with
  | singleton u => exact (hne (VertexSeq.mem_singleton.mp hv)).elim
  | cons w x hw ha ih =>
      rcases (VertexSeq.mem_cons v x w).mp hv with hv | rfl
      · obtain ⟨u, hu, huv⟩ := ih hv hne
        exact ⟨u, VertexSeq.dropTail_subset w u hu, huv⟩
      · exact ⟨w.tail, VertexSeq.tail_mem w, ha⟩

/-- A valid sequence starting at a source has no repeated vertices.

`grind →` adds acyclicity when the validity and source hypotheses are available. -/
@[grind →] theorem maximal_source_seq_acyclic [DecidableEq α] (G : EOLGraph α) (vs : VertexSeq α)
    (hw : InVertexSeqInEOL G vs) (h_start : vs.head ∈ ▷(G)) : vs.nodup := by
  induction vs with
  | singleton => 
    trivial
  | cons xs x ih =>
      cases hw with
      | cons _ _ hw ha =>
          have hnd : xs.nodup := by
            cases xs with
            | singleton => trivial
            | cons w v => exact ih hw h_start
          refine ⟨hnd, ?_⟩
          intro hx
          have hne : x ≠ xs.head := by
            intro heq
            apply (Finset.mem_filter.mp h_start).2.2
            change G.esucc (G.epred xs.head) = xs.head
            rw [← heq, ha.2, ha.1]
          obtain ⟨u, hu, huv⟩ := exists_pred_of_mem_ne_head G xs hw hx hne
          have hu_eq : u = xs.tail := huv.2.symm.trans ha.2
          have hpos : xs.length ≠ 0 := by
            intro hzero
            apply hne
            rw [VertexSeq.eq_singleton_of_length_zero xs hzero] at hx
            exact VertexSeq.mem_singleton.mp hx
          exact xs.tail_not_mem_dropTail_of_nodup hnd hpos (hu_eq ▸ hu)

/-- The complete sequence obtained by following successors from a source. -/
def path_max_seq [DecidableEq α] {G : EOLGraph α} (u : α)
    (h_source : u ∈ ▷(G)) : VertexSeq α :=
  go (.singleton u) (.singleton u) h_source
where
  go (vs : VertexSeq α) (hw : InVertexSeqInEOL G vs)
      (h_start : vs.head ∈ ▷(G)) : VertexSeq α :=
    if h_next : G.hasNext vs.tail then
      go (vs.cons (G.esucc vs.tail)) (by
        exact InVertexSeqInEOL.cons vs (G.esucc vs.tail) hw (by grind)) h_start
    else
      vs
  termination_by Fintype.card α - vs.length
  decreasing_by
    have hw_cons := InVertexSeqInEOL.cons vs (G.esucc vs.tail) hw (by grind)
    have hidup := maximal_source_seq_acyclic G (vs.cons (G.esucc vs.tail)) hw_cons (by grind)
    have hlen : vs.length < (vs.cons (G.esucc vs.tail)).length := by grind
    have hlen_bound : (vs.cons (G.esucc vs.tail)).length ≤ Fintype.card α := by
      have hlist_nodup : (vs.cons (G.esucc vs.tail)).toList.Nodup :=
        (VertexSeq.nodup_iff_toList_nodup _).mp hidup
      have hcard : (vs.cons (G.esucc vs.tail)).toList.toFinset.card =
          (vs.cons (G.esucc vs.tail)).toList.length :=
        List.toFinset_card_of_nodup hlist_nodup
      have hbound := (vs.cons (G.esucc vs.tail)).toList.toFinset.card_le_univ
      rw [hcard, VertexSeq.length_toList] at hbound
      omega
    omega

/-- Extending a valid source sequence preserves its head and ends at a maximal sequence. -/
theorem path_max_seq.go_spec [DecidableEq α] {G : EOLGraph α}
    (vs : VertexSeq α) (hw : InVertexSeqInEOL G vs) (h_start : vs.head ∈ ▷(G)) :
    InVertexSeqInEOL G (path_max_seq.go vs hw h_start) ∧
      (path_max_seq.go vs hw h_start).head = vs.head ∧
      IsMaximalSeq G (path_max_seq.go vs hw h_start) := by
  fun_induction path_max_seq.go vs hw h_start with
  | case1 vs hw h_start h_next ih =>
      exact ih
  | case2 vs hw h_start h_next =>
      exact ⟨hw, rfl, h_next⟩

/-- The constructed sequence is valid, starts at the given source, and is maximal.

Keep this bundled specification explicit; the component lemmas below provide
the smaller rules used by `simp` and `grind`. -/
theorem path_max_seq_spec [DecidableEq α] {G : EOLGraph α} (u : α)
    (h_source : u ∈ ▷(G)) :
    InVertexSeqInEOL G (path_max_seq u h_source) ∧
      (path_max_seq u h_source).head = u ∧
      IsMaximalSeq G (path_max_seq u h_source) :=
  path_max_seq.go_spec (.singleton u) (.singleton u) h_source

/-- Validity of the constructed sequence is discharged by `simp`.
`grind ←` uses the constructed result in the conclusion as its trigger. -/
@[simp, grind ←] theorem path_max_seq_in [DecidableEq α] {G : EOLGraph α} (u : α)
    (h_source : u ∈ ▷(G)) : InVertexSeqInEOL G (path_max_seq u h_source) :=
  (path_max_seq_spec u h_source).1

/-- Both tactics replace the constructed sequence's head by its starting vertex.
`grind =` matches the left-hand projection, without unfolding the recursive worker. -/
@[simp, grind =] theorem path_max_seq_head [DecidableEq α] {G : EOLGraph α} (u : α)
    (h_source : u ∈ ▷(G)) : (path_max_seq u h_source).head = u :=
  (path_max_seq_spec u h_source).2.1

/-- Maximality is a proved property of the constructed result: `simp` discharges
it and `grind ←` indexes the conclusion, rather than unfolding the search. -/
@[simp, grind ←] theorem path_max_seq_isMaximal [DecidableEq α] {G : EOLGraph α} (u : α)
    (h_source : u ∈ ▷(G)) : IsMaximalSeq G (path_max_seq u h_source) :=
  (path_max_seq_spec u h_source).2.2

/-- The endpoint of the maximal sequence starting at a source. -/
def path_max [DecidableEq α] {G : EOLGraph α} (u : α)
    (h_source : u ∈ ▷(G)) : α :=
  (path_max_seq (G := G) u h_source).tail



/-- Following successors from a source ends at a sink.

`simp ↓` discharges this fact before simplifying the filter predicate in `◁(G)`;
ordinary bottom-up simplification can change that predicate before the rule matches.
`grind ←` uses the constructed endpoint in the conclusion to instantiate the fact.
Neither tactic unfolds the search. -/
@[simp↓, grind ←] theorem path_max_mem_sinks [DecidableEq α] {G : EOLGraph α} (u : α)
    (h_source : u ∈ ▷(G)) : path_max u h_source ∈ ◁(G) := by
  obtain ⟨hw, hhead, hmax⟩ := path_max_seq_spec u h_source
  apply maximal_source_seq_ends_sink G _ hw hmax
  simpa only [hhead] using h_source

/-- Send each source to the sink at the end of its maximal sequence. -/
def source_to_sink [DecidableEq α] (G : EOLGraph α) (u : ▷(G)) : ◁(G) :=
  ⟨path_max u.1 u.2, path_max_mem_sinks u.1 u.2⟩

/-- Normalize the underlying vertex of the subtype-valued map to its endpoint.
`simp` rewrites the projection; `grind =` matches that same left-hand expression. -/
@[simp, grind =] theorem source_to_sink_val [DecidableEq α] (G : EOLGraph α) (u : ▷(G)) :
    (source_to_sink G u).1 = path_max u.1 u.2 := rfl


end EOLSequence
