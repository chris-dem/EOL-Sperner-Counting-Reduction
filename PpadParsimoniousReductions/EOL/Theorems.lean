import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic

import Mathlib.Data.Nat.Basic

import PPADParsimoniousReductions.EOL.Basic
import PPADParsimoniousReductions.EOL.Opp

/-!
# The source-sink equivalence

## Automation

The equivalence application lemmas use `[simp, grind =]` to reduce the packaged
equivalence to its underlying endpoint maps. They do not unfold either search.

The two inverse-law templates remain unregistered while their proofs are `sorry`.
After they are proved, `[simp, grind =]` would make each round trip reduce to its
starting vertex. The bundled bijectivity theorem is kept as an explicit result.
-/

open EOLGraph EOLSequence

section EOLGraph

/-
variable {ν : ℕ} [NeZero ν]

theorem end_line_vertices_disjoint (G : EOLGraph ν) :
    ({▵(G) , ⋄(G), ω(G)}: Set (Finset (Fin ν))).Pairwise Disjoint := by 
    simp only [Set.Pairwise, ne_eq, Function.comp_apply, mem_singleton_iff, 
      mem_insert_iff, Disjoint,
      Finset.bot_eq_empty, subset_empty, forall_eq_or_imp, forall_eq,
      not_true_eq_false, forall_self_imp, IsEmpty.forall_iff, true_and, and_true]
    grind



/-- Vertices are partitioned, to ends, lines, and lones -/
theorem vertex_partition (G : EOLGraph ν) :
      ▵(G) ∪ ⋄(G) ∪ ω(G) = V(G) := by 
      ext v
      constructor
      · grind
      · grind

/-- Vertices are partitioned, to ends, lines, and lones -/
theorem sources_equal_sinks (G : EOLGraph ν) :
      #◁(G) = #▷(G):= by
        sorry

theorem source_sink_match (G: EOLGraph ν)
    (v : Fin ν) (hin : v ∈ ▷(G)) (w: Walk ν)
    (hp: Path ν) (hw: w.head = v) (hin: IsPath w a)
      := by sorry

theorem source_sink_bijection  (G : EOLGraph ν): Nonempty (▷(G) ≃ ◁(G))
      := by
        sorry


theorem sol_eol_nonempty (G : EOLGraph ν) : 𝒮(G)  != ∅ := by
  sorry

-/

/- TODO: Add theorem to show that these break into cycles, lines and lones -/

variable {α : Type*} [Nonempty α] [Fintype α] [DecidableEq α]



/-- Following a source to its sink and back recovers the source. -/
@[grind =] theorem sink_to_source_source_to_sink (G : EOLGraph α) (u : ▷(G)) :
    sink_to_source G (source_to_sink G u).1 (source_to_sink G u).2 = u := by
  obtain ⟨u, hu⟩ := u
  simp only [ne_eq, Function.comp_apply, sink_to_source, path_max, source_to_sink_val,
    Subtype.mk.injEq]
  let ltr_seq := path_max_seq u hu
  have hltr_head : ltr_seq.head = u := by grind
  have hs := path_max_mem_sinks  u hu
  let rtl_seq := path_max_seq (G := Gᵒᵖ) (path_max_seq u hu).tail (by rw [path_max] at hs ; grind)
  change rtl_seq.tail = u
  grind


/-- Following a sink to its source and back recovers the sink. -/
theorem source_to_sink_sink_to_source (G : EOLGraph α) (v : ◁(G)) :
    source_to_sink G (sink_to_source G v.1 v.2) = v := by
  obtain ⟨v, hv⟩ := v
  simp [source_to_sink, sink_to_source, path_max]
  grind


/-- The two endpoint maps form an equivalence once the inverse laws are proved. -/
def source_sink_equiv (G : EOLGraph α) : ▷(G) ≃ ◁(G) where
  toFun := source_to_sink G
  invFun v := sink_to_source G v.1 v.2
  left_inv := sink_to_source_source_to_sink G
  right_inv := source_to_sink_sink_to_source G

/-- Normalize forward application of the equivalence to the source-to-sink map.
`grind =` matches precisely the left-hand application, as does the simp rule. -/
@[simp, grind =] theorem source_sink_equiv_apply (G : EOLGraph α) (u : ▷(G)) :
    source_sink_equiv G u = source_to_sink G u := rfl

/-- Normalize inverse application to the sink-to-source map, without unfolding
the endpoint search. Both tactics match the left-hand application. -/
@[simp, grind =] theorem source_sink_equiv_symm_apply (G : EOLGraph α) (v : ◁(G)) :
    (source_sink_equiv G).symm v = sink_to_source G v.1 v.2 := rfl

theorem source_sink_bijective (G : EOLGraph α) :
    Function.Bijective (source_to_sink G) :=
  (source_sink_equiv G).bijective

end EOLGraph



