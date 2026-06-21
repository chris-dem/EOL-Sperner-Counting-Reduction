import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import PPADParsimoniousReductions.Defs.Basic

open Fin Nat Finset Set
open EOLGraph

section EOLGraph

variable {ν : ℕ} [NeZero ν]

theorem end_line_vertices_disjoint (G : EOLGraph ν) :
    ({▵(G) , ⋄(G), ω(G)}: Set (Finset (Fin ν))).Pairwise Disjoint := by 
    simp only [Set.Pairwise, ne_eq, Function.comp_apply, mem_singleton_iff, 
      mem_insert_iff, Disjoint, Finset.le_eq_subset,
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


/- TODO: Add construction for paths-/
/- TODO: Add theorem to show that these break into cycles, lines and lones -/

end EOLGraph



