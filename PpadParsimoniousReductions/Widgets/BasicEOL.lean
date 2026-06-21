-- Widgets: inline images and SVGs rendered directly in the infoview.
import ProofWidgets.Component.RefreshComponent
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.GraphDisplay
import PPADParsimoniousReductions.Defs.Basic

open Lean Server Widget ProofWidgets Jsx
open EOLGraph
set_option linter.hashCommand false
abbrev n := 50

abbrev VertexType := Fin n

def mySucc (x : VertexType) :=  (2 * x) +1
def myPred (x : VertexType) := if mySucc x = 0 then 0 else
  (x - 1)/2

def eolGraph : EOLGraph n := {
 esucc := mySucc,
 epred := myPred,
 zeroPoint := by decide
}

def mkEdge (st : VertexType × VertexType) : GraphDisplay.Edge := {
    source := st.1.val.repr,
    target := st.2.val.repr
}


def eSet := List.finRange n >>= (fun s =>(List.finRange n).map (fun t => (s,t)))
    |> .filter (fun e => s(eolGraph, e.1, e.2)) |> List.toArray

def pickCol (G : EOLGraph n) (v : Fin n) :=
  if ⊤(G,v) ∧ ⊥(G, v) then
    "red"
  else
    "blue"


open ProofWidgets.GraphDisplay in
def mkVertex (id : VertexType) : Vertex := {
  id := id.val.repr
  label := mkCircle #[("fill", pickCol eolGraph id)]
  boundingShape := .circle 10
}


def vSet := eSet.flatMap (fun e => #[e.1, e.2]) |> Array.dedupSorted
  |> Array.map mkVertex


#eval eSet

#html <GraphDisplay
    vertices={vSet}
    edges={eSet.map mkEdge}
  />
