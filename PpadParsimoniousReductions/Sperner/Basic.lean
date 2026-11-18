/-
Copyright (c) 2026 Christos Demetriou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christos Demetriou
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Digits.Defs

/-!
# EndOfLine Definition

In this file we introduce the `Tree` data structure and its basic operations.
-/

set_option tactic.hygienic false
open Finset


variable {n w : ℕ} [NeZero n] [NeZero w]


abbrev Point (n w : ℕ) [NeZero n] [NeZero w] := Fin n → Fin w
abbrev Colour (n : ℕ) [NeZero n]:= Fin n → Bool

-- True = 1
-- False = -1

-- TODO: Include generalizing  strong sperner
structure kDStrongSperner (n w : ℕ) [NeZero n] [NeZero w] where
  circuit : Point n w → Colour n
  boundaryConditionLow : 
      ∀ i : Fin n , ∀ g, g i = ⟨0, by have := NeZero.ne w; omega⟩  → (circuit g) i = True
  boundaryConditionHigh : 
      ∀ i : Fin  n , ∀ g, g i = ⟨w-1, by have := NeZero.ne w; omega⟩  → (circuit g) i = False


def inner_point (p : Point n w) : Prop :=
  ∀ n : Fin n, (p n) < ⟨w - 1, by have := NeZero.ne w; omega⟩ 


def asBitFunctionOfLength {q : Nat} (xs : List (Fin 2))
    (h : xs.length = q) : Fin q → Fin 2 :=
  fun i => xs.get (Fin.cast h.symm i)

def helper (p : Point n w) (h_inner : inner_point p) (g : Fin n → Fin 2) : Point n w:=
  fun x => ⟨(p x).val + (g x).val,by rw [inner_point]at h_inner; grind⟩

theorem injective_bitmap (p : Point n w) (h_inner : inner_point p) : 
      Function.Injective (helper p h_inner) := by 
   unfold Function.Injective
   intro g1 g2 heq
   by_contra hc
   push Not at hc
   obtain  ⟨a, ha⟩ := Function.ne_iff.mp hc
   unfold helper at heq
   have hm := congrFun heq a
   simp at hm
   grind


def allBitFunctions (n : Nat) : Finset (Fin n → Fin 2) :=
  Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (Fin 2)))

def get_square (p : Point n w) (h_inner : inner_point p) : Finset (Point n w) := 
  allBitFunctions n |> .map ⟨helper p h_inner, injective_bitmap p h_inner⟩ 


def panchromatic_solution (sperner : kDStrongSperner n w) (p : Point n w) (h_inner: inner_point p) : Prop :=
  ∀ i : Fin n, ∃  j1 ∈ S, ∃ j2 ∈ S, (sperner.circuit j1) i !=  (sperner.circuit j2) i
    where 
      S := get_square p h_inner

