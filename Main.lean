-- test code for https://judge.yosupo.jp/problem/point_set_range_composite

import ACLibrary

import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Order.Nat


open AtCoder

abbrev M := Multiplicative (Tropical Natᵒᵈ)

def M.ofNat (n : Nat) : M := by
  simp [M, Multiplicative, Tropical, OrderDual]
  exact n

def M.toNat (m : M) : Nat := by
  simp [M, Multiplicative, Tropical, OrderDual] at m
  exact m

instance : ToString M where
  toString m := toString m.toNat

-- macro "assume!" cond:term : doElem =>
--   `(doElem| have := if h : $cond then h else unreachable!)

def main : IO Unit := do
  let stdin ← IO.getStdin
  let [N, Q] := (← stdin.getLine).trimRight.splitOn.map String.toNat!
    | unreachable!
  let A := (← stdin.getLine).trimRight.splitOn.map String.toNat!
  let mut segt : Segtree M N := Segtree.build <| (Vector.range N).map fun i => .ofNat A[i]!
  for _ in [:Q] do
    let [t, x, y] := (← stdin.getLine).trimRight.splitOn.map String.toNat!
      | unreachable!
    if t == 1 then
      if _h : 1 ≤ x ∧ x ≤ N then
        segt := segt.set (x - 1) (.ofNat y)
    else if t == 2 then
      if _h : 1 ≤ x ∧ x ≤ y ∧ y ≤ N then
        println! segt.fold (x - 1) y
    else
      if _h : 1 ≤ x ∧ x ≤ N then
        println! Id.run do
          let mut ok := x - 1
          let mut ng := N + 1
          while ok + 1 < ng do
            let mid := (ng + ok) / 2
            assert! ok < mid ∧ mid < ng
            if _h' : x - 1 < mid ∧ mid ≤ N then
              if (segt.fold (x - 1) mid).toNat < y then
                ok := mid
              else
                ng := mid
          return ok + 1
