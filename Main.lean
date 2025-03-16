-- test code for https://judge.yosupo.jp/problem/point_set_range_composite

import ACLibrary
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Field.ZMod

open AtCoder

axiom prime_998 : Nat.Prime 998244353

instance : Fact (Nat.Prime 998244353) := ⟨prime_998⟩

abbrev Mint := ZMod 998244353

instance : ToString Mint where
  toString x := toString x.val

structure Affine : Type where
  (a b : Mint)

namespace Affine

theorem ext {x y : Affine} : x.a = y.a → x.b = y.b → x = y := by
  intros
  cases x
  cases y
  simp_all only

-- compose left to right
def compose (f g : Affine) : Affine := ⟨f.a * g.a, f.b * g.a + g.b⟩

def one : Affine := ⟨1, 0⟩

theorem compose_assoc (f g h : Affine) : (f.compose g).compose h = f.compose (g.compose h) := by
  dsimp [compose]
  ring_nf

theorem compose_one_left (f : Affine) : one.compose f = f := by
  cases f
  dsimp [one, compose]
  simp

theorem compose_one_right (f : Affine) : f.compose one = f := by
  cases f
  dsimp [one, compose]
  simp

instance : Monoid Affine where
  one := one
  mul f g := f.compose g
  mul_assoc := compose_assoc
  one_mul := compose_one_left
  mul_one := compose_one_right

instance : CoeFun Affine (fun _ => Mint → Mint) where
  coe f := fun x => f.a * x + f.b

end Affine

-- macro "assume!" cond:term : doElem =>
--   `(doElem| have := if h : $cond then h else unreachable!)

def main : IO Unit := do
  let stdin ← IO.getStdin
  let [N, Q] := (← stdin.getLine).trimRight.splitOn.map String.toNat!
    | unreachable!
  let mut segt : Segtree Affine N ← Segtree.build <$> (Vector.range N).mapM fun _ => do
    let [a, b] := (← stdin.getLine).trimRight.splitOn.map String.toNat!
      | unreachable!
    pure <| Affine.mk a b
  for _ in [:Q] do
    let [t, a, b, c] := (← stdin.getLine).trimRight.splitOn.map String.toNat!
      | unreachable!
    if t == 0 then
      if _h : 0 ≤ a ∧ a < N then
        segt := segt.set a ⟨b, c⟩
    else
      if _h : 0 ≤ a ∧ a < b ∧ b ≤ N then
        println! (segt.fold a b) c
