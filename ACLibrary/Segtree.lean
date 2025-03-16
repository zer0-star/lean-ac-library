import Aesop
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Common

namespace AtCoder

@[simp]
abbrev Segtree.WF' [Monoid α] (data : Vector α (n * 2)) (k : Nat) (h' : 1 ≤ k := by get_elem_tactic) : Prop :=
  ∀ i : Nat, (h : k ≤ i ∧ i < n) → data[i] = data[i * 2] * data[i * 2 + 1]

@[simp]
abbrev Segtree.WF [Monoid α] (data : Vector α (n * 2)) : Prop :=
  Segtree.WF' data 1

structure Segtree (α : Type) [Monoid α] (n : Nat) where
  private mk' ::
  data : Vector α (n * 2)
  wf : Segtree.WF data

namespace Segtree

variable {α : Type} [Monoid α]

def mk (n : Nat) : Segtree α n := ⟨Vector.mkVector (n * 2) 1, by simp⟩

private def updateAt (i : Nat) (data : Vector α (n * 2)) (h : i < n := by get_elem_tactic) : Vector α (n * 2) :=
  data.set i (data[i * 2] * data[i * 2 + 1])

lemma updateAt_WF' (data : Vector α (n * 2)) (k : Nat) (hk : k < n) (hk' : 1 ≤ k) (h : WF' data (k + 1)) : WF' (updateAt k data) k := by
  intro i h'
  dsimp [updateAt]
  if h1 : i = k then
    have : k ≠ k * 2 := by omega
    have : k ≠ k * 2 + 1 := by omega
    simp_all
  else
    have : k ≠ i := by omega
    have : k ≠ i * 2 := by omega
    have : k ≠ i * 2 + 1 := by omega
    simp_all
    apply h
    omega

private def build' (data : Vector α (n * 2)) : Segtree α n :=
  let rec f (i : Nat) (data : Vector α (n * 2)) (hwf : WF' data (i + 1)) (h : i < n := by get_elem_tactic) : Segtree α n :=
    if _ : i = 0 then
      ⟨data, by simp_all⟩
    else
      let data' := updateAt i data
      f (i - 1) data' <| by
        have : i - 1 + 1 = i := by omega
        simp_all
        apply updateAt_WF'
        omega
        assumption
  if _ : n = 0 then
    ⟨data, by simp_all⟩
  else
    f (n - 1) data <| by
      have : n - 1 + 1 = n := by omega
      omega

def build (data : Vector α n) : Segtree α n :=
  build' <| Nat.mul_two n ▸ (Vector.mkVector n (1 : α) ++ data)

def get (t : Segtree α n) (i : Fin n) : α := t.data[i + n]

instance : GetElem (Segtree α n) Nat α fun _ i => i < n where
  getElem x i h := get x ⟨i, h⟩

lemma get_eq_get' (t : Segtree α n) (i : Nat) (h : i < n) : t[i] = t.data[i + n] := by
  dsimp [get, getElem]

@[simp]
abbrev WF_without (data : Vector α (n * 2)) (i : Nat) : Prop :=
  ∀ j : Nat, i ≠ j → (h : 1 ≤ j ∧ j < n) → data[j] = data[j * 2] * data[j * 2 + 1]

theorem WF_without_WF {data : Vector α (n * 2)} (hwf : WF data) : WF_without data i := by
  simp_all

theorem WF_WF_without_zero {data : Vector α (n * 2)} (hwf : WF_without data 0) : WF data := by
  intro i h
  have : 0 ≠ i := by omega
  simp_all

lemma WF_without_set (data : Vector α (n * 2)) (i : Nat) (v : α) (h : i < n) (hwf : WF data)
  : WF_without (data.set (i + n) v) ((i + n) / 2) := by
  intro j hj h'
  have : i + n ≠ j * 2 := by omega
  have : i + n ≠ j * 2 + 1 := by omega
  have : i + n ≠ j := by omega
  simp_all

lemma WF_without_updateAt
  (data : Vector α (n * 2)) (i : Nat) (h : i < n) (hwf : WF_without data i)
  : WF_without (updateAt i data) (i/2) := by
  intro j hj h'
  simp [updateAt]
  if h1 : i = j then
    have : i ≠ i * 2 := by omega
    have : i ≠ i * 2 + 1 := by omega
    simp_all
  else
    have : i ≠ j * 2 := by omega
    have : i ≠ j * 2 + 1 := by omega
    simp_all

private def Vector.buildAt
  (data : Vector α (n * 2)) (i : Nat) (hwf : WF_without data i) (h : i < n := by get_elem_tactic)
  : Segtree α n :=
  if h' : i = 0 then
    ⟨data, WF_WF_without_zero (h' ▸ hwf)⟩
  else
    let data' := updateAt i data
    let hwf' := WF_without_updateAt data i h hwf
    Vector.buildAt data' (i / 2) hwf'

def set (t : Segtree α n) (i : Nat) (v : α) (h : i < n := by get_elem_tactic)
  : Segtree α n :=
    Vector.buildAt (t.data.set (i + n) v) ((i + n) / 2) (WF_without_set _ _ _ h t.wf)

def modify (t : Segtree α n) (i : Nat) (f : α → α) (h : i < n := by get_elem_tactic)
  : Segtree α n :=
    t.set i (f t[i])

@[simp]
lemma get_updateAt_ne (data : Vector α (n * 2)) (i j : Nat) (h : i < n) (h' : j < n * 2) (h'' : i ≠ j)
  : (updateAt i data)[j] = data[j] := by
  dsimp [updateAt]
  exact Vector.getElem_set_ne _ _ _ _ _ _ h''

@[simp]
lemma buildAt_keep_larger (data : Vector α (n * 2)) (i : Nat) (hwf : WF_without data i) (h : i < n)
  : ∀ k, (h' : i < k ∧ k < n * 2) → (Vector.buildAt data i hwf h).data[k] = data[k] := by
  induction data, i, hwf, h using Vector.buildAt.induct with
  | case1 =>
    rw [Vector.buildAt]
    simp
  | case2 data i hwf h _ data' hwf' ih =>
    intro k h'
    rw [Vector.buildAt]
    simp_all
    rw [ih]
    simp only [data']
    rw [get_updateAt_ne]
    omega
    omega

theorem get_set_self (t : Segtree α n) (i : Nat) (v : α) (h : i < n) : (t.set i v)[i] = v := by
  dsimp [set]
  rw [get_eq_get']
  rw [buildAt_keep_larger]
  simp
  omega

theorem get_set_ne (t : Segtree α n) (i j : Nat) (v : α) (hi : i < n) (hj : j < n) (h' : i ≠ j) : (t.set i v)[j] = t[j] := by
  dsimp [set]
  rw [get_eq_get']
  rw [buildAt_keep_larger]
  apply Vector.getElem_set_ne
  simp
  assumption
  omega

def fold_all (t : Segtree α n) : α :=
  if _ : n = 0 then
    1
  else
    t.data[1]

def fold_aux
  (t : Segtree α n) (l r : Nat) (p q : α)
  (h : 1 ≤ l ∧ l ≤ r ∧ r ≤ n * 2 := by get_elem_tactic) : α :=
  if _ : l = r then
    p * q
  else
    let p' := if l % 2 = 1 then p * t.data[l] else  p
    let q' := if r % 2 = 1 then (t.data[r - 1] * q) else q
    t.fold_aux ((l+1)/2) (r/2) p' q'

def fold (t : Segtree α n) (l r : Nat) (h : 0 ≤ l ∧ l ≤ r ∧ r ≤ n := by get_elem_tactic) : α :=
  if _ : n = 0 then
    1
  else
    t.fold_aux (l+n) (r+n) 1 1

def fold_naive (t : Segtree α n) (l r : Nat) (h : 0 ≤ l ∧ l ≤ r ∧ r ≤ n := by get_elem_tactic) : α :=
  if _ : l = r then
    1
  else
    t[l] * t.fold_naive (l + 1) r
termination_by r - l

private def fold_naive'
  (t : Segtree α n) (l r : Nat)
  (h : 1 ≤ l ∧ l ≤ r ∧ r ≤ n * 2 := by get_elem_tactic) : α :=
  if _ : l = r then
    1
  else
    t.data[l] * t.fold_naive' (l + 1) r
termination_by r - l

lemma fold_naive'_def (t : Segtree α n) (l r : Nat) (h : 1 ≤ l ∧ l < r ∧ r ≤ n * 2) : t.fold_naive' l r = t.data[l] * t.fold_naive' (l + 1) r := by
  rw [fold_naive']
  split
  omega
  simp_all only

@[simp]
lemma fold_naive_one (t : Segtree α n) (i : Nat) (h : 0 ≤ i ∧ i ≤ n ) : t.fold_naive i i = 1 := by
  rw [fold_naive]
  simp

@[simp]
lemma fold_naive'_one (t : Segtree α n) (i : Nat) (h : 1 ≤ i ∧ i ≤ n * 2) : t.fold_naive' i i = 1 := by
  rw [fold_naive']
  simp

def leftmost (t : Segtree α n) (i : Nat) (h : 1 ≤ i ∧ i < 2 * n := by get_elem_tactic) : Nat :=
  if _ : i < n then
    t.leftmost (i * 2)
  else
    i

lemma leftmost_lower (t : Segtree α n) (i : Nat) (h : 1 ≤ i ∧ i < 2 * n) : t.leftmost i ≥ n := by
  rw [leftmost]
  split
  · exact leftmost_lower t (i * 2) _
  · simp_all

lemma leftmost_upper (t : Segtree α n) (i : Nat) (h : 1 ≤ i ∧ i < 2 * n) : t.leftmost i < 2 * n := by
  rw [leftmost]
  split
  · exact leftmost_upper t (i * 2) _
  · simp_all

lemma fold_naive_eq_fold_naive'
  (t : Segtree α n) (l r : Nat) (h : 0 ≤ l ∧ l ≤ r ∧ r ≤ n) (h' : n ≥ 1)
  : t.fold_naive l r = t.fold_naive' (l + n) (r + n) := by
  rw [fold_naive, fold_naive']
  split <;> split
  trivial
  omega
  omega
  have ih := fold_naive_eq_fold_naive' t (l + 1) r (by omega) h'
  have : l + 1 + n = l + n + 1 := by omega
  simp_all only [get_eq_get']
termination_by r - l

lemma fold_naive'_double (t : Segtree α n) (l r : Nat) (h : 1 ≤ l ∧ l ≤ r ∧ r ≤ n)
  : t.fold_naive' l r = t.fold_naive' (l * 2) (r * 2) := by
  rw [fold_naive', fold_naive']
  split <;> split <;> try omega
  trivial
  have := fold_naive'_double t (l + 1) r (by omega)
  conv =>
    rhs
    rw [fold_naive']
  split
  omega
  have := t.wf l (by omega)
  have : (l + 1) * 2 = l * 2 + 1 + 1 := by omega
  simp_all only [mul_assoc]
termination_by r - l

@[simp]
lemma fold_naive'_r (t : Segtree α n) (l r : Nat) (h : 1 ≤ l ∧ l ≤ r ∧ r < n * 2)
  : t.fold_naive' l r * t.data[r] = t.fold_naive' l (r + 1) := by
    rw [fold_naive', fold_naive']
    split <;> split <;> try omega
    · have : 1 ≤ r + 1 ∧ r + 1 ≤ n * 2 := by omega
      simp_all
    · rw [mul_assoc, fold_naive'_r t (l + 1) r (by omega)]
termination_by r - l

lemma fold_aux_eq_fold_naive' (t : Segtree α n) (l r : Nat) (p q : α) (h' : 1 ≤ l ∧ l ≤ r ∧ r ≤ n * 2) : t.fold_aux l r p q = p * t.fold_naive' l r * q := by
  rw [fold_aux, fold_naive']
  split
  · simp
  split <;> split <;> simp
  · rw [fold_aux_eq_fold_naive' t ((l + 1) / 2) (r / 2) (p * t.data[l]) (t.data[r - 1] * q) (by omega)]
    rw [fold_naive'_double _ _ _ (by omega)]
    have : (l + 1) / 2 * 2 = l + 1 := by omega
    have : r / 2 * 2 = r - 1 := by omega
    have := fold_naive'_r t (l + 1) (r - 1) (by omega)
    simp_all [show r - 1 + 1 = r from by omega]
    rw [← this]
    simp only [mul_assoc]
  · rw [fold_aux_eq_fold_naive']
    rw [fold_naive'_double _ _ _ (by omega)]
    have : (l + 1) / 2 * 2 = l + 1 := by omega
    have : r / 2 * 2 = r := by omega
    simp_all only [mul_assoc]
  · rw [fold_aux_eq_fold_naive']
    rw [fold_naive'_double _ _ _ (by omega)]
    have : (l + 1) / 2 * 2 = l := by omega
    have : r / 2 * 2 = r - 1 := by omega
    have := fold_naive'_r t l (r - 1) (by omega)
    rw [← fold_naive'_def]
    simp_all only [show r - 1 + 1 = r from by omega]
    rw [← this]
    simp only [mul_assoc]
    omega
  · rw [fold_aux_eq_fold_naive']
    rw [fold_naive'_double _ _ _ (by omega)]
    have : (l + 1) / 2 * 2 = l := by omega
    have : r / 2 * 2 = r := by omega
    simp_all
    rw [fold_naive'_def]
    omega
termination_by r - l

theorem fold_eq_fold_naive (t : Segtree α n) (l r : Nat) (h : 0 ≤ l ∧ l ≤ r ∧ r ≤ n)
  : t.fold l r = t.fold_naive l r := by
  rw [fold]
  split
  · have : l = r := by omega
    simp_all only
    rw [fold_naive_one]
    omega
  · rw [fold_aux_eq_fold_naive', fold_naive_eq_fold_naive']
    simp
    omega

