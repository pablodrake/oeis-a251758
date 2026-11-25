module

public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Advertised statement: OEIS A251758 (`conjecture`)

Let $n \ge 2$ have sorted divisors $1 = d_1 < d_2 < \dots < d_k = n$, let
$s(n) = \sum_{i=1}^{k-1} d_i d_{i+1}$, and define $a(n) = \lfloor n^2 / s(n) \rfloor$
(OEIS [A251758](https://oeis.org/A251758)).

This file states `OeisA251758.conjecture` from `google-deepmind/formal-conjectures`
(`FormalConjectures/OEIS/251758.lean`), originally posed by Robert G. Wilson v
(Dec 18, 2014): $p\#_{12} / p\#_4 = 35{,}336{,}848{,}261$ is the least $x \ge 2$
such that $a(x) = 8$.
-/

@[expose] public section

namespace OeisA251758

open Nat List Finset

/-- The `k`-th primorial: product of the first `k` primes `p_0 * p_1 * ... * p_{k-1}`. -/
noncomputable def kthPrimorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- $\lfloor n^2 / s \rfloor$, where $s$ is the sum of products of consecutive divisors of $n$ in
increasing order. -/
def a (n : ℕ) : ℕ :=
  let divisorsList : List ℕ := (List.range (n + 1)).filter (· ∣ n)
  let sList : List ℕ :=
    (divisorsList.zip divisorsList.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := sList.sum
  if s = 0 then 0 else n ^ 2 / s

/--
Let $p\#_i$ denote the $i$-th primorial (`kthPrimorial i`).
$p\#_{12}/p\#_4 = 35336848261$ is the least $x \ge 2$ such that $a(x) = 8$.
-/
theorem conjecture :
    IsLeast {x : ℕ | 2 ≤ x ∧ a x = 8}
      (kthPrimorial 12 / kthPrimorial (Nat.primeCounting' 8)) := by
  sorry

end OeisA251758

end
