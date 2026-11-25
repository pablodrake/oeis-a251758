module

public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Proof of OEIS A251758 (`conjecture`)

Let $n \ge 2$ have sorted divisors $1 = d_1 < d_2 < \dots < d_k = n$, and let
$s(n) = \sum_{i=1}^{k-1} d_i d_{i+1}$. Define $a(n) = \lfloor n^2 / s(n) \rfloor$.

**Conjecture (Robert G. Wilson v, Dec 18 2014; `FormalConjectures/OEIS/251758.lean`):**
$$X_0 = \frac{p\#_{12}}{p\#_4} = 11 \cdot 13 \cdot 17 \cdot 19 \cdot 23 \cdot 29 \cdot 31 \cdot 37 = 35336848261$$
is the **least** integer $x \ge 2$ such that $a(x) = 8$.
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

/-- Sum of products of consecutive elements of a list. -/
def consecProdSum (L : List ℕ) : ℕ :=
  ((L.zip L.tail).map fun p : ℕ × ℕ => p.1 * p.2).sum

/-- Sum of reciprocals of products of consecutive elements of a list. -/
def recipConsec (L : List ℕ) : ℚ :=
  ((L.zip L.tail).map fun p : ℕ × ℕ => (1 : ℚ) / ((p.1 : ℚ) * (p.2 : ℚ))).sum

/-- Sorted list of divisors of `n`. -/
def divList (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (· ∣ n)

lemma a_eq (n : ℕ) :
    a n = if consecProdSum (divList n) = 0 then 0 else n ^ 2 / consecProdSum (divList n) := rfl

/-! ### Helper Lemmas -/

private lemma list_eq_of_perm_of_pairwise_le {L₁ L₂ : List ℕ}
    (hp : L₁.Perm L₂) (h1 : L₁.Pairwise (· ≤ ·)) (h2 : L₂.Pairwise (· ≤ ·)) : L₁ = L₂ :=
  hp.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hab hba) h1 h2

private lemma list_eq_of_perm_of_pairwise_ge {L₁ L₂ : List ℕ}
    (hp : L₁.Perm L₂) (h1 : L₁.Pairwise (· ≥ ·)) (h2 : L₂.Pairwise (· ≥ ·)) : L₁ = L₂ :=
  hp.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hba hab) h1 h2

private lemma finset_prod_sort_eq {α : Type*} [CommMonoid α] (S : Finset ℕ) (f : ℕ → α) :
    ((S.sort (· ≤ ·)).map f).prod = ∏ x ∈ S, f x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hperm : ((insert a s).sort (· ≤ ·)).Perm (a :: s.sort (· ≤ ·)) := by
      rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
        (List.nodup_cons.mpr ⟨by simp [Finset.mem_sort, ha], Finset.sort_nodup _ _⟩)]
      intro x; simp [Finset.mem_sort]
    rw [(hperm.map f).prod_eq, List.map_cons, List.prod_cons, ih, Finset.prod_insert ha]

private lemma finset_sum_sort_eq {α : Type*} [AddCommMonoid α] (S : Finset ℕ) (f : ℕ → α) :
    ((S.sort (· ≤ ·)).map f).sum = ∑ x ∈ S, f x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hperm : ((insert a s).sort (· ≤ ·)).Perm (a :: s.sort (· ≤ ·)) := by
      rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
        (List.nodup_cons.mpr ⟨by simp [Finset.mem_sort, ha], Finset.sort_nodup _ _⟩)]
      intro x; simp [Finset.mem_sort]
    rw [(hperm.map f).sum_eq, List.map_cons, List.sum_cons, ih, Finset.sum_insert ha]

private lemma prod_primeFactors_pow_eq_self {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
  have h := Nat.prod_factorization_pow_eq_self hn
  unfold Finsupp.prod at h
  rwa [Nat.support_factorization] at h

private lemma finset_prod_le_prod_Q {ι : Type*} {s : Finset ι} {f g : ι → ℚ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (hfg a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (le_trans (hf a (Finset.mem_insert_self a s)) (hfg a (Finset.mem_insert_self a s)))

private lemma finset_prod_le_prod_Nat {ι : Type*} {s : Finset ι} {f g : ι → ℕ}
    (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Nat.mul_le_mul (hfg a (Finset.mem_insert_self a s))
      (ih fun i hi => hfg i (Finset.mem_insert_of_mem hi))

private lemma list_prod_map_eq_fin_prod (L : List ℕ) (f : ℕ → ℕ) :
    (L.map f).prod = ∏ i : Fin L.length, f (L[i.1]'i.2) := by
  induction L with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Fin.prod_univ_succ, ih]
    rfl

private lemma finsupp_sum_apply_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ →₀ ℕ) (q : ℕ) :
    (∑ j ∈ s, f j) q = ∑ j ∈ s, f j q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finsupp.add_apply, ih]

private lemma factorization_eq_zero_of_notMem_pf {n p : ℕ} (hp : p ∉ n.primeFactors) :
    n.factorization p = 0 := by
  rw [← Nat.support_factorization] at hp
  exact Finsupp.notMem_support_iff.mp hp

private lemma prime_dvd_finset_prod {ι : Type*} {s : Finset ι} {f : ι → ℕ} {p : ℕ}
    (hp : p.Prime) (h : p ∣ ∏ i ∈ s, f i) : ∃ i ∈ s, p ∣ f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty] at h
    exact absurd (Nat.dvd_one.mp h) hp.ne_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    rcases hp.dvd_mul.mp h with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · rcases ih h2 with ⟨i, hi, hdi⟩
      exact ⟨i, Finset.mem_insert_of_mem hi, hdi⟩

/-! ### Part 1: Properties of `divList`, `consecProdSum`, and `recipConsec` -/

lemma divList_sorted (n : ℕ) : (divList n).Pairwise (· < ·) := by
  unfold divList
  exact List.Pairwise.filter _ List.pairwise_lt_range

lemma mem_divList {n d : ℕ} (hn : 1 ≤ n) : d ∈ divList n ↔ d ∣ n := by
  unfold divList
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, and_iff_right_iff_imp]
  intro hd
  have := Nat.le_of_dvd (by omega) hd
  omega

lemma divList_pos {n d : ℕ} (hn : 1 ≤ n) (hd : d ∈ divList n) : 0 < d := by
  rw [mem_divList hn] at hd
  exact Nat.pos_of_dvd_of_pos hd (by omega)

lemma finset_sort_pairwise_lt (S : Finset ℕ) : (S.sort (· ≤ ·)).Pairwise (· < ·) := by
  have hle : (S.sort (· ≤ ·)).Pairwise (· ≤ ·) := Finset.pairwise_sort S (· ≤ ·)
  have hne : (S.sort (· ≤ ·)).Pairwise (· ≠ ·) := Finset.sort_nodup S (· ≤ ·)
  exact (hle.and hne).imp fun h => lt_of_le_of_ne h.1 h.2

lemma divList_eq_sort_divisors {n : ℕ} (hn : 1 ≤ n) :
    divList n = n.divisors.sort (· ≤ ·) := by
  apply list_eq_of_perm_of_pairwise_le
  · rw [List.perm_ext_iff_of_nodup (divList_sorted n).nodup (Finset.sort_nodup _ _)]
    intro d
    rw [mem_divList hn, Finset.mem_sort, Nat.mem_divisors]
    exact ⟨fun h => ⟨h, by omega⟩, fun h => h.1⟩
  · exact (divList_sorted n).imp le_of_lt
  · exact Finset.pairwise_sort _ _

lemma consecProdSum_nil : consecProdSum [] = 0 := rfl
lemma consecProdSum_singleton (x : ℕ) : consecProdSum [x] = 0 := rfl
lemma consecProdSum_cons_cons (x y : ℕ) (L : List ℕ) :
    consecProdSum (x :: y :: L) = x * y + consecProdSum (y :: L) := rfl

lemma recipConsec_nil : recipConsec [] = 0 := rfl
lemma recipConsec_singleton (x : ℕ) : recipConsec [x] = 0 := rfl
lemma recipConsec_cons_cons (x y : ℕ) (L : List ℕ) :
    recipConsec (x :: y :: L) = (1 : ℚ) / ((x : ℚ) * (y : ℚ)) + recipConsec (y :: L) := rfl

lemma consecProdSum_reverse (L : List ℕ) : consecProdSum L.reverse = consecProdSum L := by
  induction L with
  | nil => simp [consecProdSum_nil]
  | cons x xs ih =>
    cases xs with
    | nil => simp [consecProdSum_singleton]
    | cons y ys =>
      have h_app : ∀ (A : List ℕ) (u v : ℕ),
          consecProdSum (A ++ [u, v]) = consecProdSum (A ++ [u]) + u * v := by
        intro A u v
        induction A with
        | nil => simp [consecProdSum_cons_cons, consecProdSum_singleton]
        | cons a as iha =>
          cases as with
          | nil => simp [consecProdSum_cons_cons, consecProdSum_singleton]
          | cons b bs =>
            change a * b + consecProdSum ((b :: bs) ++ [u, v]) =
              a * b + consecProdSum ((b :: bs) ++ [u]) + u * v
            rw [iha]; ring
      rw [consecProdSum_cons_cons, ← ih]
      have hrev : (x :: y :: ys).reverse = ys.reverse ++ [y, x] := by simp [List.reverse_cons]
      have hrev2 : (y :: ys).reverse = ys.reverse ++ [y] := by simp [List.reverse_cons]
      rw [hrev, h_app, ← hrev2]
      ring

lemma divList_reverse_eq_map_div {n : ℕ} (hn : 1 ≤ n) :
    (divList n).reverse = (divList n).map (fun d => n / d) := by
  apply list_eq_of_perm_of_pairwise_ge
  · have hnodup1 : (divList n).reverse.Nodup := List.nodup_reverse.mpr (divList_sorted n).nodup
    have hnodup2 : ((divList n).map (fun d => n / d)).Nodup := by
      rw [List.nodup_map_iff_inj_on (divList_sorted n).nodup]
      intro d1 hd1 d2 hd2 hdiv
      rw [mem_divList hn] at hd1 hd2
      have h1 : d1 * (n / d1) = n := Nat.mul_div_cancel' hd1
      have h2 : d2 * (n / d2) = n := Nat.mul_div_cancel' hd2
      have hqpos : 0 < n / d1 :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hd1) (Nat.pos_of_dvd_of_pos hd1 (by omega))
      rw [hdiv] at h1
      exact Nat.eq_of_mul_eq_mul_right (by omega) (h1.trans h2.symm)
    rw [List.perm_ext_iff_of_nodup hnodup1 hnodup2]
    intro d
    simp only [List.mem_reverse, List.mem_map, mem_divList hn]
    constructor
    · intro hd
      refine ⟨n / d, Nat.div_dvd_of_dvd hd, ?_⟩
      exact Nat.div_div_self hd (by omega)
    · rintro ⟨e, he, rfl⟩
      exact Nat.div_dvd_of_dvd he
  · rw [List.pairwise_reverse]
    exact (divList_sorted n).imp le_of_lt
  · rw [List.pairwise_map]
    refine (divList_sorted n).imp_of_mem fun {a b} ha hb hab => ?_
    exact Nat.div_le_div_left (le_of_lt hab) (divList_pos hn ha)

lemma consecProdSum_eq_sq_mul_recipConsec {n : ℕ} (hn : 1 ≤ n) :
    (consecProdSum (divList n) : ℚ) = (n : ℚ) ^ 2 * recipConsec (divList n) := by
  have hrev := divList_reverse_eq_map_div hn
  have h1 : (consecProdSum (divList n) : ℚ) = (consecProdSum ((divList n).map (fun d => n / d)) : ℚ) := by
    rw [← hrev, consecProdSum_reverse]
  rw [h1]
  have hgen : ∀ L : List ℕ, (∀ d ∈ L, d ∣ n) →
      (consecProdSum (L.map (fun d => n / d)) : ℚ) = (n : ℚ) ^ 2 * recipConsec L := by
    intro L hL
    induction L with
    | nil => simp [consecProdSum_nil, recipConsec_nil]
    | cons x xs ih =>
      cases xs with
      | nil => simp [consecProdSum_singleton, recipConsec_singleton]
      | cons y ys =>
        have hih := ih (fun d hd => hL d (List.mem_cons_of_mem x hd))
        simp only [List.map_cons, consecProdSum_cons_cons, recipConsec_cons_cons, Nat.cast_add,
          Nat.cast_mul, mul_add] at hih ⊢
        rw [hih]
        congr 1
        have hx : x ∣ n := hL x List.mem_cons_self
        have hy : y ∣ n := hL y (List.mem_cons_of_mem _ List.mem_cons_self)
        have hx0 : (x : ℚ) ≠ 0 := by
          have := Nat.pos_of_dvd_of_pos hx (by omega); positivity
        have hy0 : (y : ℚ) ≠ 0 := by
          have := Nat.pos_of_dvd_of_pos hy (by omega); positivity
        have hnx : ((n / x : ℕ) : ℚ) * (x : ℚ) = (n : ℚ) := by
          exact_mod_cast Nat.div_mul_cancel hx
        have hny : ((n / y : ℕ) : ℚ) * (y : ℚ) = (n : ℚ) := by
          exact_mod_cast Nat.div_mul_cancel hy
        calc ((n / x : ℕ) : ℚ) * ((n / y : ℕ) : ℚ)
            = (((n / x : ℕ) : ℚ) * (x : ℚ)) * (((n / y : ℕ) : ℚ) * (y : ℚ)) *
                ((1 : ℚ) / ((x : ℚ) * (y : ℚ))) := by
              field_simp [hx0, hy0]
          _ = (n : ℚ) ^ 2 * ((1 : ℚ) / ((x : ℚ) * (y : ℚ))) := by
              rw [hnx, hny]; ring
  exact hgen (divList n) (fun d hd => (mem_divList hn).mp hd)

lemma consecProdSum_pos {n : ℕ} (hn : 2 ≤ n) : 0 < consecProdSum (divList n) := by
  have h1 : 1 ∈ divList n := (mem_divList (by omega)).mpr (one_dvd n)
  have h2 : n ∈ divList n := (mem_divList (by omega)).mpr (dvd_refl n)
  cases hL : divList n with
  | nil => rw [hL] at h1; cases h1
  | cons x xs =>
    cases xs with
    | nil =>
      rw [hL] at h1 h2
      simp at h1 h2
      omega
    | cons y ys =>
      rw [consecProdSum_cons_cons]
      have hx : 0 < x := divList_pos (n := n) (by omega) (by rw [hL]; exact List.mem_cons_self)
      have hy : 0 < y :=
        divList_pos (n := n) (by omega) (by rw [hL]; exact List.mem_cons_of_mem x List.mem_cons_self)
      have : 0 < x * y := Nat.mul_pos hx hy
      omega

lemma recipConsec_bounds_of_a_eq_8 {n : ℕ} (hn : 2 ≤ n) (ha : a n = 8) :
    (1 : ℚ) / 9 < recipConsec (divList n) ∧ recipConsec (divList n) ≤ 1 / 8 := by
  have hs_pos : 0 < consecProdSum (divList n) := consecProdSum_pos hn
  rw [a_eq, ite_eq_right_iff.mpr (fun h => absurd h hs_pos.ne')] at ha
  have hle : 8 * consecProdSum (divList n) ≤ n ^ 2 := by
    have := Nat.div_mul_le_self (n ^ 2) (consecProdSum (divList n))
    rw [ha] at this; linarith
  have hlt : n ^ 2 < 9 * consecProdSum (divList n) := by
    have := Nat.lt_div_mul_add hs_pos (a := n ^ 2)
    rw [ha] at this; linarith
  have hsq : (consecProdSum (divList n) : ℚ) = (n : ℚ) ^ 2 * recipConsec (divList n) :=
    consecProdSum_eq_sq_mul_recipConsec (by omega)
  have hn2 : (0 : ℚ) < (n : ℚ) ^ 2 := by positivity
  have hleQ : (8 : ℚ) * ((n : ℚ) ^ 2 * recipConsec (divList n)) ≤ (n : ℚ) ^ 2 := by
    rw [← hsq]; exact_mod_cast hle
  have hltQ : (n : ℚ) ^ 2 < (9 : ℚ) * ((n : ℚ) ^ 2 * recipConsec (divList n)) := by
    rw [← hsq]; exact_mod_cast hlt
  constructor <;> nlinarith

/-! ### Part 2: Monotonicity and Dominance Lemmas for `recipConsec` -/

private lemma insert_increases (a y b : ℕ) (ha : 0 < a) (hay : a < y) (hyb : y < b) :
    (1 : ℚ) / ((a : ℚ) * (b : ℚ)) ≤
      (1 : ℚ) / ((a : ℚ) * (y : ℚ)) + (1 : ℚ) / ((y : ℚ) * (b : ℚ)) := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hyQ : (0 : ℚ) < y := by exact_mod_cast (by omega : 0 < y)
  have hbQ : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  have hybQ : (y : ℚ) < b := by exact_mod_cast hyb
  rw [← sub_nonneg]
  have heq : (1 : ℚ) / (a * y) + 1 / (y * b) - 1 / (a * b) = (b + a - y) / (a * y * b) := by
    field_simp
  rw [heq]
  apply div_nonneg <;> linarith [mul_pos (mul_pos haQ hyQ) hbQ]

lemma recipConsec_le_insert (L : List ℕ) (y : ℕ)
    (hL : L.Pairwise (· < ·)) (hpos : ∀ d ∈ L, 0 < d) (hy : 0 < y)
    (L' : List ℕ) (hL' : L'.Pairwise (· < ·))
    (hperm : L'.Perm (y :: L)) :
    recipConsec L ≤ recipConsec L' := by
  induction L generalizing L' with
  | nil =>
    have : L' = [y] := List.Perm.eq_singleton hperm
    subst this; simp [recipConsec_nil, recipConsec_singleton]
  | cons a as ih =>
    have hmem_a : a ∈ L' := hperm.symm.subset (List.mem_cons_of_mem y List.mem_cons_self)
    have hmem_y : y ∈ L' := hperm.symm.subset List.mem_cons_self
    cases L' with
    | nil => cases hmem_y
    | cons z zs =>
      have hz_in : z ∈ y :: a :: as := hperm.subset List.mem_cons_self
      have hz_le : ∀ w ∈ zs, z < w := (List.pairwise_cons.mp hL').1
      have hzs_sort : zs.Pairwise (· < ·) := (List.pairwise_cons.mp hL').2
      by_cases hzy : z = y
      · subst hzy
        have hzs_perm : zs.Perm (a :: as) := List.Perm.cons_inv hperm
        have hzs_eq : zs = a :: as :=
          list_eq_of_perm_of_pairwise_le hzs_perm (hzs_sort.imp le_of_lt) (hL.imp le_of_lt)
        rw [hzs_eq, recipConsec_cons_cons]
        have : (0 : ℚ) ≤ 1 / ((z : ℚ) * (a : ℚ)) := by positivity
        linarith
      · have hza : z = a := by
          rcases List.mem_cons.mp hz_in with rfl | hza'
          · exact absurd rfl hzy
          · rcases List.mem_cons.mp hza' with rfl | hzas
            · rfl
            · have ha_lt_z : a < z := (List.pairwise_cons.mp hL).1 z hzas
              have hz_lt_a : z < a := hz_le a (by
                rcases List.mem_cons.mp hmem_a with rfl | h
                · omega
                · exact h)
              omega
        subst hza
        have hzs_perm : zs.Perm (y :: as) :=
          List.Perm.cons_inv (hperm.trans (List.Perm.swap z y as))
        cases as with
        | nil =>
          have hzs_eq : zs = [y] := List.Perm.eq_singleton hzs_perm
          rw [hzs_eq, recipConsec_singleton, recipConsec_cons_cons, recipConsec_singleton]
          positivity
        | cons b bs =>
          cases zs with
          | nil =>
            have : y ∈ ([] : List ℕ) := hzs_perm.symm.subset List.mem_cons_self
            cases this
          | cons w ws =>
            by_cases hwy : w = y
            · subst hwy
              have hws_perm : ws.Perm (b :: bs) := List.Perm.cons_inv hzs_perm
              have hws_eq : ws = b :: bs :=
                list_eq_of_perm_of_pairwise_le hws_perm
                  ((List.pairwise_cons.mp hzs_sort).2.imp le_of_lt)
                  ((List.pairwise_cons.mp hL).2.imp le_of_lt)
              rw [hws_eq, recipConsec_cons_cons, recipConsec_cons_cons, recipConsec_cons_cons]
              have hz_pos : 0 < z := hpos z List.mem_cons_self
              have hzw : z < w := hz_le w List.mem_cons_self
              have hwb : w < b :=
                (List.pairwise_cons.mp hzs_sort).1 b (by rw [hws_eq]; exact List.mem_cons_self)
              have hinc := insert_increases z w b hz_pos hzw hwb
              linarith
            · have hwb : w = b := by
                have hw_in : w ∈ y :: b :: bs := hzs_perm.subset List.mem_cons_self
                rcases List.mem_cons.mp hw_in with rfl | hw'
                · exact absurd rfl hwy
                · rcases List.mem_cons.mp hw' with rfl | hwbs
                  · rfl
                  · have hb_lt_w : b < w :=
                      (List.pairwise_cons.mp (List.pairwise_cons.mp hL).2).1 w hwbs
                    have hb_in_zs : b ∈ w :: ws :=
                      hzs_perm.symm.subset (List.mem_cons_of_mem y List.mem_cons_self)
                    rcases List.mem_cons.mp hb_in_zs with rfl | hb_ws
                    · omega
                    · have hw_lt_b : w < b := (List.pairwise_cons.mp hzs_sort).1 b hb_ws
                      omega
              subst hwb
              rw [recipConsec_cons_cons, recipConsec_cons_cons]
              have hrec := ih (List.pairwise_cons.mp hL).2
                (fun d hd => hpos d (List.mem_cons_of_mem _ hd))
                (w :: ws) hzs_sort hzs_perm
              linarith

lemma recipConsec_mono_subset (S₁ S₂ : Finset ℕ) (hsub : S₁ ⊆ S₂) (hpos : ∀ d ∈ S₂, 0 < d) :
    recipConsec (S₁.sort (· ≤ ·)) ≤ recipConsec (S₂.sort (· ≤ ·)) := by
  induction hcard : (S₂ \ S₁).card generalizing S₁ with
  | zero =>
    have heq : S₁ = S₂ :=
      Finset.Subset.antisymm hsub (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hcard))
    subst heq; exact le_rfl
  | succ k ih =>
    have hne : (S₂ \ S₁).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨y, hy⟩ := hne
    rw [Finset.mem_sdiff] at hy
    have hstep : recipConsec (S₁.sort (· ≤ ·)) ≤ recipConsec ((insert y S₁).sort (· ≤ ·)) := by
      refine recipConsec_le_insert (S₁.sort (· ≤ ·)) y (finset_sort_pairwise_lt S₁)
        (fun d hd => hpos d (hsub ((Finset.mem_sort _).mp hd))) (hpos y hy.1)
        ((insert y S₁).sort (· ≤ ·)) (finset_sort_pairwise_lt _) ?_
      rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
        (List.nodup_cons.mpr ⟨by simp [hy.2], Finset.sort_nodup _ _⟩)]
      intro d
      simp [Finset.mem_sort]
    have hsub' : insert y S₁ ⊆ S₂ := Finset.insert_subset hy.1 hsub
    have hcard' : (S₂ \ insert y S₁).card = k := by
      have h1 : S₂ \ insert y S₁ = (S₂ \ S₁).erase y := by
        ext z; simp [and_left_comm]
      rw [h1, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr hy), hcard]
      omega
    exact le_trans hstep (ih (insert y S₁) hsub' hcard')

/-- Pointwise dominance on sorted lists of equal length. -/
lemma recipConsec_le_of_getElem_le (L₁ L₂ : List ℕ)
    (hlen : L₁.length = L₂.length) (hpos2 : ∀ d ∈ L₂, 0 < d)
    (hle : ∀ i (h1 : i < L₁.length) (h2 : i < L₂.length), L₂[i]'h2 ≤ L₁[i]'h1) :
    recipConsec L₁ ≤ recipConsec L₂ := by
  induction L₁ generalizing L₂ with
  | nil =>
    cases L₂ with
    | nil => exact le_rfl
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases L₂ with
    | nil => simp at hlen
    | cons b bs =>
      cases as with
      | nil =>
        cases bs with
        | nil => simp [recipConsec_singleton]
        | cons _ _ => simp at hlen
      | cons a' as' =>
        cases bs with
        | nil => simp at hlen
        | cons b' bs' =>
          rw [recipConsec_cons_cons, recipConsec_cons_cons]
          have h0 : b ≤ a := hle 0 (by simp) (by simp)
          have h1 : b' ≤ a' := hle 1 (by simp) (by simp)
          have hb : (0 : ℚ) < b := by exact_mod_cast hpos2 b List.mem_cons_self
          have hb' : (0 : ℚ) < b' := by
            exact_mod_cast hpos2 b' (List.mem_cons_of_mem _ List.mem_cons_self)
          have hterm : (1 : ℚ) / ((a : ℚ) * (a' : ℚ)) ≤ (1 : ℚ) / ((b : ℚ) * (b' : ℚ)) := by
            apply one_div_le_one_div_of_le (mul_pos hb hb')
            exact mul_le_mul (by exact_mod_cast h0) (by exact_mod_cast h1) (by positivity) (by positivity)
          have hlen' : (a' :: as').length = (b' :: bs').length := by
            simp only [List.length_cons] at hlen ⊢; omega
          have htail : recipConsec (a' :: as') ≤ recipConsec (b' :: bs') := by
            refine ih (b' :: bs') hlen'
              (fun d hd => hpos2 d (List.mem_cons_of_mem _ hd)) ?_
            intro i hi1 hi2
            exact hle (i + 1) (by simp only [List.length_cons] at hi1 ⊢; omega)
              (by simp only [List.length_cons] at hi2 ⊢; omega)
          linarith

/-- If `Φ` is injective on `S` and `Φ d ≤ d` for all `d ∈ S`, then `recipConsec (sort S) ≤ recipConsec (sort (S.image Φ))`. -/
lemma recipConsec_le_image (S : Finset ℕ) (Φ : ℕ → ℕ)
    (hinj : Set.InjOn Φ (S : Set ℕ)) (hle : ∀ d ∈ S, Φ d ≤ d)
    (hpos : ∀ d ∈ S, 0 < Φ d) :
    recipConsec (S.sort (· ≤ ·)) ≤ recipConsec ((S.image Φ).sort (· ≤ ·)) := by
  set L₁ := S.sort (· ≤ ·)
  set L₂ := (S.image Φ).sort (· ≤ ·)
  have hlen : L₁.length = L₂.length := by
    simp only [L₁, L₂, Finset.length_sort]
    exact (Finset.card_image_of_injOn hinj).symm
  refine recipConsec_le_of_getElem_le L₁ L₂ hlen ?_ ?_
  · intro d hd
    have hmem : d ∈ S.image Φ := (Finset.mem_sort _).mp hd
    rcases Finset.mem_image.mp hmem with ⟨x, hx, rfl⟩
    exact hpos x hx
  · intro i h1 h2
    by_contra hlt
    push Not at hlt
    let idxSet : Finset ℕ := Finset.range (i + 1)
    let T : Finset ℕ := idxSet.attach.image fun j => L₁[j.1]'(by have := Finset.mem_range.mp j.2; omega)
    have hT_sub : T ⊆ S := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
      exact (Finset.mem_sort _).mp (List.getElem_mem _)
    have hT_card : T.card = i + 1 := by
      rw [Finset.card_image_of_injective]
      · simp [idxSet]
      · intro j1 j2 heq
        have hnodup := (finset_sort_pairwise_lt S).nodup
        have := (List.Nodup.getElem_inj_iff hnodup).mp heq
        exact Subtype.ext this
    have himg_card : (T.image Φ).card = i + 1 := by
      rw [Finset.card_image_of_injOn (hinj.mono (by exact_mod_cast hT_sub)), hT_card]
    let U : Finset ℕ := (Finset.range i).attach.image fun j => L₂[j.1]'(by have := Finset.mem_range.mp j.2; omega)
    have hU_card : U.card ≤ i := by
      calc U.card ≤ (Finset.range i).attach.card := Finset.card_image_le
        _ = i := by simp
    have hL2_sort : L₂.Pairwise (· < ·) := finset_sort_pairwise_lt (S.image Φ)
    have hsub_U : T.image Φ ⊆ U := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
      have hj_le : j.1 ≤ i := by have := Finset.mem_range.mp j.2; omega
      have hx_le : L₁[j.1]'(by omega) ≤ L₁[i]'h1 := by
        rcases eq_or_lt_of_le hj_le with heq | hlt_j
        · simp [heq]
        · exact le_of_lt (List.pairwise_iff_getElem.mp (finset_sort_pairwise_lt S) j.1 i _ h1 hlt_j)
      have hΦx_lt : Φ (L₁[j.1]'(by omega)) < L₂[i]'h2 :=
        lt_of_le_of_lt (le_trans (hle _ (hT_sub (Finset.mem_image.mpr ⟨j, Finset.mem_attach _ _, rfl⟩))) hx_le) hlt
      have hΦx_mem : Φ (L₁[j.1]'(by omega)) ∈ L₂ := by
        rw [Finset.mem_sort]
        exact Finset.mem_image_of_mem Φ (hT_sub (Finset.mem_image.mpr ⟨j, Finset.mem_attach _ _, rfl⟩))
      obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hΦx_mem
      have hki : k < i := by
        by_contra hkge
        push Not at hkge
        rcases eq_or_lt_of_le hkge with rfl | hik
        · omega
        · have hlt2 := List.pairwise_iff_getElem.mp hL2_sort i k h2 hk hik
          omega
      exact Finset.mem_image.mpr ⟨⟨k, Finset.mem_range.mpr hki⟩, Finset.mem_attach _ _, hkeq⟩
    have := Finset.card_le_card hsub_U
    omega

/-! ### Part 3: Smooth Number Set `S7`, Head/Tail Split, and Finite Euler Product Bound -/

private def Q7 : Finset ℕ := {11, 13, 17, 19, 23, 29, 31}

private def Q7List : List ℕ := [11, 13, 17, 19, 23, 29, 31]

private def S7 (n : ℕ) : Prop :=
  0 < n ∧ ∀ p ∈ n.primeFactors, p ∈ Q7

private def S7_500 : List ℕ :=
  [1, 11, 13, 17, 19, 23, 29, 31, 121, 143, 169, 187, 209, 221, 247, 253,
   289, 299, 319, 323, 341, 361, 377, 391, 403, 437, 493]

private lemma S7_500_sorted : S7_500.Pairwise (· < ·) := by decide

private def stripPrime (p : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | fuel + 1, n => if n % p = 0 then stripPrime p fuel (n / p) else n

private def isS7Bool (n : ℕ) : Bool :=
  if n = 0 then false
  else
    let n := stripPrime 11 4 n
    let n := stripPrime 13 4 n
    let n := stripPrime 17 4 n
    let n := stripPrime 19 4 n
    let n := stripPrime 23 4 n
    let n := stripPrime 29 4 n
    let n := stripPrime 31 4 n
    n == 1

private lemma stripPrime_dvd (p fuel n : ℕ) : stripPrime p fuel n ∣ n := by
  induction fuel generalizing n with
  | zero => exact dvd_refl n
  | succ f ih =>
    unfold stripPrime
    split_ifs with h
    · exact dvd_trans (ih (n / p)) (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h))
    · exact dvd_refl n

private lemma primeFactors_stripPrime_subset {p fuel n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hfuel : n < p ^ fuel) :
    (stripPrime p fuel n).primeFactors ⊆ n.primeFactors.erase p := by
  induction fuel generalizing n with
  | zero => simp at hfuel; omega
  | succ f ih =>
    unfold stripPrime
    split_ifs with h
    · have hpdvd : p ∣ n := Nat.dvd_of_mod_eq_zero h
      have hdiv_pos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpdvd) hp.pos
      have hdiv_lt : n / p < p ^ f := by
        rw [Nat.div_lt_iff_lt_mul hp.pos]; rwa [pow_succ] at hfuel
      exact subset_trans (ih hdiv_pos hdiv_lt)
        (Finset.erase_subset_erase p (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hpdvd) hn.ne'))
    · intro q hq
      refine Finset.mem_erase.mpr ⟨?_, hq⟩
      rintro rfl
      exact h (Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_primeFactors hq))

private lemma isS7Bool_true_of_S7 {d : ℕ} (hd : S7 d) (hle : d ≤ 500) : isS7Bool d = true := by
  have ⟨hpos, hpf⟩ := hd
  unfold isS7Bool
  rw [ite_eq_right_iff.mpr (fun h => absurd h hpos.ne')]
  have hlt : ∀ p ∈ Q7, ∀ m ≤ 500, m < p ^ 4 := by
    intro p hp m hm
    have hp11 : 11 ≤ p := (by decide : ∀ x ∈ Q7, 11 ≤ x) p hp
    have : 500 < 11 ^ 4 := by norm_num
    have : 11 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hp11 4
    omega
  have step : ∀ (p m : ℕ) (S : Finset ℕ), p.Prime → p ∈ Q7 → 0 < m → m ≤ 500 →
      m.primeFactors ⊆ insert p S →
      0 < stripPrime p 4 m ∧ stripPrime p 4 m ≤ 500 ∧ (stripPrime p 4 m).primeFactors ⊆ S := by
    intro p m S hp hpQ hm hm500 hsub
    have hdvd := stripPrime_dvd p 4 m
    have hpos' : 0 < stripPrime p 4 m := Nat.pos_of_dvd_of_pos hdvd hm
    have hle' : stripPrime p 4 m ≤ 500 := le_trans (Nat.le_of_dvd hm hdvd) hm500
    have hpf' : (stripPrime p 4 m).primeFactors ⊆ S := by
      have := primeFactors_stripPrime_subset hp hm (hlt p hpQ m hm500)
      intro q hq
      have h1 := Finset.mem_erase.mp (this hq)
      have h2 := Finset.mem_insert.mp (hsub h1.2)
      exact h2.resolve_left h1.1
    exact ⟨hpos', hle', hpf'⟩
  have h1 := step 11 d {13, 17, 19, 23, 29, 31} (by decide) (by decide) hpos hle hpf
  have h2 := step 13 _ {17, 19, 23, 29, 31} (by decide) (by decide) h1.1 h1.2.1 h1.2.2
  have h3 := step 17 _ {19, 23, 29, 31} (by decide) (by decide) h2.1 h2.2.1 h2.2.2
  have h4 := step 19 _ {23, 29, 31} (by decide) (by decide) h3.1 h3.2.1 h3.2.2
  have h5 := step 23 _ {29, 31} (by decide) (by decide) h4.1 h4.2.1 h4.2.2
  have h6 := step 29 _ {31} (by decide) (by decide) h5.1 h5.2.1 h5.2.2
  have h7 := step 31 _ ∅ (by decide) (by decide) h6.1 h6.2.1 h6.2.2
  have heq1 : stripPrime 31 4 (stripPrime 29 4 (stripPrime 23 4 (stripPrime 19 4 (stripPrime 17 4 (stripPrime 13 4 (stripPrime 11 4 d)))))) = 1 := by
    have h0 : (stripPrime 31 4 (stripPrime 29 4 (stripPrime 23 4 (stripPrime 19 4 (stripPrime 17 4 (stripPrime 13 4 (stripPrime 11 4 d))))))).primeFactors = ∅ :=
      Finset.subset_empty.mp h7.2.2
    rw [← prod_primeFactors_pow_eq_self h7.1.ne', h0]
    simp
  simp [heq1]

private lemma S7_500_bool_1 : ∀ d ∈ List.range' 1 100, isS7Bool d = true → d ∈ S7_500 := by decide
private lemma S7_500_bool_2 : ∀ d ∈ List.range' 101 100, isS7Bool d = true → d ∈ S7_500 := by decide
private lemma S7_500_bool_3 : ∀ d ∈ List.range' 201 100, isS7Bool d = true → d ∈ S7_500 := by decide
private lemma S7_500_bool_4 : ∀ d ∈ List.range' 301 100, isS7Bool d = true → d ∈ S7_500 := by decide
private lemma S7_500_bool_5 : ∀ d ∈ List.range' 401 100, isS7Bool d = true → d ∈ S7_500 := by decide

private lemma mem_S7_500_of_S7 {d : ℕ} (hd : S7 d) (hle : d ≤ 500) : d ∈ S7_500 := by
  have hb := isS7Bool_true_of_S7 hd hle
  have hpos := hd.1
  by_cases h1 : d ≤ 100
  · exact S7_500_bool_1 d (List.mem_range'.mpr ⟨d - 1, by omega, by omega⟩) hb
  · by_cases h2 : d ≤ 200
    · exact S7_500_bool_2 d (List.mem_range'.mpr ⟨d - 101, by omega, by omega⟩) hb
    · by_cases h3 : d ≤ 300
      · exact S7_500_bool_3 d (List.mem_range'.mpr ⟨d - 201, by omega, by omega⟩) hb
      · by_cases h4 : d ≤ 400
        · exact S7_500_bool_4 d (List.mem_range'.mpr ⟨d - 301, by omega, by omega⟩) hb
        · exact S7_500_bool_5 d (List.mem_range'.mpr ⟨d - 401, by omega, by omega⟩) hb

private lemma S7_of_mem_S7_500 {d : ℕ} (hd : d ∈ S7_500) : S7 d := by
  have hpos : 0 < d := (by decide : ∀ x ∈ S7_500, 0 < x) d hd
  have hdvd : d ∣ (11 * 13 * 17 * 19 * 23 * 29 * 31) ^ 2 :=
    (by decide : ∀ x ∈ S7_500, x ∣ (11 * 13 * 17 * 19 * 23 * 29 * 31) ^ 2) d hd
  refine ⟨hpos, fun p hp => ?_⟩
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd_sq : p ∣ (11 * 13 * 17 * 19 * 23 * 29 * 31) ^ 2 :=
    dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdvd
  have hp_dvd : p ∣ 11 * 13 * 17 * 19 * 23 * 29 * 31 := hpp.dvd_of_dvd_pow hp_dvd_sq
  have hmem : ∀ {a b : ℕ}, p ∣ a * b → p ∣ a ∨ p ∣ b := fun h => hpp.dvd_mul.mp h
  have hprim : ∀ {q : ℕ}, q.Prime → p ∣ q → p = q := fun hq h => (Nat.prime_dvd_prime_iff_eq hpp hq).mp h
  rcases hmem hp_dvd with h | h
  · rcases hmem h with h | h
    · rcases hmem h with h | h
      · rcases hmem h with h | h
        · rcases hmem h with h | h
          · rcases hmem h with h | h
            · rw [hprim (by decide) h]; decide
            · rw [hprim (by decide) h]; decide
          · rw [hprim (by decide) h]; decide
        · rw [hprim (by decide) h]; decide
      · rw [hprim (by decide) h]; decide
    · rw [hprim (by decide) h]; decide
  · rw [hprim (by decide) h]; decide

/-- For a strictly increasing positive list `L`, `recipConsec L ≤ ∑ d ∈ L, 1/d^2`. -/
private lemma recipConsec_le_sum_inv_sq (L : List ℕ)
    (hsort : L.Pairwise (· < ·)) (hpos : ∀ d ∈ L, 0 < d) :
    recipConsec L ≤ (L.map (fun (d : ℕ) => (1 : ℚ) / (d : ℚ) ^ 2)).sum := by
  induction L with
  | nil => simp [recipConsec_nil]
  | cons x xs ih =>
    cases xs with
    | nil =>
      rw [recipConsec_singleton, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      positivity
    | cons y ys =>
      rw [recipConsec_cons_cons, List.map_cons, List.sum_cons]
      have hx : (0 : ℚ) < x := by exact_mod_cast hpos x List.mem_cons_self
      have hxy : (x : ℚ) < y := by exact_mod_cast (List.pairwise_cons.mp hsort).1 y List.mem_cons_self
      have hterm : (1 : ℚ) / ((x : ℚ) * (y : ℚ)) ≤ (1 : ℚ) / (x : ℚ) ^ 2 := by
        rw [sq]
        exact one_div_le_one_div_of_le (mul_pos hx hx) (mul_le_mul_of_nonneg_left (le_of_lt hxy) hx.le)
      have hrec := ih (List.pairwise_cons.mp hsort).2 (fun d hd => hpos d (List.mem_cons_of_mem _ hd))
      linarith

/-- Splitting `recipConsec (A ++ B)` at the boundary between `A` and `B`. -/
private lemma recipConsec_append_le (A B : List ℕ) (a_last b_lb : ℕ)
    (hA_ne : A ≠ []) (hlast : A.getLast hA_ne = a_last)
    (ha_pos : 0 < a_last) (hb_pos : 0 < b_lb) (hB_lb : ∀ y ∈ B, b_lb ≤ y) :
    recipConsec (A ++ B) ≤ recipConsec A + (1 : ℚ) / ((a_last : ℚ) * (b_lb : ℚ)) + recipConsec B := by
  induction A with
  | nil => exact absurd rfl hA_ne
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [List.getLast_singleton] at hlast
      subst hlast
      cases B with
      | nil =>
        simp only [List.append_nil, recipConsec_singleton, recipConsec_nil, add_zero, zero_add]
        positivity
      | cons y ys =>
        simp only [List.cons_append, List.nil_append, recipConsec_cons_cons, recipConsec_singleton, zero_add]
        have hy : (b_lb : ℚ) ≤ y := by exact_mod_cast hB_lb y List.mem_cons_self
        have hterm : (1 : ℚ) / ((x : ℚ) * (y : ℚ)) ≤ (1 : ℚ) / ((x : ℚ) * (b_lb : ℚ)) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact mul_le_mul_of_nonneg_left hy (by positivity)
        linarith
    | cons x' xs' =>
      have hne' : x' :: xs' ≠ [] := List.cons_ne_nil _ _
      have hlast' : (x' :: xs').getLast hne' = a_last := by
        simpa [List.getLast_cons hne'] using hlast
      have hrec := ih hne' hlast'
      simp only [List.cons_append, recipConsec_cons_cons] at hrec ⊢
      linarith

/-- Finite geometric series bound in `ℚ`: for `q ≥ 2`, `∑ j ∈ range (E+1), (1/q^2)^j ≤ q^2/(q^2 - 1)`. -/
private lemma geom_sum_inv_sq_le (q E : ℕ) (hq : 2 ≤ q) :
    (∑ j ∈ Finset.range (E + 1), ((1 : ℚ) / (q : ℚ) ^ 2) ^ j) ≤
      ((q : ℚ) ^ 2) / ((q : ℚ) ^ 2 - 1) := by
  set r : ℚ := (1 : ℚ) / (q : ℚ) ^ 2
  have hq2 : (4 : ℚ) ≤ (q : ℚ) ^ 2 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hr_nonneg : 0 ≤ r := by positivity
  have h1mr : 0 < 1 - r := by
    have : r ≤ 1 / 4 := by
      simp only [r]; exact one_div_le_one_div_of_le (by norm_num) hq2
    linarith
  have hgeom : (∑ j ∈ Finset.range (E + 1), r ^ j) * (1 - r) = 1 - r ^ (E + 1) := by
    induction E with
    | zero => simp
    | succ E ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      ring
  have hle1 : ∑ j ∈ Finset.range (E + 1), r ^ j ≤ 1 / (1 - r) := by
    rw [le_div_iff₀ h1mr, hgeom]
    have : 0 ≤ r ^ (E + 1) := pow_nonneg hr_nonneg _
    linarith
  have hr_eq : 1 / (1 - r) = (q : ℚ) ^ 2 / ((q : ℚ) ^ 2 - 1) := by
    simp only [r]
    field_simp [show (q : ℚ) ^ 2 ≠ 0 by linarith, show (q : ℚ) ^ 2 - 1 ≠ 0 by linarith]
  linarith

/-- Finite Euler product bound: for any finite set `U` of `S7`-numbers,
`∑ d ∈ U, 1/d^2 ≤ ∏ q ∈ Q7, q^2 / (q^2 - 1)`. -/
private lemma sum_inv_sq_S7_le (U : Finset ℕ) (hU : ∀ d ∈ U, S7 d) :
    (∑ d ∈ U, (1 : ℚ) / (d : ℚ) ^ 2) ≤ ∏ q ∈ Q7, ((q : ℚ) ^ 2) / ((q : ℚ) ^ 2 - 1) := by
  let E : ℕ := U.sup id
  let eval : (Q7 → Fin (E + 1)) → ℕ := fun e => ∏ q : Q7, (q.1) ^ (e q).1
  have hfac_lt : ∀ d ∈ U, ∀ q : Q7, d.factorization q.1 < E + 1 := by
    intro d hd q
    have hd_le_E : d ≤ E := Finset.le_sup (f := id) hd
    have hfac_le : d.factorization q.1 ≤ d := by
      have hpos := (hU d hd).1
      by_cases hq : q.1 ∈ d.primeFactors
      · have hqp : q.1.Prime := Nat.prime_of_mem_primeFactors hq
        have hpow : q.1 ^ (d.factorization q.1) ≤ d :=
          Nat.le_of_dvd hpos (Nat.ordProj_dvd d q.1)
        have hlin : d.factorization q.1 ≤ 2 ^ (d.factorization q.1) := Nat.lt_two_pow_self.le
        have h2q : 2 ^ (d.factorization q.1) ≤ q.1 ^ (d.factorization q.1) :=
          Nat.pow_le_pow_left hqp.two_le _
        omega
      · have : d.factorization q.1 = 0 := factorization_eq_zero_of_notMem_pf hq
        omega
    omega
  let expVec : ℕ → (Q7 → Fin (E + 1)) := fun d q =>
    if h : d.factorization q.1 < E + 1 then ⟨d.factorization q.1, h⟩ else ⟨0, Nat.succ_pos E⟩
  have heval_exp : ∀ d ∈ U, eval (expVec d) = d := by
    intro d hd
    have ⟨hd_pos, hpf⟩ := hU d hd
    have hval : eval (expVec d) = ∏ q : Q7, q.1 ^ (d.factorization q.1) := by
      refine Finset.prod_congr rfl fun q _ => ?_
      dsimp only [expVec]
      split_ifs with h
      · rfl
      · exact absurd (hfac_lt d hd q) h
    rw [hval]
    have hprod : ∏ q ∈ Q7, q ^ (d.factorization q) = ∏ p ∈ d.primeFactors, p ^ (d.factorization p) := by
      symm
      refine Finset.prod_subset hpf fun p _ hpnot => ?_
      rw [factorization_eq_zero_of_notMem_pf hpnot, pow_zero]
    rw [← Finset.prod_attach Q7 (fun q => q ^ (d.factorization q))] at hprod
    exact hprod.trans (prod_primeFactors_pow_eq_self hd_pos.ne')
  have hexp_inj : Set.InjOn expVec (U : Set ℕ) := by
    intro d1 hd1 d2 hd2 heq
    have := congrArg eval heq
    rwa [heval_exp d1 hd1, heval_exp d2 hd2] at this
  have hterm_eq : ∀ e : Q7 → Fin (E + 1),
      (1 : ℚ) / (eval e : ℚ) ^ 2 = ∏ q : Q7, ((1 : ℚ) / (q.1 : ℚ) ^ 2) ^ (e q).1 := by
    intro e
    dsimp only [eval]
    push_cast
    rw [← Finset.prod_pow, one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [one_div, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  calc ∑ d ∈ U, (1 : ℚ) / (d : ℚ) ^ 2
      = ∑ d ∈ U, (1 : ℚ) / (eval (expVec d) : ℚ) ^ 2 := by
        refine Finset.sum_congr rfl fun d hd => by rw [heval_exp d hd]
    _ = ∑ e ∈ U.image expVec, (1 : ℚ) / (eval e : ℚ) ^ 2 := by
        rw [Finset.sum_image (fun d1 hd1 d2 hd2 h => hexp_inj hd1 hd2 h)]
    _ ≤ ∑ e : Q7 → Fin (E + 1), (1 : ℚ) / (eval e : ℚ) ^ 2 := by
        exact Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
    _ = ∑ e : Q7 → Fin (E + 1), ∏ q : Q7, ((1 : ℚ) / (q.1 : ℚ) ^ 2) ^ (e q).1 := by
        refine Finset.sum_congr rfl fun e _ => hterm_eq e
    _ = ∏ q : Q7, ∑ j : Fin (E + 1), ((1 : ℚ) / (q.1 : ℚ) ^ 2) ^ j.1 := by
        exact (Fintype.prod_sum (fun (q : Q7) (j : Fin (E + 1)) => ((1 : ℚ) / (q.1 : ℚ) ^ 2) ^ j.1)).symm
    _ = ∏ q : Q7, ∑ j ∈ Finset.range (E + 1), ((1 : ℚ) / (q.1 : ℚ) ^ 2) ^ j := by
        refine Finset.prod_congr rfl fun q _ => ?_
        exact Fin.sum_univ_eq_sum_range (fun j => ((1 : ℚ) / (q.1 : ℚ) ^ 2) ^ j) (E + 1)
    _ ≤ ∏ q : Q7, ((q.1 : ℚ) ^ 2) / ((q.1 : ℚ) ^ 2 - 1) := by
        refine finset_prod_le_prod_Q (fun q _ => Finset.sum_nonneg fun _ _ => by positivity) ?_
        intro q _
        have hq2 : 2 ≤ q.1 := by
          have : ∀ x ∈ Q7, 2 ≤ x := by decide
          exact this q.1 q.2
        exact geom_sum_inv_sq_le q.1 E hq2
    _ = ∏ q ∈ Q7, ((q : ℚ) ^ 2) / ((q : ℚ) ^ 2 - 1) := by
        exact Finset.prod_attach Q7 (fun q => ((q : ℚ) ^ 2) / ((q : ℚ) ^ 2 - 1))

private lemma numeric_upper_bound :
    recipConsec S7_500 + (1 : ℚ) / ((493 : ℚ) * 500) +
      ((∏ q ∈ Q7, ((q : ℚ) ^ 2) / ((q : ℚ) ^ 2 - 1)) -
        ∑ d ∈ S7_500.toFinset, (1 : ℚ) / (d : ℚ) ^ 2) < (1 : ℚ) / 9 := by
  have hsum : ∑ d ∈ S7_500.toFinset, (1 : ℚ) / (d : ℚ) ^ 2 =
      (S7_500.map (fun (d : ℕ) => (1 : ℚ) / (d : ℚ) ^ 2)).sum := by
    rw [List.sum_toFinset _ S7_500_sorted.nodup]
  rw [hsum]
  norm_num [recipConsec, S7_500, Q7]

/-- For ANY finite set `S` of `S7`-numbers, `recipConsec (S.sort (· ≤ ·)) < 1 / 9`. -/
private lemma recipConsec_S7_lt_one_ninth (S : Finset ℕ) (hS : ∀ d ∈ S, S7 d) :
    recipConsec (S.sort (· ≤ ·)) < (1 : ℚ) / 9 := by
  let S_tail : Finset ℕ := S.filter (500 < ·)
  let S_big : Finset ℕ := S7_500.toFinset ∪ S_tail
  have hsub : S ⊆ S_big := by
    intro d hd
    by_cases h500 : d ≤ 500
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr (mem_S7_500_of_S7 (hS d hd) h500))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd, by omega⟩)
  have hbig_S7 : ∀ d ∈ S_big, S7 d := by
    intro d hd
    rcases Finset.mem_union.mp hd with h1 | h2
    · exact S7_of_mem_S7_500 (List.mem_toFinset.mp h1)
    · exact hS d (Finset.mem_filter.mp h2).1
  have hmono : recipConsec (S.sort (· ≤ ·)) ≤ recipConsec (S_big.sort (· ≤ ·)) :=
    recipConsec_mono_subset S S_big hsub (fun d hd => (hbig_S7 d hd).1)
  have hdisj : Disjoint S7_500.toFinset S_tail := by
    rw [Finset.disjoint_left]
    intro d h1 h2
    have hle : d ≤ 500 := (by decide : ∀ x ∈ S7_500, x ≤ 500) d (List.mem_toFinset.mp h1)
    have hgt : 500 < d := (Finset.mem_filter.mp h2).2
    omega
  have hbig_eq : S_big.sort (· ≤ ·) = S7_500 ++ S_tail.sort (· ≤ ·) := by
    apply list_eq_of_perm_of_pairwise_le
    · have hnodup_app : (S7_500 ++ S_tail.sort (· ≤ ·)).Nodup := by
        rw [List.nodup_append]
        refine ⟨S7_500_sorted.nodup, Finset.sort_nodup _ _, fun a ha b hb hab => ?_⟩
        subst hab
        exact Finset.disjoint_left.mp hdisj (List.mem_toFinset.mpr ha) ((Finset.mem_sort _).mp hb)
      rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) hnodup_app]
      intro d
      simp [S_big, Finset.mem_sort]
    · exact Finset.pairwise_sort _ _
    · rw [List.pairwise_append]
      refine ⟨S7_500_sorted.imp le_of_lt, Finset.pairwise_sort _ _, fun a ha b hb => ?_⟩
      have hle : a ≤ 500 := (by decide : ∀ x ∈ S7_500, x ≤ 500) a ha
      have hgt : 500 < b := (Finset.mem_filter.mp ((Finset.mem_sort _).mp hb)).2
      omega
  have hne : S7_500 ≠ [] := by decide
  have hlast : S7_500.getLast hne = 493 := by decide +revert
  have hsplit : recipConsec (S7_500 ++ S_tail.sort (· ≤ ·)) ≤
      recipConsec S7_500 + (1 : ℚ) / ((493 : ℚ) * 500) + recipConsec (S_tail.sort (· ≤ ·)) :=
    recipConsec_append_le S7_500 (S_tail.sort (· ≤ ·)) 493 500 hne hlast (by omega) (by omega)
      (fun y hy => le_of_lt (Finset.mem_filter.mp ((Finset.mem_sort _).mp hy)).2)
  have htail_sq : recipConsec (S_tail.sort (· ≤ ·)) ≤ ∑ d ∈ S_tail, (1 : ℚ) / (d : ℚ) ^ 2 := by
    calc recipConsec (S_tail.sort (· ≤ ·))
        ≤ ((S_tail.sort (· ≤ ·)).map (fun (d : ℕ) => (1 : ℚ) / (d : ℚ) ^ 2)).sum :=
          recipConsec_le_sum_inv_sq _ (finset_sort_pairwise_lt S_tail)
            (fun d hd => (hS d (Finset.mem_filter.mp ((Finset.mem_sort _).mp hd)).1).1)
      _ = ∑ d ∈ S_tail, (1 : ℚ) / (d : ℚ) ^ 2 :=
          finset_sum_sort_eq S_tail (fun (d : ℕ) => (1 : ℚ) / (d : ℚ) ^ 2)
  have heuler := sum_inv_sq_S7_le S_big hbig_S7
  rw [Finset.sum_union hdisj] at heuler
  have hnum := numeric_upper_bound
  rw [hbig_eq] at hmono
  linarith

/-! ### Part 4: Lower Bound (`x < X0 → a x ≠ 8`) -/

private def X0 : ℕ := 35336848261

private lemma prime_ge_11_list_bound (ps : List ℕ)
    (hsort : ps.Pairwise (· < ·)) (hprime : ∀ p ∈ ps, p.Prime ∧ 11 ≤ p) :
    ∀ i (hi : i < ps.length) (hi8 : i < 8),
      ([11, 13, 17, 19, 23, 29, 31, 37] : List ℕ)[i]'(by simp; omega) ≤ ps[i]'hi := by
  intro i hi hi8
  have next_prime_ge : ∀ (j : ℕ) (hj : j + 1 < ps.length) (lo hi_p : ℕ),
      lo ≤ ps[j]'(by omega) →
      (∀ m ∈ Finset.Ico (lo + 1) hi_p, ¬ m.Prime) →
      hi_p ≤ ps[j + 1]'hj := by
    intro j hj lo hi_p hlo hcomp
    have hlt : ps[j]'(by omega) < ps[j + 1]'hj :=
      List.pairwise_iff_getElem.mp hsort j (j + 1) (by omega) hj (by omega)
    have h1 : lo + 1 ≤ ps[j + 1]'hj := by omega
    by_contra hlt2
    push Not at hlt2
    have hmem : ps[j + 1]'hj ∈ Finset.Ico (lo + 1) hi_p := Finset.mem_Ico.mpr ⟨h1, hlt2⟩
    exact hcomp _ hmem (hprime _ (List.getElem_mem hj)).1
  have h0 : 11 ≤ ps[0]'(by omega) := (hprime _ (List.getElem_mem (by omega))).2
  interval_cases i
  · exact h0
  · exact next_prime_ge 0 hi 11 13 h0 (by decide)
  · have h1 := next_prime_ge 0 (by omega) 11 13 h0 (by decide)
    exact next_prime_ge 1 hi 13 17 h1 (by decide)
  · have h1 := next_prime_ge 0 (by omega) 11 13 h0 (by decide)
    have h2 := next_prime_ge 1 (by omega) 13 17 h1 (by decide)
    exact next_prime_ge 2 hi 17 19 h2 (by decide)
  · have h1 := next_prime_ge 0 (by omega) 11 13 h0 (by decide)
    have h2 := next_prime_ge 1 (by omega) 13 17 h1 (by decide)
    have h3 := next_prime_ge 2 (by omega) 17 19 h2 (by decide)
    exact next_prime_ge 3 hi 19 23 h3 (by decide)
  · have h1 := next_prime_ge 0 (by omega) 11 13 h0 (by decide)
    have h2 := next_prime_ge 1 (by omega) 13 17 h1 (by decide)
    have h3 := next_prime_ge 2 (by omega) 17 19 h2 (by decide)
    have h4 := next_prime_ge 3 (by omega) 19 23 h3 (by decide)
    exact next_prime_ge 4 hi 23 29 h4 (by decide)
  · have h1 := next_prime_ge 0 (by omega) 11 13 h0 (by decide)
    have h2 := next_prime_ge 1 (by omega) 13 17 h1 (by decide)
    have h3 := next_prime_ge 2 (by omega) 17 19 h2 (by decide)
    have h4 := next_prime_ge 3 (by omega) 19 23 h3 (by decide)
    have h5 := next_prime_ge 4 (by omega) 23 29 h4 (by decide)
    exact next_prime_ge 5 hi 29 31 h5 (by decide)
  · have h1 := next_prime_ge 0 (by omega) 11 13 h0 (by decide)
    have h2 := next_prime_ge 1 (by omega) 13 17 h1 (by decide)
    have h3 := next_prime_ge 2 (by omega) 17 19 h2 (by decide)
    have h4 := next_prime_ge 3 (by omega) 19 23 h3 (by decide)
    have h5 := next_prime_ge 4 (by omega) 23 29 h4 (by decide)
    have h6 := next_prime_ge 5 (by omega) 29 31 h5 (by decide)
    exact next_prime_ge 6 hi 31 37 h6 (by decide)

private lemma a_ne_8_of_lt_X0 {x : ℕ} (hx2 : 2 ≤ x) (hxlt : x < X0) : a x ≠ 8 := by
  intro ha
  have ⟨hgt9, hle8⟩ := recipConsec_bounds_of_a_eq_8 hx2 ha
  by_cases hmin : x.minFac ≤ 7
  · have hmf_dvd : x.minFac ∣ x := Nat.minFac_dvd x
    have hmf_gt1 : 1 < x.minFac := (Nat.minFac_prime (by omega)).one_lt
    have hpair_sub : ({1, x.minFac} : Finset ℕ) ⊆ x.divisors := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rw [Nat.mem_divisors]
      rcases hd with rfl | rfl
      · exact ⟨one_dvd x, by omega⟩
      · exact ⟨hmf_dvd, by omega⟩
    have hmono := recipConsec_mono_subset ({1, x.minFac} : Finset ℕ) x.divisors hpair_sub
      (fun d hd => Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (by omega))
    rw [← divList_eq_sort_divisors (by omega)] at hmono
    have hsort2 : ({1, x.minFac} : Finset ℕ).sort (· ≤ ·) = [1, x.minFac] := by
      apply list_eq_of_perm_of_pairwise_le
      · rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (by simp; omega)]
        intro d; simp [Finset.mem_sort]
      · exact Finset.pairwise_sort _ _
      · simp; omega
    rw [hsort2, recipConsec_cons_cons, recipConsec_singleton, add_zero] at hmono
    have hmfQ : (x.minFac : ℚ) ≤ 7 := by exact_mod_cast hmin
    have hmfpos : (0 : ℚ) < x.minFac := by positivity
    have hge7 : (1 : ℚ) / 7 ≤ 1 / ((1 : ℚ) * (x.minFac : ℚ)) := by
      rw [one_mul]
      exact one_div_le_one_div_of_le hmfpos hmfQ
    linarith
  · push Not at hmin
    have hpf_ge11 : ∀ p ∈ x.primeFactors, p.Prime ∧ 11 ≤ p := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ x := Nat.dvd_of_mem_primeFactors hp
      have hge8 : 8 ≤ p := le_trans (by omega : 8 ≤ x.minFac) (Nat.minFac_le_of_dvd hpp.two_le hpdvd)
      have hnot : p ≠ 8 ∧ p ≠ 9 ∧ p ≠ 10 := by
        refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; exact absurd hpp (by decide))
      exact ⟨hpp, by omega⟩
    let ps := x.primeFactors.sort (· ≤ ·)
    have hps_sort : ps.Pairwise (· < ·) := finset_sort_pairwise_lt _
    have hps_prime : ∀ p ∈ ps, p.Prime ∧ 11 ≤ p := fun p hp => hpf_ge11 p ((Finset.mem_sort _).mp hp)
    have hps_bound := prime_ge_11_list_bound ps hps_sort hps_prime
    have hlen_le7 : ps.length ≤ 7 := by
      by_contra hge8
      push Not at hge8
      have h0 : 11 ≤ ps[0]'(by omega) := hps_bound 0 (by omega) (by omega)
      have h1 : 13 ≤ ps[1]'(by omega) := hps_bound 1 (by omega) (by omega)
      have h2 : 17 ≤ ps[2]'(by omega) := hps_bound 2 (by omega) (by omega)
      have h3 : 19 ≤ ps[3]'(by omega) := hps_bound 3 (by omega) (by omega)
      have h4 : 23 ≤ ps[4]'(by omega) := hps_bound 4 (by omega) (by omega)
      have h5 : 29 ≤ ps[5]'(by omega) := hps_bound 5 (by omega) (by omega)
      have h6 : 31 ≤ ps[6]'(by omega) := hps_bound 6 (by omega) (by omega)
      have h7 : 37 ≤ ps[7]'(by omega) := hps_bound 7 (by omega) (by omega)
      have hprod_ge : X0 ≤ ps.prod := by
        have htake : ps = ps.take 8 ++ ps.drop 8 := (List.take_append_drop 8 ps).symm
        have htake_eq : ps.take 8 = [ps[0], ps[1], ps[2], ps[3], ps[4], ps[5], ps[6], ps[7]] := by
          apply List.ext_getElem (by simp; omega)
          intro i hi1 hi2
          have : i < 8 := by simp at hi1; omega
          interval_cases i <;> simp
        have hdrop_pos : 1 ≤ (ps.drop 8).prod :=
          List.one_le_prod_of_one_le fun p hp => (hps_prime p (List.mem_of_mem_drop hp)).1.one_lt.le
        rw [htake, List.prod_append, htake_eq]
        simp only [List.prod_cons, List.prod_nil, mul_one] at *
        have h8 : X0 ≤ ps[0] * ps[1] * ps[2] * ps[3] * ps[4] * ps[5] * ps[6] * ps[7] := by
          dsimp only [X0]
          calc 35336848261 = 11 * 13 * 17 * 19 * 23 * 29 * 31 * 37 := by norm_num
            _ ≤ ps[0] * ps[1] * ps[2] * ps[3] * ps[4] * ps[5] * ps[6] * ps[7] := by gcongr
        nlinarith
      have hprod_dvd : ps.prod ∣ x := by
        have heq : ps.prod = ∏ p ∈ x.primeFactors, p := by
          simpa using finset_prod_sort_eq x.primeFactors id
        rw [heq]
        exact Nat.prod_primeFactors_dvd x
      have hle_x : ps.prod ≤ x := Nat.le_of_dvd (by omega) hprod_dvd
      omega
    let Φ : ℕ → ℕ := fun d => ∏ i : Fin ps.length, (Q7List[i.1]'(by simp [Q7List]; omega)) ^ (d.factorization (ps[i.1]'i.2))
    have hQ7_prime : ∀ (i : Fin ps.length), (Q7List[i.1]'(by simp [Q7List]; omega)).Prime := by
      intro i
      have : ∀ q ∈ Q7List, q.Prime := by decide
      exact this _ (List.getElem_mem _)
    have hQ7_mem : ∀ (i : Fin ps.length), Q7List[i.1]'(by simp [Q7List]; omega) ∈ Q7 := by
      intro i
      have : ∀ q ∈ Q7List, q ∈ Q7 := by decide
      exact this _ (List.getElem_mem _)
    have hQ7_nodup : Q7List.Nodup := by decide
    have hQ7_le : ∀ (i : Fin ps.length), Q7List[i.1]'(by simp [Q7List]; omega) ≤ ps[i.1]'i.2 := by
      intro i
      have hb := hps_bound i.1 i.2 (by omega)
      have hlt7 : i.1 < 7 := by omega
      have heq : Q7List[i.1]'(by simp [Q7List]; omega) =
          ([11, 13, 17, 19, 23, 29, 31, 37] : List ℕ)[i.1]'(by simp; omega) := by
        rcases i with ⟨idx, hidx⟩
        dsimp only at hlt7 ⊢
        interval_cases idx <;> rfl
      rw [heq]; exact hb
    have hΦ_pos : ∀ d ∈ x.divisors, 0 < Φ d := by
      intro d _
      exact Finset.prod_pos fun i _ => pow_pos (hQ7_prime i).pos _
    have hΦ_S7 : ∀ d ∈ x.divisors, S7 (Φ d) := by
      intro d hd
      refine ⟨hΦ_pos d hd, fun p hp => ?_⟩
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ Φ d := Nat.dvd_of_mem_primeFactors hp
      rcases prime_dvd_finset_prod hpp hpdvd with ⟨i, _, hi⟩
      have hpeq : p = Q7List[i.1]'(by simp [Q7List]; omega) :=
        (Nat.prime_dvd_prime_iff_eq hpp (hQ7_prime i)).mp (hpp.dvd_of_dvd_pow hi)
      rw [hpeq]
      exact hQ7_mem i
    have hΦ_le : ∀ d ∈ x.divisors, Φ d ≤ d := by
      intro d hd
      have hd_dvd : d ∣ x := (Nat.mem_divisors.mp hd).1
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd (by omega)
      have hdpf : d.primeFactors ⊆ x.primeFactors := Nat.primeFactors_mono hd_dvd (by omega)
      have hd_eq : d = ∏ i : Fin ps.length, (ps[i.1]'i.2) ^ (d.factorization (ps[i.1]'i.2)) := by
        have h1 : ∏ p ∈ x.primeFactors, p ^ (d.factorization p) =
            ∏ p ∈ d.primeFactors, p ^ (d.factorization p) := by
          symm
          refine Finset.prod_subset hdpf fun p _ hpnot => ?_
          rw [factorization_eq_zero_of_notMem_pf hpnot, pow_zero]
        have h2 : ∏ p ∈ x.primeFactors, p ^ (d.factorization p) =
            (ps.map fun p => p ^ (d.factorization p)).prod :=
          (finset_prod_sort_eq x.primeFactors (fun p => p ^ (d.factorization p))).symm
        have h3 : (ps.map fun p => p ^ (d.factorization p)).prod =
            ∏ i : Fin ps.length, (ps[i.1]'i.2) ^ (d.factorization (ps[i.1]'i.2)) :=
          list_prod_map_eq_fin_prod ps (fun p => p ^ (d.factorization p))
        rw [← h3, ← h2, h1, prod_primeFactors_pow_eq_self hd_pos.ne']
      conv_rhs => rw [hd_eq]
      exact finset_prod_le_prod_Nat (fun i _ => Nat.pow_le_pow_left (hQ7_le i) _)
    have hΦ_inj : Set.InjOn Φ (x.divisors : Set ℕ) := by
      intro d1 hd1 d2 hd2 heq
      have hfac_eq : ∀ i : Fin ps.length, d1.factorization (ps[i.1]'i.2) = d2.factorization (ps[i.1]'i.2) := by
        intro i
        set q := Q7List[i.1]'(by simp [Q7List]; omega)
        have hqp : q.Prime := hQ7_prime i
        have hval : ∀ d, (Φ d).factorization q = d.factorization (ps[i.1]'i.2) := by
          intro d
          dsimp only [Φ]
          rw [Nat.factorization_prod (fun j _ => pow_ne_zero _ (hQ7_prime j).ne_zero)]
          rw [finsupp_sum_apply_nat]
          rw [Finset.sum_eq_single i]
          · rw [Nat.Prime.factorization_pow hqp, Finsupp.single_eq_same]
          · intro j _ hji
            rw [Nat.Prime.factorization_pow (hQ7_prime j), Finsupp.single_eq_of_ne]
            intro hqeq
            have := (List.Nodup.getElem_inj_iff hQ7_nodup).mp hqeq
            exact hji (Fin.ext this.symm)
          · intro h; exact absurd (Finset.mem_univ i) h
        rw [← hval d1, ← hval d2, heq]
      have hd1_dvd : d1 ∣ x := (Nat.mem_divisors.mp hd1).1
      have hd2_dvd : d2 ∣ x := (Nat.mem_divisors.mp hd2).1
      have hd1_pos : 0 < d1 := Nat.pos_of_dvd_of_pos hd1_dvd (by omega)
      have hd2_pos : 0 < d2 := Nat.pos_of_dvd_of_pos hd2_dvd (by omega)
      rw [← prod_primeFactors_pow_eq_self hd1_pos.ne',
        ← prod_primeFactors_pow_eq_self hd2_pos.ne']
      have h1 : ∏ p ∈ d1.primeFactors, p ^ (d1.factorization p) =
          ∏ p ∈ x.primeFactors, p ^ (d1.factorization p) :=
        Finset.prod_subset (Nat.primeFactors_mono hd1_dvd (by omega)) fun p _ hpnot => by
          rw [factorization_eq_zero_of_notMem_pf hpnot, pow_zero]
      have h2 : ∏ p ∈ d2.primeFactors, p ^ (d2.factorization p) =
          ∏ p ∈ x.primeFactors, p ^ (d2.factorization p) :=
        Finset.prod_subset (Nat.primeFactors_mono hd2_dvd (by omega)) fun p _ hpnot => by
          rw [factorization_eq_zero_of_notMem_pf hpnot, pow_zero]
      rw [h1, h2]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpmem : p ∈ ps := (Finset.mem_sort _).mpr hp
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hpmem
      rw [hfac_eq ⟨idx, hidx⟩]
    have hdom := recipConsec_le_image x.divisors Φ hΦ_inj hΦ_le hΦ_pos
    rw [← divList_eq_sort_divisors (by omega)] at hdom
    have hS7_lt := recipConsec_S7_lt_one_ninth (x.divisors.image Φ) (by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨d, hd, rfl⟩
      exact hΦ_S7 d hd)
    linarith

/-! ### Part 5: Verification for `X0 = 35336848261` and Primorial Identity -/

private def divisorsX0 : List ℕ :=
  [1, 11, 13, 17, 19, 23, 29, 31,
   37, 143, 187, 209, 221, 247, 253, 299,
   319, 323, 341, 377, 391, 403, 407, 437,
   481, 493, 527, 551, 589, 629, 667, 703,
   713, 851, 899, 1073, 1147, 2431, 2717, 3289,
   3553, 4147, 4199, 4301, 4433, 4807, 5083, 5291,
   5423, 5681, 5797, 6061, 6409, 6479, 6851, 6919,
   7163, 7337, 7429, 7657, 7733, 7843, 8177, 8671,
   9139, 9269, 9361, 9367, 9889, 10013, 11063, 11339,
   11687, 11803, 11951, 12121, 12617, 12673, 13547, 13949,
   14467, 14911, 15283, 16169, 17081, 18241, 19499, 20387,
   20677, 21793, 24679, 26381, 33263, 46189, 55913, 62491,
   70499, 75361, 78793, 81719, 84227, 89947, 95381, 96577,
   100529, 101959, 103037, 110143, 121693, 121771, 124729, 128557,
   130169, 131461, 133331, 139403, 147407, 149017, 153439, 155363,
   157573, 159137, 164021, 164749, 168113, 176111, 177859, 187891,
   188071, 198679, 200651, 210197, 214489, 215441, 222053, 224257,
   227447, 230299, 237133, 239723, 253487, 265031, 268801, 271469,
   274873, 283309, 290191, 290377, 320827, 342953, 346579, 351509,
   365893, 370481, 392863, 419543, 432419, 448477, 468901, 501239,
   565471, 631997, 765049, 1062347, 1339481, 1431859, 1621477, 1708993,
   1733303, 1812239, 1937221, 2068781, 2185469, 2312167, 2369851, 2442583,
   2533289, 2608463, 2788357, 2800733, 2915341, 2956811, 2993887, 3023603,
   3116399, 3194147, 3529097, 3573349, 3772483, 3774901, 3812369, 3866599,
   4075291, 4321493, 4505527, 4569617, 4614973, 4756609, 4816253, 4933247,
   5107219, 5157911, 5454059, 5513629, 5830201, 6095713, 6220181, 6516107,
   6678671, 6951967, 7351123, 7971317, 8215961, 8415539, 8521063, 9945637,
   10743949, 13005833, 14535931, 30808063, 32932757, 39306839, 41523911, 49560797,
   50265787, 52978783, 56179409, 59994649, 64132211, 67052843, 71677177, 73465381,
   80862353, 86822723, 87684487, 90375571, 93731693, 103627121, 109402007, 110773819,
   118183439, 139671337, 143064163, 159895241, 169075829, 188967103, 247110827, 955049953,
   1139898331, 1218512009, 1536384707, 1859834119, 2078638133, 2718219097, 3212440751, 35336848261]

set_option maxRecDepth 8192 in
private lemma divisorsX0_sorted : divisorsX0.Pairwise (· < ·) := by decide

set_option maxRecDepth 8192 in
private lemma divisorsX0_eq_divList : divList X0 = divisorsX0 := by
  rw [divList_eq_sort_divisors (by decide : 1 ≤ X0)]
  apply list_eq_of_perm_of_pairwise_le
  · have hX0_ne : X0 ≠ 0 := by decide
    have hX0_eq : X0 = 11 * (13 * (17 * (19 * (23 * (29 * (31 * 37)))))) := by norm_num [X0]
    have hsub : divisorsX0.toFinset ⊆ X0.divisors := by
      intro d hd
      rw [List.mem_toFinset] at hd
      rw [Nat.mem_divisors]
      exact ⟨(by decide : ∀ x ∈ divisorsX0, x ∣ X0) d hd, hX0_ne⟩
    have hcard_mul : ∀ (p m : ℕ), p.Prime → m ≠ 0 → Nat.Coprime p m →
        (p * m).divisors.card = 2 * m.divisors.card := by
      intro p m hp hm hcop
      have hpm : p * m ≠ 0 := mul_ne_zero hp.ne_zero hm
      have heq : (p * m).divisors = m.divisors ∪ m.divisors.image (p * ·) := by
        ext d
        simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
        constructor
        · rintro ⟨hd, _⟩
          by_cases hpd : p ∣ d
          · rcases hpd with ⟨k, rfl⟩
            right
            refine ⟨k, ⟨?_, hm⟩, rfl⟩
            exact (mul_dvd_mul_iff_left hp.ne_zero).mp hd
          · left
            have hcop' : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hpd
            exact ⟨hcop'.symm.dvd_of_dvd_mul_left hd, hm⟩
        · rintro (⟨hd, _⟩ | ⟨k, ⟨hk, _⟩, rfl⟩)
          · exact ⟨dvd_mul_of_dvd_right hd p, hpm⟩
          · exact ⟨mul_dvd_mul_left p hk, hpm⟩
      have hdisj : Disjoint m.divisors (m.divisors.image (p * ·)) := by
        rw [Finset.disjoint_left]
        intro d hd1 hd2
        rcases Finset.mem_image.mp hd2 with ⟨k, _, rfl⟩
        have hp_dvd_m : p ∣ m := dvd_trans (dvd_mul_right p k) (Nat.mem_divisors.mp hd1).1
        exact (hp.coprime_iff_not_dvd.mp hcop) hp_dvd_m
      rw [heq, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (mul_right_injective₀ hp.ne_zero)]
      omega
    have hcard_X0 : X0.divisors.card = 256 := by
      have h1 : (37 : ℕ).divisors.card = 2 := by
        rw [Nat.Prime.divisors (by decide)]; simp
      have h2 := hcard_mul 31 37 (by decide) (by decide) (by decide)
      have h3 := hcard_mul 29 (31 * 37) (by decide) (by decide) (by decide)
      have h4 := hcard_mul 23 (29 * (31 * 37)) (by decide) (by decide) (by decide)
      have h5 := hcard_mul 19 (23 * (29 * (31 * 37))) (by decide) (by decide) (by decide)
      have h6 := hcard_mul 17 (19 * (23 * (29 * (31 * 37)))) (by decide) (by decide) (by decide)
      have h7 := hcard_mul 13 (17 * (19 * (23 * (29 * (31 * 37))))) (by decide) (by decide) (by decide)
      have h8 := hcard_mul 11 (13 * (17 * (19 * (23 * (29 * (31 * 37)))))) (by decide) (by decide) (by decide)
      rw [hX0_eq]; omega
    have hcard_list : divisorsX0.toFinset.card = 256 := by
      rw [List.toFinset_card_of_nodup divisorsX0_sorted.nodup]
      decide
    have hset_eq : divisorsX0.toFinset = X0.divisors :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) divisorsX0_sorted.nodup]
    intro d
    rw [Finset.mem_sort, ← hset_eq, List.mem_toFinset]
  · exact Finset.pairwise_sort _ _
  · exact divisorsX0_sorted.imp le_of_lt

set_option maxRecDepth 8192 in
private lemma a_X0_eq_8 : a X0 = 8 := by
  rw [a_eq, divisorsX0_eq_divList]
  decide

private lemma kthPrimorial_ratio_eq_X0 :
    kthPrimorial 12 / kthPrimorial (Nat.primeCounting' 8) = X0 := by
  have hp0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have hp1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  have hp2 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  have hp3 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_count (show Nat.Prime 7 by decide)
  have hp4 : Nat.nth Nat.Prime 4 = 11 := Nat.nth_count (show Nat.Prime 11 by decide)
  have hp5 : Nat.nth Nat.Prime 5 = 13 := Nat.nth_count (show Nat.Prime 13 by decide)
  have hp6 : Nat.nth Nat.Prime 6 = 17 := Nat.nth_count (show Nat.Prime 17 by decide)
  have hp7 : Nat.nth Nat.Prime 7 = 19 := Nat.nth_count (show Nat.Prime 19 by decide)
  have hp8 : Nat.nth Nat.Prime 8 = 23 := Nat.nth_count (show Nat.Prime 23 by decide)
  have hp9 : Nat.nth Nat.Prime 9 = 29 := Nat.nth_count (show Nat.Prime 29 by decide)
  have hp10 : Nat.nth Nat.Prime 10 = 31 := Nat.nth_count (show Nat.Prime 31 by decide)
  have hp11 : Nat.nth Nat.Prime 11 = 37 := Nat.nth_count (show Nat.Prime 37 by decide)
  have hpc8 : Nat.primeCounting' 8 = 4 := by decide
  rw [hpc8]
  unfold kthPrimorial
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11]
  decide

/-! ### Main Theorem -/

/--
Let $p\#_i$ denote the $i$-th primorial (`kthPrimorial i`).
$p\#_{12}/p\#_4 = 35336848261$ is the least $x \ge 2$ such that $a(x) = 8$.
(`FormalConjectures/OEIS/251758.lean`, `conjecture`)
-/
theorem conjecture :
    IsLeast {x : ℕ | 2 ≤ x ∧ a x = 8}
      (kthPrimorial 12 / kthPrimorial (Nat.primeCounting' 8)) := by
  rw [kthPrimorial_ratio_eq_X0]
  refine ⟨⟨by decide, a_X0_eq_8⟩, ?_⟩
  intro x ⟨hx2, hax⟩
  by_contra hlt
  push Not at hlt
  exact a_ne_8_of_lt_X0 hx2 hlt hax

#print axioms conjecture

end OeisA251758

end
