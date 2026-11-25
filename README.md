# Lean 4 Proof of the First Occurrence of 8 in OEIS A251758

Machine-verified Lean 4.36.0 proof of `OeisA251758.conjecture` from [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/251758.lean), originally posed by Robert G. Wilson v on [OEIS A251758](https://oeis.org/A251758) (Dec 18, 2014).

## Theorem

For $n \ge 2$ with sorted divisors $1 = d_1 < d_2 < \dots < d_k = n$, let $s(n) = \sum_{i=1}^{k-1} d_i d_{i+1}$ and $a(n) = \lfloor n^2 / s(n) \rfloor$. Then

```math
X_0 = \frac{p\#_{12}}{p\#_4} = 11 \cdot 13 \cdot 17 \cdot 19 \cdot 23 \cdot 29 \cdot 31 \cdot 37 = 35{,}336{,}848{,}261
```

is the least integer $x \ge 2$ such that $a(x) = 8$.

## Proof Outline (`OeisA251758/Proof.lean`)

1. **Divisor reversal:** Using the involution $d \mapsto x / d$, $s(x) = x^2 \cdot R(\mathrm{divList}(x))$ where $R([d_1, \dots, d_k]) = \sum_{i=1}^{k-1} \frac{1}{d_i d_{i+1}}$, so $a(x) = 8 \implies \frac{1}{9} < R(\mathrm{divList}(x)) \le \frac{1}{8}$.
2. **Small prime factor exclusion:** By insertion monotonicity of $R$, if $x$ has a prime factor $p \le 7$, then $R(\mathrm{divList}(x)) \ge \frac{1}{p} \ge \frac{1}{7} > \frac{1}{8}$.
3. **Smooth-number dominance & rational Euler-product bound:** Any $x < X_0$ with all prime factors $\ge 11$ has at most $7$ distinct prime factors. Replacing them in increasing order with $Q_7 = \lbrace 11, 13, 17, 19, 23, 29, 31 \rbrace$ can only increase $R$, and splitting $Q_7$-smooth numbers at $500$ with a finite geometric-series Euler product in $\mathbb{Q}$ yields $R(\mathrm{divList}(x)) < 0.11103 < \frac{1}{9}$.
4. **Exact check at $X_0$:** Kernel-checked verification over all $256$ sorted divisors of $X_0$ establishing $a(X_0) = 8$.

## Verification

```sh
lake build
```

`#print axioms OeisA251758.conjecture` depends only on the three standard Lean axioms: `[propext, Classical.choice, Quot.sound]`.

## Provenance & Credits

- **Original question:** Robert G. Wilson v, [OEIS A251758](https://oeis.org/A251758) (Dec 18, 2014).
- **Earlier computational report:** An independent computational argument for $a(n)=8$ was posted on Oct 4, 2026 in [`the-omega-institute/trureturing#12805`](https://github.com/the-omega-institute/trureturing/issues/12805#issuecomment-5976408068) without a Lean formalization.
- **Formalization:** Pablo Santana Torres (with AI assistance via Gemini / Antigravity).
