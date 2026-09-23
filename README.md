# A Lean proof of an improved upper bound for Green's Open Problem 25

This repository formalizes a solution to the **upper-bound target** registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/25.lean).
Green's problem asks for which `k` every partition

```text
{1, ..., N} = A_1 ∪ ... ∪ A_k
```

satisfies `|⋃_i (A_i ∔ A_i)| ≥ N/10`, where `A ∔ A = {a + b : a, b ∈ A, a ≠ b}`.
The best-known upper bound [ESS89] says this can fail for `k ≍ N / log N`.
We prove that it already fails, for all sufficiently large `N`, with

```text
k(N) = ⌈N^(23/40)⌉ = o(N / log N).
```

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fgreen-25-upper-bound%2Frefs%2Fheads%2Fmain%2Flean4web%2FGreen25UpperLean4Web.lean)

This does **not** solve the main theorem `Green25.green_25` (the exact set of admissible `k`)
or the lower-bound question `Green25.green_25.lower`.  The exponent `23/40` is not claimed
to be optimal.

## Formal Conjectures target

The file in `lean/` imports the Formal Conjectures statement and proves it with the
explicit answer `N ↦ ⌈N^(23/40)⌉`:

```lean
@[category research solved, AMS 5 11]
theorem green_25_upper_solved :
    let ans := (answer(fun N => Nat.ceil ((N : ℝ) ^ (23 / 40 : ℝ))) : ℕ → ℕ)
    (∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧
    (fun N => (ans N : ℝ)) =o[atTop] Green25.bestUpper ∧
    ¬ ∀ᶠ N in atTop, Green25.Property25 (ans N) N
```

Thus the theorem `Green25.green_25.upper` can be changed from `research open` to
`research solved` by replacing its answer hole with `fun N => Nat.ceil ((N : ℝ) ^ (23 / 40 : ℝ))` and using this proof.

The proof gives an explicit threshold: for every `N > 2^(10240000 - 1)`,

```lean
¬ Green25.Property25 (Nat.ceil ((N : ℝ) ^ (23 / 40 : ℝ))) N
```

so the counterexamples hold for **all** sufficiently large `N`, not only along a subsequence.

## Mathematical Explanation (AI generated)

**Theorem.**  Let $N > 2^{10239999}$ and $K = \lceil N^{23/40} \rceil$.  There is a partition
$\{1,\dots,N\} = A_1 \cup \dots \cup A_K$ into $K$ non-empty classes with
$$\Bigl|\bigcup_{i} (A_i \mathbin{\hat{+}} A_i)\Bigr| < \frac{N}{10}.$$
Since $N^{23/40} = o(N/\log N)$, this gives `Green25.green_25.upper`.

*Proof sketch.*  Choose $d$ with $2^{d-1} < N \le 2^d$ and write $d = 8\ell + r$ with
$0 \le r < 8$.  Put $t = \lfloor 23(d-1)/40 \rfloor$, so that $2^t \le N^{23/40} \le K$.
Fix $q = 1/16$.

**1. Linear colourings.**  Identify $x \in \{1,\dots,2^d\}$ with the binary digits of $x - 1$, a
vector in $\mathbb F_2^d$.  (This shifts every sum by $2$, which does not affect the counting.)
For a linear map $H : \mathbb F_2^d \to \mathbb F_2^t$, colour $x$ by $Hx$.  This uses at most
$2^t$ colours.  If $x \ne y$ have the same colour, then $c = x \oplus y$ is non-zero and
$Hc = 0$.  So the sum $s = x + y$ lies in
$$\mathrm{Bad}(H) = \{\, s : \exists\, c \ne 0,\ Hc = 0,\ \exists\, x,\ x + (x \oplus c) = s \,\}.$$

**2. Counting differences by carries.**  Add $x$ and $x \oplus c$ digit by digit without
carrying.  The result is a word $z \in \{0,1,2\}^d$ with $\sum_i z_i 2^i = s$, and
$z_i = 1$ exactly where $c_i = 1$.  Hence $c$ is recovered from $z$.  So the number of
admissible $c$ for a given $s$ is at most
$$h_d(s) = \#\Bigl\{ z \in \{0,1,2\}^d : \sum_i z_i 2^i = s \Bigr\}.$$

**3. A fractional union bound.**  For uniformly random $H$ and fixed $c \ne 0$,
$\Pr[Hc = 0] = 2^{-t}$.  Hence, for $0 \le q \le 1$,
$$\Pr[s \in \mathrm{Bad}(H)] \le \min\bigl(1,\ h_d(s)\,2^{-t}\bigr) \le \bigl(h_d(s)\,2^{-t}\bigr)^q.$$
Summing over $s$ gives
$$\mathbb E\,|\mathrm{Bad}(H)| \le 2^{-tq} \sum_s h_d(s)^q.$$
The saturation at $1$, used through the exponent $q < 1$, is what beats the plain union bound.

**4. The carry recursion.**  Read the digits of $z$ from the least significant end and keep
track of the carry.  The pair $(a, b)$ counts representations of the current output prefix
that end with carry $0$ or $1$.  Each output bit acts by
$$T_0(a,b) = (a,\ a+b), \qquad T_1(a,b) = (a+b,\ b),$$
starting from $(1, 0)$.  A sum $s$ corresponds to an output word $w$ together with a final
carry.  Therefore
$$\sum_s h_d(s)^q = \sum_{|w| = d} \bigl(a_w^q + b_w^q\bigr) \le 2^{1-q} \sum_{|w| = d} (a_w + b_w)^q,$$
using $a^q + b^q \le 2^{1-q}(a+b)^q$.

**5. Block estimate.**  Let $F_n(a,b) = \sum_{|w| = n} \| T_w(a,b) \|_1^q$.  This function is
concave, since $x \mapsto x^q$ is concave and the $T_w$ are linear.  It is also invariant
under swapping $a$ and $b$.  Averaging $(a,b)$ with $(b,a)$ gives
$$F_L(a,b) \le B_L(q)\,(a+b)^q, \qquad B_L(q) = \sum_{|w| = L} \Bigl(\tfrac12 \| T_w(1,1) \|_1\Bigr)^q.$$
Iterating over $\ell$ blocks of length $8$ and then $r$ single bits gives
$$\sum_s h_d(s)^q \le 2^{1-q}\, B_8(q)^{\ell}\, \bigl(2 \cdot (3/2)^q\bigr)^{r}.$$

**6. The numerical certificate.**  Evaluating all $256$ words of length $8$ and rounding each
term upwards gives
$$B_8(1/16) \le 312.445416.$$
With $\rho = B_8(1/16) / 2^{663/80}$, where $663/80 = 8 + 8 \cdot \tfrac1{16} \cdot \tfrac{23}{40}$,
an integer computation shows $\rho^{80} < 999/1000$.  The choice of $t$ gives
$2^{663\ell/80} \le 2^{d+1}\, 2^{tq}$, so the bounds above combine to
$$\mathbb E\,|\mathrm{Bad}(H)| \le C \cdot 2^{d} \rho^{\ell}$$
for an absolute constant $C$.  For $\ell \ge 1{,}280{,}000$ this is below $2^{d-6}$, so some
$H$ has $|\mathrm{Bad}(H)| < 2^{d-6}$.

**7. Restricting and refining.**  Restrict this colouring to $\{1,\dots,N\}$.  It uses at most
$2^t \le K \le N$ colours.  Split classes until exactly $K$ classes are non-empty.  A
refinement cannot create new monochromatic pairs, so the restricted sumset of the resulting
partition has fewer than $2^{d-6}$ elements.  Finally
$$10 \cdot 2^{d-6} < 2^{d-1} < N.$$
This contradicts `Property25 K N`. $\square$

**Remarks.**  The huge threshold comes only from the crude contraction $\rho^{80} < 0.999$;
nothing is optimised.  Every step above, including the $256$-word computation (by `decide`), is
checked by the Lean kernel; no external computation is trusted.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.27.0` | Formal Conjectures version, pinned to commit `2411d22e...` |
| `lean4web/` | `v4.35.0-rc2` | Standalone mathlib-only proof for Lean4Web (mathlib `809072a6...`) |

Each directory contains one proof file, `lakefile.toml`, `lean-toolchain`, and
`lake-manifest.json`.  The standalone file copies the Formal Conjectures definitions of
`Finset.restrictedSumset`, `Green25.Property25` and `Green25.bestUpper` verbatim.  It also
copies the Formal Conjectures `answer( )` elaborator.  Because Lean4Web checks a single file,
the option `google.answer` cannot be registered and read there, so it is fixed to its default
`.alwaysTrue`.  The file then proves the same statement with the same
`answer(fun N => Nat.ceil ((N : ℝ) ^ (23 / 40 : ℝ)))`, omitting only the `category`
attribute.  It targets the
Lean4Web runtime "Latest Mathlib with Lean v4.35.0-rc2".  Its first command,
`attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent`, stops that mathlib
from finding `AddCommGroup (ZMod 2)` through a group-theoretic instance.  That instance is not
reducibly equal to the ring structure.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both results are kernel checked.  The proof files contain no `sorry`, `admit`, custom axiom,
`native_decide`, or `unsafe` theorem.  Their final `#print axioms` commands report only Lean's
standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

## Status boundary

What is solved here:

```text
For all N > 2^(10240000 - 1), some partition of {1, ..., N} into exactly ⌈N^(23/40)⌉
classes has |⋃ (A_i ∔ A_i)| < N/10.  Hence Green25.green_25.upper holds with
answer N ↦ ⌈N^(23/40)⌉.
```

What remains open:

```text
Determine the exact set of k for which Property25 eventually holds,
and improve the lower bound log log N.
```

The current Formal Conjectures `main` uses Lean `v4.33.1`.  There, `25.lean` has moved to the
module system (`module`, `public section`), but the statement is unchanged.  This repository
has not yet been built against that version.

## Sources

- [Green, B. "100 open problems", Problem 25](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.25)
- [Formal Conjectures: `GreensOpenProblems/25.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/25.lean)
- Erdős, P., Sárközy, A., Sós, V. T. "On a conjecture of Roth and some related problems I" (1989).
- Ruzsa, I. Z. "A problem on restricted sumsets" (2004).
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced
by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra, and Claude Code
using Claude Opus 5.5.
