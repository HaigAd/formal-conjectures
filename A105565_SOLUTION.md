# OEIS A105565: Lean-verified solution

This repository contains a Lean 4 proof of the discrepancy conjecture recorded in
[OEIS A105565](https://oeis.org/A105565).

For

\[
\alpha=\frac{\log 10}{\log\varphi}-4,
\qquad
\beta=\frac{\log 5}{2\log\varphi}-1,
\]

let `a(n)` be 1 if exactly five Fibonacci numbers have exactly `n` decimal digits, and 0
otherwise, and put \(S(n)=\sum_{k=1}^{n}a(k)\). The proof establishes the stronger identity

\[
S(n)=\lfloor n\alpha+\beta\rfloor-1 \qquad (n\ge 1),
\]

and therefore

\[
\beta-2<S(n)-\alpha n<\beta-1.
\]

## Formal artifact

- Lean source: `FormalConjectures/OEIS/105565.lean`
- Theorem: `OeisA105565.conjecture`
- Formal Conjectures base commit: `2411d22e1bd550d050d0eac6c1fb379a76a3e7c5`
- Lean/mathlib toolchain: 4.27.0

The proof checks the exact bounded-filter definition used by Formal Conjectures, including the
finite index range `range (5 * n + 10)`.

## Reproduction

From the repository root:

```sh
lake exe cache get
lake env lean FormalConjectures/OEIS/105565.lean
lake --wfail build 'FormalConjectures.OEIS.«105565»'
```

The verified build completed successfully with 8,055 jobs. The theorem's axiom report is:

```text
'OeisA105565.conjecture' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The target source contains no `sorry`, `admit`, `axiom`, or `unsafe` declaration.

## Paper

The short proof note and its LaTeX source are included as:

- `output/pdf/haig_codex_a105565.pdf`
- `paper/haig_codex_a105565.tex`

## Attribution and AI disclosure

Solved by OpenAI Codex, prompted by Adam Haig.

Adam Haig supplied the prompt, selected the conjecture and acceptance criteria, authorized
publication, and reviewed the resulting mathematical and formal artifacts. OpenAI Codex performed
the majority of the mathematical work: it developed and refined the cutoff argument, located
relevant mathlib lemmas, generated and iteratively repaired the Lean formalization, executed the
verification checks, and drafted the accompanying note. Adam Haig is the human submitter and is
responsible for maintaining the public deposit and correcting any error that may be found.
