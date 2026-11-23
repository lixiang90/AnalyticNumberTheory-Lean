# AnalyticNumberTheory-Lean

A structured, `sorry`-free Lean 4 + Mathlib (`v4.36.0`) library and interactive [Verso](https://github.com/leanprover/verso) online encyclopedia for Analytic Number Theory, grounded in 潘承洞、潘承彪《解析数论基础》 and organized purely by mathematical theme.

- **Online Encyclopedia**: https://lixiang90.github.io/AnalyticNumberTheory-Lean/
- **Repository**: https://github.com/lixiang90/AnalyticNumberTheory-Lean

## Structure

- `AnalyticNumberTheory/` — Formal Lean 4 modules organized into ten thematic domains:
  1. `AnalyticTools/` — Integral transforms, summation formulas (Abel, Euler–Maclaurin, Poisson), Gamma & Stirling, complex function bounds (Jensen, Borel–Carathéodory, Hadamard three-circles, Phragmén–Lindelöf), finite-order entire functions & Hadamard factorization.
  2. `DirichletSeries/` — Convergence abscissae, uniqueness & Landau's theorem, arithmetic convolutions, Euler products, Perron's formula, vertical order & mean value theorems.
  3. `RiemannZeta/` — Functional equation, pole & vertical bounds, Hadamard product & zero expansion, zero counting, de la Vallée Poussin zero-free region, Riemann Hypothesis equivalences, asymptotics & moments.
  4. `PrimeDistribution/` — Chebyshev functions & Mertens' theorems, explicit formula, Prime Number Theorem with error term, oscillation theorems, primes in arithmetic progressions, short intervals & Linnik/Bombieri–Vinogradov frameworks.
  5. `DirichletLFunctions/` — Dirichlet characters & primitive conductors, Gauss sums, Pólya–Vinogradov character sums, functional equations, zero expansions, zero-free regions, Page & Siegel theorems.
  6. `ExponentialSums/` — Weyl differencing, van der Corput A/B processes & exponent pairs, Vaughan's identity & linear prime exponential sums, Vinogradov mean value & Hua's lemma.
  7. `AdditiveNumberTheory/` — Hardy–Littlewood circle method, Goldbach problem (singular series & minor arcs), Waring's problem.
  8. `DivisorProblems/` — Dirichlet hyperbola method, average orders of arithmetic functions, Gauss circle problem & Voronoï/van der Corput refinements.
  9. `SieveMethods/` — Large sieve & Gallagher duality, Dirichlet polynomial mean values & Halász method, combinatorial sieves (Brun, Buchstab, Rosser), Selberg upper bound sieve.
  10. `ModularAndPartitions/` — Dedekind sums & reciprocity, Dedekind $\eta$-function modular transformations, integer partitions & asymptotic bounds.
- `Encyclopedia/` — Human-readable Verso online encyclopedia (`VersoManual`) with KaTeX math, live typechecked docstrings, cross-references, citations, and searchable index.

## Building

```bash
lake exe cache get
lake build AnalyticNumberTheory Encyclopedia
lake run verso/versoMain EncyclopediaMain.lean
```

The generated multi-page HTML encyclopedia is written to `_out/html-multi/`.
