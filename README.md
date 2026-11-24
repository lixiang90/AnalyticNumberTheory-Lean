# AnalyticNumberTheory-Lean

A structured, `sorry`-free Lean 4 + Mathlib (`v4.36.0`) library and interactive [Verso](https://github.com/leanprover/verso) online encyclopedia for Analytic Number Theory, grounded in 潘承洞、潘承彪《解析数论基础》 and organized purely by mathematical theme.

- **Online Encyclopedia**: https://lixiang90.github.io/AnalyticNumberTheory-Lean/
- **Repository**: https://github.com/lixiang90/AnalyticNumberTheory-Lean

## Structure

- `AnalyticNumberTheory/` — Formal Lean 4 modules organized into ten thematic domains:
  1. `AnalyticTools/` — Integral transforms, summation formulas (Abel, Euler–Maclaurin, Poisson), Gamma & Stirling, complex function bounds (Jensen, Borel–Carathéodory, Hadamard three-circles, Phragmén–Lindelöf), finite-order entire functions & Hadamard factorization.
  2. `DirichletSeries/` — Convergence abscissae, uniqueness & Landau's theorem, arithmetic convolutions, Euler products, Perron's formula, vertical order & mean value theorems.
  3. `RiemannZeta/` — Functional equation, pole & vertical bounds, Hadamard product & zero expansion, zero counting, de la Vallée Poussin zero-free region, Riemann Hypothesis equivalences, asymptotics & moments.
  4. `PrimeDistribution/` — Chebyshev functions, Mertens' theorems, the explicit formula, the Prime Number Theorem with error term, oscillation, primes in progressions, conditional short-interval estimates, a Bombieri–Vinogradov reduction and least-prime criteria.
  5. `DirichletLFunctions/` — Dirichlet characters & primitive conductors, Gauss sums, Pólya–Vinogradov character sums, functional equations, zero expansions, zero-free regions, Page & Siegel theorems.
  6. `ExponentialSums/` — Weyl differencing, van der Corput A/B processes & exponent pairs, Vaughan's identity & linear prime exponential sums, Vinogradov mean value & Hua's lemma.
  7. `AdditiveNumberTheory/` — Circle-method identities, Goldbach singular series, major-arc approximation and the ternary asymptotic under the Siegel–Walfisz estimate. Waring topics include integral and local representation counts, discrete Fourier inversion, Chinese remainder factorization and uniform convergence of the singular series for degree `k` and `s > 2k` variables. The library also proves local solubility for prime powers coprime to the degree when `s > k`, absolute integrability of the real factor in that range, and a minor-arc power saving for `s > 2^k` and `k ≥ 2`.
  8. `DivisorProblems/` — Dirichlet's hyperbola identity over semirings, average orders of arithmetic functions, Jacobi's two-square theorem, Gauss circle counts and a Fourier proof of the divisor error estimate $O(x^{1/3}\log x)$.
  9. `SieveMethods/` — Legendre's prime-counting formula, Buchstab's identity, Brun and Selberg sieves, analytic and arithmetic large sieves, Brun–Titchmarsh estimates, hybrid mean values of Dirichlet polynomials and the Halász–Montgomery large-values inequality.
  10. `ModularAndPartitions/` — Dedekind sums & reciprocity, Dedekind $\eta$-function modular transformations, integer partitions & asymptotic bounds.
- `Encyclopedia/` — Human-readable Verso online encyclopedia (`VersoManual`) with KaTeX math, live typechecked docstrings, cross-references, citations, and searchable index.

## Reading the formalization

The encyclopedia introduces the ten themes in Chinese. For example, its Waring article derives
the exact integral for the number of ordered representations by nonnegative powers, and its
divisor article evaluates the hyperbola identity at a finite cutoff. Each displayed Lean
declaration links the mathematical statement to the hypotheses used by the library.

Coverage is still in progress. The deduction of the Hardy–Ramanujan partition asymptotic uses
`RademacherSeriesFormula` as a hypothesis. The Bombieri–Vinogradov reduction takes a mean bound
on primitive character sums as input. The ternary Goldbach asymptotic and its consequence for
three odd primes currently take the uniform Siegel–Walfisz estimate as a hypothesis. Other
outstanding results include the general Waring asymptotic and Linnik's least-prime bound.

## Building

```bash
lake exe cache get
lake build AnalyticNumberTheory Encyclopedia
lake run verso/versoMain EncyclopediaMain.lean
```

The generated multi-page HTML encyclopedia is written to `_out/html-multi/`.
