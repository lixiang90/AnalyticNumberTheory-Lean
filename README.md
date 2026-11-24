# AnalyticNumberTheory-Lean

A structured, `sorry`-free Lean 4 + Mathlib (`v4.36.0`) library and interactive [Verso](https://github.com/leanprover/verso) online encyclopedia for Analytic Number Theory, grounded in 潘承洞、潘承彪《解析数论基础》 and organized purely by mathematical theme.

- **Online Encyclopedia**: https://lixiang90.github.io/AnalyticNumberTheory-Lean/
- **Repository**: https://github.com/lixiang90/AnalyticNumberTheory-Lean

## Structure

- `AnalyticNumberTheory/` — Formal Lean 4 modules organized into ten thematic domains:
  1. `AnalyticTools/` — Farey fractions and period dissections, integral transforms, summation formulas (Abel, Euler–Maclaurin, Poisson), Gamma & Stirling, complex function bounds (Jensen, Borel–Carathéodory, Hadamard three-circles, Phragmén–Lindelöf), finite-order entire functions & Hadamard factorization.
  2. `DirichletSeries/` — Convergence abscissae, uniqueness & Landau's theorem, arithmetic convolutions, Euler products, Perron's formula, vertical order & mean value theorems.
  3. `RiemannZeta/` — Functional equation, pole & vertical bounds, Hadamard product & zero expansion, zero counting, de la Vallée Poussin zero-free region, Riemann Hypothesis equivalences, the critical-line second moment and Hardy’s theorem on infinitely many zeros on the critical line.
  4. `PrimeDistribution/` — Chebyshev functions, Mertens' theorems, the explicit formula, the Prime Number Theorem with error term, oscillation, the uniform Siegel–Walfisz theorem for primes in progressions, zero-density estimates for zeta and families of primitive Dirichlet characters, short-interval results, the maximal Bombieri–Vinogradov theorem for ψ, θ and π and subexponential least-prime bounds.
  5. `DirichletLFunctions/` — Dirichlet characters & primitive conductors, Gauss sums, Pólya–Vinogradov character sums, functional equations, a conductor-uniform Riemann–von Mangoldt formula, zero expansions, zero-free regions, Page and Siegel theorems, Deuring–Heilbronn repulsion for the complex zeros of distinct primitive characters, and critical-line mean squares for periodic coefficients.
  6. `ExponentialSums/` — Weyl differencing, van der Corput A/B processes & exponent pairs, Vaughan's identity & linear prime exponential sums, Vinogradov mean value & Hua's lemma.
  7. `AdditiveNumberTheory/` — Circle-method identities, Goldbach singular series, the weighted ternary asymptotic with arbitrary logarithmic saving and Vinogradov’s three-primes theorem. For two primes, the number of positive even exceptions up to N is O_A(N/(log N)^A) for every natural A. Waring topics include integral and local representation counts, discrete Fourier inversion, Chinese remainder factorization and an Euler product of local densities for the singular series for degree `k` and `s > 2k` variables. The library also proves local solubility for prime powers coprime to the degree when `s > k`, a Fourier inversion proof that the real factor at one equals `Γ(1+1/k)^s/Γ(s/k)` in that range, and the full circle-method asymptotic with error `o(n^(s/k−1))` for `s > 2^k` and `k ≥ 2`. A uniform lower bound for the singular series with sufficiently many variables yields the Hilbert–Waring theorem for every positive degree.
  8. `DivisorProblems/` — Dirichlet's hyperbola identity over semirings, average orders of arithmetic functions, Jacobi's two-square theorem, Gauss circle counts and a Fourier proof of the divisor error estimate $O(x^{1/3}\log x)$.
  9. `SieveMethods/` — Legendre's prime-counting formula, Buchstab's identity, Brun and Selberg sieves, analytic and arithmetic large sieves, Brun–Titchmarsh estimates, hybrid mean values of Dirichlet polynomials and the Halász–Montgomery large-values inequality.
  10. `ModularAndPartitions/` — Dedekind sums & reciprocity, Dedekind $\eta$-function modular transformations, partition generating functions, modular inversion, the Hardy–Ramanujan saddle-point asymptotic and the exact Rademacher expansion with a finite truncation bound.
- `Encyclopedia/` — Human-readable Verso online encyclopedia (`VersoManual`) with KaTeX math, live typechecked docstrings, cross-references, citations, and searchable index.

## Reading the formalization

The encyclopedia introduces the ten themes in Chinese. For example, its Waring article derives
the exact integral for the number of ordered representations by nonnegative powers, and its
divisor article evaluates the hyperbola identity at a finite cutoff. Each displayed Lean
declaration links the mathematical statement to the hypotheses used by the library.

The library proves the Hardy–Ramanujan leading term by a saddle-point argument and the
Bombieri–Vinogradov mean estimate by Vaughan's identity and the large sieve. Coverage
is still in progress. The library also proves the exact Rademacher series and an unconditional
zeta zero-density bound. Remaining work includes stronger zero-free regions and Linnik's
polynomial bound for the least prime in a progression.

## Building

```bash
lake exe cache get
lake build AnalyticNumberTheory Encyclopedia
lake run verso/versoMain EncyclopediaMain.lean
```

The generated multi-page HTML encyclopedia is written to `_out/html-multi/`.
