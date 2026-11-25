# AnalyticNumberTheory-Lean

A structured, `sorry`-free Lean 4 + Mathlib (`v4.36.0`) library and interactive [Verso](https://github.com/leanprover/verso) online encyclopedia for Analytic Number Theory, grounded in 潘承洞、潘承彪《解析数论基础》 and organized purely by mathematical theme.

- **Online Encyclopedia**: https://lixiang90.github.io/AnalyticNumberTheory-Lean/
- **Repository**: https://github.com/lixiang90/AnalyticNumberTheory-Lean

## Structure

- `AnalyticNumberTheory/` — Formal Lean 4 modules organized into ten thematic domains:
  1. `AnalyticTools/` — Farey fractions and period dissections, integral transforms, summation formulas (Abel, Euler–Maclaurin, Poisson), Gamma & Stirling, complex function bounds (Jensen, Borel–Carathéodory, Hadamard three-circles, Phragmén–Lindelöf), finite-order entire functions & Hadamard factorization.
  2. `DirichletSeries/` — Convergence abscissae, uniqueness & Landau's theorem, arithmetic convolutions, Euler products, Perron's formula, vertical order & mean value theorems.
  3. `RiemannZeta/` — Functional equation, pole, convexity and Weyl subconvexity bounds, Hadamard product & zero expansion, zero counting, de la Vallée Poussin and Littlewood zero-free regions, Riemann Hypothesis equivalences, the critical-line second moment, the Hurwitz zeta mean square $T\zeta(2\sigma,a)$ for fixed real shifts $0<a\le1$ and $1/2<\sigma\le1$, Ingham’s fourth-moment asymptotic with leading coefficient $1/(2\pi^2)$, and Hardy’s theorem on infinitely many zeros on the critical line.
  4. `PrimeDistribution/` — Chebyshev functions, Mertens' theorems, the explicit formula, the Prime Number Theorem with error $O_d(x\exp(-d\sqrt{\log x}))$ for every fixed $d>0$, oscillation, the uniform Siegel–Walfisz theorem for primes in progressions, Ingham’s zero-density exponent $3(1-\sigma)/(2-\sigma)$ and Huxley’s exponent $12(1-\sigma)/5$, log-free zero-density estimates for zeta and for families of primitive Dirichlet characters, the prime number theorem in intervals of length $x^\theta$ for all fixed $\theta<1$ sufficiently close to one, the maximal Bombieri–Vinogradov theorem for ψ, θ and π, and Linnik’s polynomial least-prime theorem.
  5. `DirichletLFunctions/` — Dirichlet characters & primitive conductors, Gauss sums, Pólya–Vinogradov character sums, functional equations, a conductor-uniform Riemann–von Mangoldt formula, zero expansions, zero-free regions, Page and Siegel theorems, conductor-uniform Deuring–Heilbronn repulsion and Turán high-derivative zero detection, critical-line and right-strip mean squares for arbitrary fixed periodic coefficients, and height-aspect Weyl bounds.
  6. `ExponentialSums/` — Weyl differencing, van der Corput A/B processes & exponent pairs, Vaughan's identity & linear prime exponential sums, Vinogradov’s integral and solution-count identity, the leading diagonal constant $s!$ for $s\le k$, inhomogeneous and affine power-sum systems, nonsingular prime-power congruence counts, the classical Vinogradov mean value theorem with explicit constants in the degree, bilinear polynomial sums, and Hua's lemma.
  7. `AdditiveNumberTheory/` — Circle-method identities, Goldbach singular series, the weighted ternary asymptotic with arbitrary logarithmic saving and Vinogradov’s three-primes theorem. For two primes, the number of positive even exceptions up to N is O_A(N/(log N)^A) for every natural A. Waring topics include integral and local representation counts, discrete Fourier inversion, Chinese remainder factorization and an Euler product of local densities for the singular series for degree `k` and `s > 2k` variables. The library also proves local solubility for prime powers coprime to the degree when `s > k`, a Fourier inversion proof that the real factor at one equals `Γ(1+1/k)^s/Γ(s/k)` in that range, and the full circle-method asymptotic with error `o(n^(s/k−1))` for `s > 2^k` and `k ≥ 2`. A uniform lower bound for the singular series with sufficiently many variables yields the Hilbert–Waring theorem for every positive degree.
  8. `DivisorProblems/` — Dirichlet's hyperbola identity over semirings, average orders of arithmetic functions, Jacobi's two-square theorem, the $O(x^{1/3})$ Gauss circle discrepancy for squared radius $x$, and a Fourier proof of the divisor error estimate $O(x^{1/3}\log x)$.
  9. `SieveMethods/` — Legendre's prime-counting formula, Buchstab's identity, Brun and Selberg sieves, exact Rosser remainders with the fundamental lemma at large sieve parameter, the differential-delay equations for the linear sieve functions, analytic and arithmetic large sieves, Brun–Titchmarsh estimates, a prime-supported hybrid large sieve, hybrid mean values of Dirichlet polynomials and the Halász–Montgomery large-values inequality.
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
zeta zero-density bound. It proves Linnik's polynomial bound for the least prime in each reduced residue class.
Stronger zero-free regions and sharper prime estimates in short intervals remain in progress.

## Building

```bash
lake exe cache get
lake build AnalyticNumberTheory Encyclopedia
lake run verso/versoMain EncyclopediaMain.lean
```

The generated multi-page HTML encyclopedia is written to `_out/html-multi/`.
