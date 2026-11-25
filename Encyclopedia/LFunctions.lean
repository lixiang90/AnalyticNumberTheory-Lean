import AnalyticNumberTheory.DirichletLFunctions.PrimitiveApproximateFunctionalEquation
import AnalyticNumberTheory.DirichletLFunctions.PeriodicApproximateFunctionalEquation
import AnalyticNumberTheory.DirichletLFunctions.FunctionalEquation
import AnalyticNumberTheory.DirichletLFunctions.ZeroCounting
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.DirichletLFunctions

#doc (Manual) "Dirichlet L 函数的函数方程与零点计数" =>
%%%
tag := "dirichlet-functional-equation"
file := "dirichlet-functional-equation"
%%%

{index}[Dirichlet L 函数]设 $`\chi` 是模 $`q` 的原特征。对 $`L(s,\chi)` 补上由特征奇偶性决定的 Gamma 因子，可将 $`1-s` 处的值与共轭特征在 $`s` 处的值联系起来。Lean 采用的补全函数将模数幂单独列出，因此下式右端显式含有 $`q^{s-1/2}`。

{docstring completedLFunction_one_sub_primitive}

归一化 Gauss 和给出的根数决定相位。它的模为一，所以对函数方程两边取绝对值时，根数这一项消失。

{docstring norm_rootNumber_primitive}

# 按导子计数零点
%%%
file := "conductor-zero-count"
tag := "conductor-zero-count"
%%%

{index}[Riemann–von Mangoldt 公式]设 $`f` 为特征 $`\chi` 的导子。令 $`N_\chi(T)` 为开临界带内满足 $`|\operatorname{Im}\rho|\le T` 的零点数，每个零点按重数计入。对所有 $`T\ge 2`，有

$$`N_\chi(T)=\frac{T}{\pi}\log\frac{fT}{2\pi e}+O(\log(fT)).`

同一个误差常数适用于所有模数、所有特征及所有这样的高度。原始特征的证明对矩形边界应用辐角原理。非原始特征比诱导它的原始特征多出的有限 Euler 因子，在开临界带内处处非零。

{docstring zeroCountL_riemannVonMangoldt_uniform}

主特征的导子为一。由于这里上下两个半平面都计数，其结果正好等于{ref "zeta-zeros"}[黎曼 ζ 函数上半平面零点数]的两倍。

{docstring zeroCountL_principal}

# 周期系数的截断函数方程
%%%
tag := "sharp-periodic-equation"
file := "periodic-cutoffs"
%%%

令 $`\Phi` 是模 $`q\ge1` 的周期函数，满足 $`|\Phi|\le1`。将 $`L(s,\Phi)` 展开成各个剩余类的 Hurwitz ζ 函数，对每一类应用{ref "sharp-hurwitz-equation"}[截断公式]。合并后，直接和为 $`\sum_{n\le qx}\Phi(n)n^{-s}`，另一侧有频率 $`0<|n|\le y`，其中 $`2\pi xy=|\Im s|`。对偶系数是未归一化的有限 Fourier 变换

$$`\widehat{\Phi}(n)=\sum_{r=1}^q\Phi(r)\exp(-2\pi i nr/q).`

在对偶和的每一项中，$`\widehat{\Phi}(n)` 乘以 $`q^{-s}\Gamma(1-s)(-2\pi i n)^{s-1}`。逐类相加给出至多为 Hurwitz 误差界 $`q^{1-\sigma}` 倍的余项，其中 $`\sigma=\Re s`。一般周期函数与任意模 $`q` 的 Dirichlet 特征都可直接使用这个估计。

{docstring periodicLFunction_sharp_afe}

{docstring dirichletLFunction_sharp_afe}

当 $`\chi` 是原特征时，它的 Fourier 变换可写为 Gauss 和乘以共轭特征。由 $`\chi(-1)` 合并正、负频率，对偶侧只需计算一个多项式 $`\sum_{n\le y}\overline{\chi(n)}\,n^{s-1}`。与之相乘的因子包含 $`q^{-s}`、Gauss 和和两个频率的 Gamma 因子，适用于奇、偶两类原特征。

{docstring primitiveLFunction_sharp_afe}
