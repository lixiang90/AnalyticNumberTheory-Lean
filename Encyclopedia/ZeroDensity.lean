import AnalyticNumberTheory.PrimeDistribution.ShortIntervalEstimates
import AnalyticNumberTheory.PrimeDistribution.DirichletZeroCountDensity
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.PrimeDistribution

#doc (Manual) "ζ 函数的零密度估计与短区间素数" =>
%%%
tag := "zero-density"
file := "zero-density"
%%%

{index}[零密度估计]令 $`N(\sigma,T)` 计入满足 $`\sigma\le\Re\rho<1`、$`0<\Im\rho\le T` 的不同 ζ 零点。若 $`1/2\le\sigma\le1`、$`T\ge2`，有

$$`N(\sigma,T)\ll T^{4(1-\sigma)}(\log T)^{11}.`

当 $`\sigma>3/4` 时，右端的高度幂次小于一。证明用{ref "zero-detection"}[截断 Möbius 多项式]把零点转成 Dirichlet 多项式的大值，再在单位高度区间取样。若每个零点按重数计入，库中给出的界多一个对数因子。

{docstring zeta_zeroDensity}

{docstring zeta_zeroDensity_with_multiplicity}

{index}[短区间素数]截断显式公式把 $`\psi(x+h)-\psi(x)` 与零点的贡献联系起来。对于 $`h=x^\theta` 和 $`3/4<\theta<1`，下述结论仍使用声明中的加强无零区假设。零密度估计与截断显式公式两项已由库中的定理给出。

{docstring psi_shortInterval_of_superLogZeroFree}

另一个无条件范围直接来自带误差项的{ref "prime-counting"}[素数定理]。存在 $`d>0`，取 $`h=x\exp(-d\sqrt{\log x})` 时，$`\psi(x+h)-\psi(x)` 与 $`\vartheta(x+h)-\vartheta(x)` 都渐近于 $`h`。

{docstring chebyshev_expShortInterval}

# Dirichlet 特征族的零点
%%%
tag := "dirichlet-family-density"
file := "character-families"
%%%

令 $`Y=Q(T+2)`，其中 $`Q\ge1`、$`T\ge0`。把模数不超过 $`Q` 的所有原始非主特征放在一起，统计各自 $`L` 函数在 $`\sigma\le\Re\rho<1`、$`|\Im\rho|\le T` 的零点。对 $`3/4\le\sigma\le1`，不同零点按每个特征分别计数后，总数至多为

$$`C(1+\log Y)^{10}Y^{16(1-\sigma)}.`

常数 $`C` 与模数上限、高度和实部截点无关。共轭特征把负纵坐标的零点映到正纵坐标，实零点也计入这个估计。

{docstring dirichlet_family_zeroDensity}

按重数计数时，对每个零点再用局部零点个数控制其重数，得到幂次为十一的对数因子。结合全临界带内的粗计数，这个带重数的上界适用于 $`0\le\sigma\le1`。若 $`(1-\sigma)\log Y\ge\log(1+\log Y)`，还可把对数因子吸收到幂中，得到 $`CY^{27(1-\sigma)}`。

{docstring primitiveFamilyZeroCount_le}

{docstring primitiveFamilyZeroCount_le_of_log_gap}
