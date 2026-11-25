import AnalyticNumberTheory.RiemannZeta.RiemannSiegelElementaryPhase
import AnalyticNumberTheory.RiemannZeta.RiemannSiegelFirstCorrection
import AnalyticNumberTheory.RiemannZeta.HurwitzFirstCorrection
import AnalyticNumberTheory.RiemannZeta.RiemannSiegelCorrection
import AnalyticNumberTheory.RiemannZeta.HurwitzBoundedHeight
import AnalyticNumberTheory.RiemannZeta.RiemannSiegelCosine
import AnalyticNumberTheory.RiemannZeta.RiemannUnbalancedApproximation
import AnalyticNumberTheory.RiemannZeta.RiemannSharpApproximation
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import AnalyticNumberTheory.RiemannZeta.SmoothedDirichletSums
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.RiemannZeta

#doc (Manual) "黎曼 ξ 函数与临界线" =>
%%%
tag := "riemann-xi"
file := "riemann-xi"
%%%

{index}[黎曼 ξ 函数]将 $`\zeta(s)` 与 Gamma 因子配成整函数 $`\xi(s)` 后，函数方程成为关于 $`s\mapsto 1-s` 的对称关系。按本库的归一化，$`\xi(0)=\xi(1)=1/2`。

{docstring xi_one_sub}

取 $`s=1/2+it`，此时 $`1-s=\overline{s}`。再用 $`\xi(\overline{s})=\overline{\xi(s)}`，可知临界线上每一点的函数值都为实数。

{docstring xi_half_add_mul_I_im}

{index}[光滑函数方程]用高斯权 $`e^{w^2}` 作竖线积分，可以把 $`\xi(s)^k` 写成关于 $`s` 和 $`1-s` 的两项之和。具体地，令 $`I_c(s,k)` 为沿 $`w=c+it` 对 $`\xi(s+w)^k e^{w^2}/w` 关于 $`t` 的积分，其中 $`c>0`。向左移动积分线时，$`w=0` 的留数给出 $`\xi(s)^k`。因此 $`I_c(s,k)+I_c(1-s,k)=2\pi\,\xi(s)^k`。

{docstring xi_pow_gaussian_functional_equation}

在 $`0<\Re s<1` 内，把两条积分线上的 Dirichlet 级数逐项积分，得到 $`\zeta(s)` 的两个绝对收敛的加权和。对 $`\zeta(s)^2`，展开系数是正因子个数 $`d(n)`。每个权由独立的竖线积分给定，因而可继续估计截断误差。

{docstring riemannZeta_smoothed_functional_equation}

{docstring riemannZeta_sq_smoothed_functional_equation}

# 两个截断和与 Hurwitz ζ 函数
%%%
tag := "sharp-hurwitz-equation"
file := "sharp-cutoffs"
%%%

{index}[近似函数方程]设 $`s=\sigma+it`，其中 $`0<\sigma<1`。取两个实截断点 $`x,y\ge 2`，使 $`2\pi xy=|t|`。对于 $`0<a\le1`，直接求和的一侧包含所有 $`m\ge0` 且 $`m+a\le x` 的项 $`(m+a)^{-s}`。另一侧按非零整数频率求和。写 $`e(u)=\exp(2\pi i u)`，便有

$$`\zeta(s,a)=\sum_{0\le m\le x-a}(m+a)^{-s}+
 \Gamma(1-s)\sum_{0<|n|\le y} e(-na)(-2\pi i n)^{s-1}+R.`

复幂取主值。余项对平移参数 $`a` 一致，对正、负高度均满足

$$`|R|\le256\left(1+\frac1{1-\sigma}\right)
  \left[x^{-\sigma}\bigl(1+\log(y+2)\bigr)+\frac{x^{1-\sigma}}{\sqrt{|t|}}\right].`

{docstring hurwitzZeta_sharp_afe}

取 $`a=1`，所有平移因子都等于一，正、负频率合成同一个 Gamma 因子，乘以 $`\sum_{n\le y}n^{s-1}`。例如，临界线上取 $`x=y=\sqrt{|t|/(2\pi)}`，两个有限和等长，误差为 $`O(|t|^{-1/4}\log |t|)`。对有理平移按同余类求和，就得到{ref "sharp-periodic-equation"}[周期系数的对应公式]。

{docstring riemannZeta_sharp_afe}

# 临界带上的无对数误差
%%%
tag := "log-free-hurwitz-approximation"
file := "log-free-approximation"
%%%

在{ref "sharp-hurwitz-equation"}[两个截断和的公式]中，若 $`2\le x\le y`，可将余项压到 $`604 x^{-\sigma}`。这个常数对 $`0<a\le1`、正负两种高度以及闭带 $`0\le\sigma\le1` 一致。改进来自保留驻点附近成对频率的符号，借助正弦和的抵消来估计原先产生对数的边界项。

{docstring hurwitzZeta_logFree_sharp_afe}

对于普通 ζ 函数，取 $`x=y=\sqrt{|t|/(2\pi)}`。当 $`|t|\ge8\pi` 时，临界线上的两个 Dirichlet 多项式都包含 $`\lfloor x\rfloor` 项，余项至多为 $`604(2\pi)^{1/4}|t|^{-1/4}`。

{docstring riemannSiegel_sharp_error}

普通 ζ 的函数方程还允许交换两侧截断点。对于 $`x,y\ge2`、$`2\pi xy=|t|` 的任意组合，统一余项为
$`O(x^{-\sigma}+|t|^{1/2-\sigma}y^{\sigma-1})`。

{docstring riemannZeta_unbalanced_sharp_afe}

# Hardy 函数的有限余弦和
%%%
tag := "hardy-riemann-siegel-cosine"
file := "hardy-cosine"
%%%

令 $`Z(t)=e^{i\vartheta(t)}\zeta(1/2+it)`，其中 $`e^{i\vartheta(t)}` 是 $`\Gamma_{\mathbb R}(1/2+it)` 的单位相位。由于函数方程将两个对称截断和化为一对共轭，得到实数公式

$$`Z(t)=2\sum_{n\le\sqrt{|t|/(2\pi)}}\frac{\cos(\vartheta(t)-t\log n)}{\sqrt n}+R(t).`

在 $`|t|\ge8\pi` 上有 $`|R(t)|\le604(2\pi)^{1/4}|t|^{-1/4}`。例如取 $`t=200\pi`，和式恰好需要 $`n=1,\ldots,10`。相位的辐角可以相差整周，给出相同的余弦值。

{docstring hardyZ_riemannSiegel_cosine}

对于带平移的 Hurwitz ζ，固定 $`B\ge1` 和 $`\varepsilon>0`，再取满足 $`2\le x\le y`、$`2\pi xy=\max(B,|t|)` 的两个截断点。当 $`0\le\sigma\le1`、$`|1-s|\ge\varepsilon` 时，余项为 $`O_{B,\varepsilon}(x^{-\sigma})`，对 $`0<a\le1` 一致。取 $`B\ge8\pi` 即可把这样的截断延伸到高度零。

{docstring hurwitzZeta_clipped_sharp_afe}

# Riemann–Siegel 首修正系数
%%%
tag := "riemann-siegel-first-coefficient"
file := "correction-coefficient"
%%%

令 $`c=2\{\sqrt{|t|/(2\pi)}\}`，花括号表示小数部分。Riemann–Siegel 展开中的第一个系数可用 Mordell 积分定义为连续实函数。除去分母为零的点，它有初等表达式

$$`C(c)=\frac{\cos\bigl(\pi(c^2/2-c-1/8)\bigr)}{\cos(\pi c)}.`

在 $`0\le c\le2` 内，余弦商有两个可去奇点。沿积分表示取极限，得到 $`C(1/2)=C(3/2)=1/2`。这为截断点的小数部分恰在这些位置时提供了同一个连续定义。

{docstring riemannSiegelCorrection_eq_cos_quotient}

{docstring riemannSiegelCorrection_one_half}

{docstring riemannSiegelCorrection_three_halves}

{docstring mordellIntegral_eq_riemannSiegelCorrection}

# Hurwitz ζ 函数的首修正公式
%%%
tag := "hurwitz-first-correction"
file := "hurwitz-first-correction"
%%%

在临界线上取 $`s=1/2+it`，令 $`t=2\pi x^2`、$`x\ge1024`。对位移 $`0<a\le1`，记 $`\lambda=\{x-a\}`、$`q=\lfloor x\rfloor`、$`v=x+\lambda-q`。从 $`\zeta(s,a)` 中减去在 $`x` 处截断的正向和与对偶和后，首修正项为

$$`x^{-s}\exp\!\left(\pi i\left(2x\lambda+\lambda^2-v^2/2-7/8\right)\right)C(v).`

减去此项后的余量至多为 $`Kx^{-3/2}`，也就是 $`O(t^{-3/4})`。同一个常数 $`K` 对所有上述位移都适用。取 $`a=1` 时 $`v=2\{x\}`，恢复 Riemann ζ 函数的首修正系数。$`C` 在两个可去奇点处取前节给出的连续值。

{docstring hurwitzFirstCorrection}

{docstring hurwitzZeta_first_correction}

对于全部 $`t\ge8\pi`，取 $`x=\sqrt{t/(2\pi)}` 后同一 Hurwitz 首修正公式仍有 $`O(t^{-3/4})` 的余量。令 $`N=\lfloor x\rfloor`，并用 $`\vartheta(t)` 表示 Hardy 单位因子的辐角。转到实函数 $`Z(t)` 后，公式为

$$`Z(t)=2\sum_{n=1}^{N}\frac{\cos(\vartheta(t)-t\log n)}{\sqrt n}
       +(-1)^{N+1}x^{-1/2}C(2\{x\})+O(t^{-3/4}).`

{docstring hurwitzZeta_first_correction_height}

{docstring hardyZ_riemannSiegel_first_correction}

以初等相位 $`\theta_0(t)=(t\log(t/(2\pi))-t)/2-\pi/8` 代替精确的 Gamma 相位后，实余弦和仍保留首个修正项和 $`O(t^{-3/4})` 的余项。

{docstring hardyZ_elementary_first_correction}
