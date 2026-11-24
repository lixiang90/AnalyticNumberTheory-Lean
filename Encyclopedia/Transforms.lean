import AnalyticNumberTheory.AnalyticTools.Transforms
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AnalyticTools

#doc (Manual) "Fourier 与 Mellin 变换" =>
%%%
tag := "fourier-mellin"
file := "fourier-mellin"
%%%

{index}[Fourier 变换]在核 $`e^{-2\pi i x\xi}` 的归一化下，函数 $`g(x)=e^{-\pi x^2}` 的 Fourier 变换仍是 $`g`。常数 $`\pi` 的位置很重要，它使得频率变量与原变量采用同一尺度。

{docstring fourier_gaussian_selfReciprocal}

{index}[Mellin 变换]Mellin 变换的核为 $`t^{s-1}`，它适合处理伸缩。对 $`t>0` 展开 $`1/(e^t-1)=\sum_{n\ge1}e^{-nt}`，在积分中作代换 $`u=nt`，每一项贡献 $`n^{-s}\Gamma(s)`。当 $`\operatorname{Re}(s)>1` 时，可以交换求和与积分，于是得到 $`\Gamma(s)\zeta(s)`。

{docstring mellin_inv_exp_sub_one_eq_gamma_mul_zeta}
