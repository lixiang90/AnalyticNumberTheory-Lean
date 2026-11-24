import AnalyticNumberTheory.ModularAndPartitions.PartitionAsymptotic
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.ModularAndPartitions

#doc (Manual) "Hardy–Ramanujan 分拆渐近公式" =>
%%%
tag := "partition-asymptotic"
file := "partition-asymptotic"
%%%

{index}[Hardy–Ramanujan 分拆渐近公式]当 $`n\to\infty` 时，无序分拆数满足

$$`p(n)\sim\frac{1}{4\sqrt3\,n}\exp\!\left(\pi\sqrt{\frac{2n}{3}}\right).`

{docstring hardyRamanujanAsymptotic}

从{ref "integer-partitions"}[分拆生成函数] $`F(q)` 的 Fourier 系数积分出发，取 $`q=e^{-2\pi z}`。由{ref "dedekind-eta"}[Dedekind η 函数]的反演律，在 $`\Re z>0` 的整个半平面上都有下列精确等式。它把接近单位圆的生成函数变为另一个可估计的生成函数。

{docstring partitionGenFun_nome_inversion}

积分圆的高度取 $`y=(24n)^{-1/2}`。在中心弧上，相位的一次项抵消。把横坐标写成 $`x=y^{3/2}u` 后，核收敛到高斯函数，中心积分的常数来自其总质量。

{docstring tendsto_integral_partitionSaddleKernel}

在其余弧段上，中间区域用模反演，远离中心的区域用 Euler 乘积的前八个因子。将相邻幂配对，可以保证每对至少有一个因子远离奇点。整个补弧对径向生成函数的相对上界为 $`O(y^2)`，小于中心弧的 $`y^{3/2}` 尺度。

{docstring eventually_norm_partitionGenFun_off_center_le}
