-- 示したい定理:R上のC^1級関数は、R上でfは局所リプシッツ連続である
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

open Set Metric

theorem C1_implies_LocallyLipschitz
    -- f は実数から実数への関数
    (f : ℝ → ℝ)
    -- h_c1 は f がC¹級であるという仮定
    (h_c1 : ContDiff ℝ 1 f) :
    -- 結論：f は局所リプシッツ連続である
    LocallyLipschitz f := by
    sorry -- TODO : 証明を書く
