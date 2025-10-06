-- 示したい定理:R上のC^1級関数は、R上でfは局所リプシッツ連続である
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Calculus.MeanValue -- 平均値の定理
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Analysis.Normed.Module.Convex -- convex_closedBall
open Set Metric

theorem C1_implies_LocallyLipschitz
    -- f は実数から実数への関数
    (f : ℝ → ℝ)
    -- h_c1 は f がC¹級であるという仮定
    (h_c1 : ContDiff ℝ 1 f) :
    -- 結論：f は局所リプシッツ連続である
    LocallyLipschitz f := by
    rw [LocallyLipschitz]
    -- x ∈ ℝ を任意に取る
    intro x
    -- Goal: ∃ K, ∃ t ∈ nhds x, LipschitzOnWith K f t
    -- LipschitzOnWithをバラす
    -- Unfold the definition of LipschitzOnWith
    simp only [LipschitzOnWith]
    -- Goal: ∃ K, ∃ t ∈ nhds x, ∀ {x : ℝ}, x ∈ t → ∀ {y : ℝ}, y ∈ t → dist (f x) (f y) ≤ ↑K * dist x y
    -- K: リプシッツ定数
    -- t∈ nhds x とは: xを含む何らかの開集合tが見つかる
    -- ここで、tはなんでもいいんだけど、とりあえず(x-1,x+1)にしとく
    -- とおもったものの、tを開区間にして、K=sup_t |f'|とすると、sup_t |f'|が存在するとは限らない
    -- (f'が有界とは限らないので。)
    let t := Metric.closedBall x 1
    have h_nhds : t ∈ nhds x := by
      rw [Metric.mem_nhds_iff]
      -- Goal: ∃ ε > 0, ball x ε ⊆ t
      simp [t]
      use 0.5
      constructor
      · linarith
      ·
        intro y hy
        -- goal: y ∈ closedBall x 1
        rw [Metric.mem_closedBall]
        -- hy: y ∈ ball x 0.5
        rw [Metric.mem_ball] at hy
        -- hy: dist y x < 0.5
        -- goal: dist y x ≤ 1
        linarith

    have h_t_is_compact : IsCompact t := by
      -- closedBallはコンパクト
      -- Mathlib.Topology.MetricSpace.ProperSpace で証明されている
      exact isCompact_closedBall x 1

    have h_t_is_convex : Convex ℝ t := by
      exact convex_closedBall x 1


     -- コンパクト集合 t 上の連続関数 ‖deriv f y‖ の値の集合を s とおく
    let s := (fun y => ‖deriv f y‖) '' t
    -- その集合の上限 (supremum) を K とする。
    -- コンパクト集合上の連続関数は有界なので、この K は有限の値となる。
    let K := sSup s
    -- 構成するKはNNReal(非負整数)なので,このKをNNRealに変換する
    let K_nn : NNReal := ⟨K, by
    -- Kが非負であることの証明
    apply Real.sSup_nonneg
    -- 集合sの元がすべて非負であることを示す
    rintro _ ⟨y, _, rfl⟩
    exact norm_nonneg _
    ⟩

    use K_nn -- ∃ を証明するために構成
    use t -- ∃ を証明するために構成
    use h_nhds
    -- Goal: ∀ {x : ℝ}, x ∈ t → ∀ {y : ℝ}, y ∈ t → dist (f x) (f y) ≤ ↑K_nn * dist x y
    intro x1 hx1
    intro y1 hy1

    let x2 := min x1 y1
    let y2 := max x1 y1

    -- Goal: edist (f x1) (f y1) ≤ ↑K_nn * edist x1 y1
    -- 平均値の定理はMathlibにある
     -- fが区間 [x2,y2] で微分可能であることを示す。C¹級なので当然成り立つ。
    have h_diff_on : DifferentiableOn ℝ f (Icc x2 y2) :=
      (ContDiff.differentiable h_c1 (by norm_num)).differentiableOn

    -- 平均値の定理（の不等式版）を適用して、Goalを直接証明する
    /-
    /-- The mean value theorem on a convex set in dimension 1: if the derivative of a function within
    this set is bounded by `C`, then the function is `C`-Lipschitz. Version with `derivWithin` -/
    theorem norm_image_sub_le_of_norm_derivWithin_le {C : ℝ} (hf : DifferentiableOn 𝕜 f s)
        (bound : ∀ x ∈ s, ‖derivWithin f s x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
        ‖f y - f x‖ ≤ C * ‖y - x‖ :=
      hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound xs
        ys
    -/
    -- 上の定理の文字 : このコードでの文字
    -- 𝕂 : ℝ
    -- f : f
    -- s : Icc x1 y1
    -- C : K

    have h_bound : ∀ z ∈ (Icc x2 y2), ‖derivWithin f (Icc x2 y2) z‖ ≤ K := by
      sorry

    have h_convex_set : Convex ℝ (Icc x2 y2) := by
      exact convex_Icc x2 y2

    have h_xs: x2 ∈ (Icc x2 y2) := by
      simp_all
      simp [x2]
      simp [y2]

    have h_ys: y2 ∈ (Icc x2 y2) := by
      simp [x2, y2]

    have h_final : ‖f y2 - f x2‖ ≤ K * ‖y2 - x2‖ := by
      exact Convex.norm_image_sub_le_of_norm_derivWithin_le h_diff_on h_bound h_convex_set h_xs h_ys

    sorry
