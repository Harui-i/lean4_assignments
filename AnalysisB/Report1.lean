-- 示したい定理:R上のC^1級関数は、R上でfは局所リプシッツ連続である
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Calculus.MeanValue -- 平均値の定理

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
    -- Goal: edist (f x1) (f y1) ≤ ↑K_nn * edist x1 y1
    -- 平均値の定理はnorm_image_sub_le_of_norm_deriv_leみたいな名前である
    /-
    -- ↓ Mathlib の定理
    /-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
      bounded by `C`, then the function is `C`-Lipschitz. Version with `HasDerivWithinAt`. -/
      theorem norm_image_sub_le_of_norm_hasDerivWithin_le {C : ℝ}
          (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s)
          (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖ :=
        Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
          (fun x hx => le_trans (by simp) (bound x hx)) hs xs ys
    -/
     -- fが区間 [x1,y1] で微分可能であることを示す。C¹級なので当然成り立つ。
    have h_diff_on : DifferentiableOn ℝ f (Icc x1 y1) :=
      (ContDiff.differentiable h_c1 (by norm_num)).differentiableOn

    -- 区間 [x1,y1] 内の任意の点 c で ‖deriv f c‖ ≤ K が成り立つことを示す
    have h_norm_le_K : ∀ c ∈ Icc x1 y1, ‖deriv f c‖ ≤ K := by
      intro c hc

      -- x1, y1 は t に含まれ、t は凸集合なので、c も t に含まれる。
      have hc_in_t : c ∈ t := by
        simp [Icc] at hc
        -- hc : x1 ≤ c ∧ c ≤ y1
        -- tがClosedBallなので明らかに c ∈ tだろうけど
        -- Goal: c ∈ t
        simp [t]
        sorry
      -- K は t 上での上限だったので、‖deriv f c‖ ≤ K が成立する。
      -- ‖deriv f c‖ ∈ s であることを示す
      have h_norm_in_s : ‖deriv f c‖ ∈ s := mem_image_of_mem _ hc_in_t
      -- 集合の元は上限以下である
      exact le_csSup (h_t_is_compact.isBounded_image h_deriv_cont.norm) h_norm_in_s -- error

    -- 平均値の定理（の不等式版）を適用して、Goalを直接証明する
    -- dist a b は ‖a - b‖ と定義されているので、この定理がそのまま使える
    exact norm_image_sub_le_of_norm_deriv_le h_diff_on h_norm_le_K ha hb
    sorry
