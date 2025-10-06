-- 示したい定理:R上のC^1級関数は、R上でfは局所リプシッツ連続である
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.ProperSpace

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
    use K_nn
    use t
    use h_nhds
    -- Goal: ∀ {x : ℝ}, x ∈ t → ∀ {y : ℝ}, y ∈ t → dist (f x) (f y) ≤ ↑K_nn * dist x y


    sorry
