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
    -- We will use differentiability everywhere from C¹
    have h_diff_at : ∀ z ∈ Icc x2 y2, DifferentiableAt ℝ f z := by
      intro z hz
      exact (ContDiff.differentiable h_c1 (by norm_num)).differentiableAt

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

    -- First, show the interval lies inside the closed ball t, since t is convex and contains x1, y1.
    have h_Icc_subset_t : Icc x2 y2 ⊆ t := by
      have hseg : segment ℝ x1 y1 ⊆ t := h_t_is_convex.segment_subset hx1 hy1
      by_cases h : x1 ≤ y1
      · -- then x2 = x1, y2 = y1
        have hseg_eq : segment ℝ x1 y1 = Icc x2 y2 := by
          simp [segment_eq_Icc, x2, y2, h]
        simpa [hseg_eq]
          using hseg
      · -- y1 ≤ x1
        have h' : y1 ≤ x1 := le_of_lt (lt_of_not_ge h)
        have hx2 : x2 = y1 := by simp [x2, h']
        have hy2 : y2 = x1 := by simp [y2, h']
        have hseg_eq : segment ℝ x1 y1 = Icc x2 y2 := by
          -- use symmetry of segment
          have : segment ℝ y1 x1 = Icc x2 y2 := by
            simp [segment_eq_Icc, hx2, hy2, h']
          simpa [segment_symm] using this
        simpa [hseg_eq] using hseg

    -- Show the image s is nonempty and bounded above, as image of a compact set by a continuous function
    have hx_mem_t : x ∈ t := by
      -- x is the center of the closed ball of radius 1
      simp [t, Metric.mem_closedBall, dist_self]
    have hs_nonempty : s.Nonempty := ⟨‖deriv f x‖, ⟨x, hx_mem_t, rfl⟩⟩
    have hcont_deriv : Continuous fun y => deriv f y :=
      (h_c1.continuous_deriv (le_rfl))
    have hcont_norm : Continuous fun y => ‖deriv f y‖ := hcont_deriv.norm
    have hcompact_s : IsCompact s :=
      (h_t_is_compact.image hcont_norm)
    have hbdd : BddAbove s := hcompact_s.bddAbove

    -- Now bound the derivative on the interval by K = sSup s
    have h_bound' : ∀ z ∈ (Icc x2 y2), ‖deriv f z‖ ≤ K := by
      intro z hz
      have hz_t : z ∈ t := h_Icc_subset_t hz
      have hz_in_s : ‖deriv f z‖ ∈ s := ⟨z, hz_t, rfl⟩
      exact le_csSup hbdd hz_in_s

    have h_convex_set : Convex ℝ (Icc x2 y2) := by
      exact convex_Icc x2 y2

    have h_xs: x2 ∈ (Icc x2 y2) := by
      simp_all
      simp [x2]
      simp [y2]

    have h_ys: y2 ∈ (Icc x2 y2) := by
      simp [x2, y2]

    have h_final : ‖f y2 - f x2‖ ≤ K * ‖y2 - x2‖ := by
      -- Mean value inequality on a convex set using the bound on the ordinary derivative
      exact h_convex_set.norm_image_sub_le_of_norm_deriv_le h_diff_at h_bound' h_xs h_ys


    -- Finish by rewriting to norms using `dist_eq_norm` and using the mean value inequality above.
    have hxy_norm : ‖f x1 - f y1‖ ≤ K * ‖x1 - y1‖ := by
      by_cases hle : x1 ≤ y1
      · have hx2 : x2 = x1 := by simp [x2, hle]
        have hy2 : y2 = y1 := by simp [y2, hle]
        -- h_final currently reads with arguments (y2, x2)
        -- Adjust order on the left using `norm_sub_rev`.
        simpa [hx2, hy2, norm_sub_rev] using h_final
      · have hle' : y1 ≤ x1 := le_of_lt (lt_of_not_ge hle)
        have hx2 : x2 = y1 := by simp [x2, hle']
        have hy2 : y2 = x1 := by simp [y2, hle']
        simpa [hx2, hy2] using h_final
    -- Finish: turn norms into distances, then to extended distances.
    have hxy_dist : dist (f x1) (f y1) ≤ K * dist x1 y1 := by
      simpa [dist_eq_norm] using hxy_norm
    have hxy_edist : ENNReal.ofReal (dist (f x1) (f y1))
        ≤ ENNReal.ofReal (K * dist x1 y1) := ENNReal.ofReal_le_ofReal hxy_dist
    -- Rewrite the right-hand side to match the goal


    have hxy_edist2 : PseudoMetricSpace.edist (f x1) (f y1)
        ≤ ↑K_nn * PseudoMetricSpace.edist x1 y1 := by
        simp [PseudoMetricSpace.edist]
        -- goal: ↑⟨|f x1 - f y1|⟩ ≤ ↑K_nn * ↑⟨|x1 - y1|⟩


        sorry

    simpa [edist, ENNReal.ofReal_mul, dist_eq_norm, K_nn] using hxy_edist2
