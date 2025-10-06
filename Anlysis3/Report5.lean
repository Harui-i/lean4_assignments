import Mathlib.MeasureTheory.MeasurableSpace.Defs -- 可測空間,可測関数の定義
import Mathlib.MeasureTheory.OuterMeasure.Defs -- 外測度の定義
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef --測度の定義 (コレをimportしたら死ぬほどbuildに時間がかかるようになったw)
import Mathlib.Data.Nat.Pairing -- N × N → Nの全単射を作るために必要
import Mathlib.Data.Set.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.Normed.Field.Basic -- 等比級数に必要
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory


section report5

/-
問1
Sを集合とし、F_0をSにおける有限加法族とする。μ_0を有限加法族 F_0上の完全加法的測度とする。 Sにおける外測度μ^* を次のように定義する。
μ^*(A) = inf {Σ_{i=1}^∞ μ(E_i) | E_1, E_2, ... ∈ F_0, A ⊆ ⋃_{i=1}^∞ E_i} (A: 集合, A ⊆ S)

Aに対する条件(a)と(b)が同値であることを示しなさい
(a) μ^*(A) = 0
(b) ある列 E_1, E_2, ... ∈ F_0 が存在して、A ⊆ ⋃_{i=1}^∞ E_i かつ Σ_{i=1}^∞ μ(E_i) < ∞ かつ ∀ x ∈ A に対して x ∈ E_i となる i が無限に存在する
-/

-- 1. μ^* の定義

-- F₀が有限加法族であることの条件
def IsFiniteAlgebra (S : Type*) (F₀ : Set (Set S)) : Prop :=
  ∅ ∈ F₀ ∧
  (∀ A, A ∈ F₀ → Aᶜ ∈ F₀) ∧
  (∀ A B, A ∈ F₀ → B ∈ F₀ → A ∪ B ∈ F₀)

-- μ₀が完全加法的測度であることの条件
-- ENNReal: Extended Non-negative Real Numbers. [0, ∞]みたいな

-- 外測度μ^*の定義
-- μ^*(A) = inf {Σ_{i=1}^∞ μ(E_i) | E_1, E_2, ... ∈ F_0, A ⊆ ⋃_{i=1}^∞ E_i} (A: 集合, A ⊆ S)
-- noncomputable: 計算可能ではないことを示す。
-- https://lean-ja.github.io/lean-by-example/Modifier/Noncomputable.html
-- 下の定式化が inf{..}に実はなっている！
-- ⨅という記号はindexed infimumを表す記号である。
-- fはF₀の元の列を(ℕ → Set Sの写像という形で)fで取っていて, それが被覆であることを条件としている
-- てかこれは、外測度の別定義で、mathlibのMeasureTheory.OuterMeasure.OfFunctionにある

variable {α : Type*} {F₀ : Set (Set α)} {μ₀ : Set α → ENNReal}

noncomputable def mustar (α : Type*) (F₀ : Set (Set α)) (μ₀ : Set α → ENNReal) (A : Set α) : ENNReal :=
  ⨅ (f : ℕ → Set α) (_ : ∀ n, f n ∈ F₀) (_ : A ⊆ ⋃ n, f n), (∑' n, μ₀ (f n))


-- Mathlibでは外測度は以下のように定義されている on MeasureTheory.OuterMeasure.Defs
/-
structure OuterMeasure (α : Type*) where
  /-- Outer measure function. Use automatic coercion instead. -/
  protected measureOf : Set α → ℝ≥0∞
  protected empty : measureOf ∅ = 0
  protected mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
  protected iUnion_nat : ∀ s : ℕ → Set α, Pairwise (Disjoint on s) →
    measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i)
-/

-- (a) μ^*(A) = 0の主張の定式化
def prop_a (α: Type*) (F₀ : Set (Set α)) (μ₀ : Set α → ENNReal) (A : Set α) : Prop :=
  mustar α F₀ μ₀ A = 0

open scoped ENNReal

--(b) ある列 E_1, E_2, ... ∈ F_0 が存在して、A ⊆ ⋃_{i=1}^∞ E_i かつ Σ_{i=1}^∞ μ(E_i) < ∞ かつ ∀ x ∈ A に対して x ∈ E_i となる i が無限に存在する
def prop_b (α: Type*) (F₀ : Set (Set α)) (μ₀ : Set α → ENNReal) (A : Set α) : Prop :=
  ∃ (E : ℕ → Set α), (∀ i, E i ∈ F₀) ∧
  A ⊆ ⋃ i, E i ∧
  (∑' i, μ₀ (E i)) < ∞ ∧
  ∀ x ∈ A, {i | x ∈ E i}.Infinite


-- (a) → (b)
lemma a_to_b (α : Type*) (F₀ : Set (Set α)) (hF₀: IsFiniteAlgebra α F₀)  (μ₀ : Set α → ENNReal) (A : Set α)
  (h : prop_a α F₀ μ₀ A) : prop_b α F₀ μ₀ A := by
  rw [prop_a] at h
  rw [prop_b]
  rw [mustar] at h

  -- h: ⨅ f, ⨅ (_ : ∀ (n : ℕ), f n ∈ F₀), ⨅ (_ : A ⊆ ⋃ n, f n), ∑' (n : ℕ), μ₀ (f n) = 0
  -- infimumが0であることから、任意の正数εに対してε未満の値を取る列が存在することを示す

  have forall_eps_exist_E_seq : ∀ ε : ℝ, 0 < ε → ∃ (E : ℕ → Set α), (∀ i, E i ∈ F₀) ∧
    A ⊆ ⋃ i, E i ∧
    (∑' i, μ₀ (E i)) < ENNReal.ofReal ε := by
    intro ε hε

    -- h を使って、infimum が 0 ということから ε 未満の値があることを示す
    have h_pos : (0 : ENNReal) < ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_pos]
      exact hε

    -- infimum が 0 で、0 < ENNReal.ofReal ε だから、infimum < ENNReal.ofReal ε
    have h_lt : mustar α F₀ μ₀ A < ENNReal.ofReal ε := by
      --conv について: https://aconite-ac.github.io/theorem_proving_in_lean4_ja/conv.html
      conv_lhs => rw [mustar]
      rw [h]
      exact h_pos

    -- mustar の定義を展開
    rw [mustar] at h_lt

    -- iInf_lt_iff を段階的に適用
    rw [iInf_lt_iff] at h_lt
    obtain ⟨f, hf_lt⟩ := h_lt
    rw [iInf_lt_iff] at hf_lt
    obtain ⟨hf_mem, hf_lt2⟩ := hf_lt
    rw [iInf_lt_iff] at hf_lt2
    obtain ⟨hf_subset, hf_sum⟩ := hf_lt2
    exact ⟨f, hf_mem, hf_subset, hf_sum⟩

  -- forall_eps_exist_E_seqを使って、列E_1, E_2, ...を構築
  choose E hE using forall_eps_exist_E_seq

  -- 1 / 2^nは正の数である
  have two_pow_n_inv_of_pos : ∀ n, (0: ℝ) < (1: ℝ) / (2^n : ℝ) := by
    intro n
    simp_all only [one_div, inv_pos, Nat.ofNat_pos, pow_pos]


  --let E_n := fun (n : ℕ)  => E ((1 / 2^n) : ℝ) (two_pow_n_inv_of_pos n) n
  -- Σ' m, μ₀ (E_n m) < 1 / 2^n となるような構成ができるのでそれを使って証明するアプローチ
  -- E_n は ℕ → Set α
  -- let G := ⋃ n, E_n n
  -- こう定義しただけじゃGは列じゃない...
  -- N × N → Nの全単射は結構簡単に作れるから、その逆写像(gとする)を使って、
  -- G_n := E_n (g n).1 (g n).2 みたいにすると, ℕ → Set αの列になる
  -- あ、MathlibのNat.paringってのを使うといいらしい

  -- E_all_seq iについて考える
  -- n := (unpair i).1
  -- m := (unpair i).2
  -- とすると、 E_all_seq i := E_n n m
  let E_all_seq : ℕ → Set α := fun i =>
    E ((1 / 2^(Nat.unpair i).1) : ℝ) (two_pow_n_inv_of_pos (Nat.unpair i).1) (Nat.unpair i).2

  use E_all_seq
  constructor
  ·
    -- goal: ∀ (i : ℕ), E_all_seq i ∈ F₀
    intro i
    -- E_all_seq iを展開
    simp_all only [E_all_seq] -- solved
  ·
    constructor
    -- goal: A ⊆ ⋃ i, E_all_seq i
    intro x hx
    simp_all only [E_all_seq]
    rewrite [Set.mem_iUnion]
    -- goal: ∃ i, x ∈ E (1 / 2^(unpair i).1) (two_pow_n_inv_of_pos (unpair i).1 : 0 < 1 / 2^(unpair i).1) (unpair i).2
    -- たぶん hEを使えばいける
    -- hE: ∀ (i : ℕ), E i ∈ F₀ ∧ A ⊆ ⋃ i, E i ∧ (∑' i, μ₀ (E i)) < ENNReal.ofReal ε
    -- ここで、nはどれを使ってもいいからn=1を使う
    -- で、E_1 は E_{1,1}, E_{1,2}, みたいな列になっていて、
    -- E_{1, m}であってx ∈ E_{1, m}となるmがある。
    -- そんな(1,m)からunpairしてiを作ればいい。

    have hE1_contains_x : ∃ m : ℕ, x ∈ E (1 / 2^1) (two_pow_n_inv_of_pos 1) m := by
      -- goal: ∃ m, x ∈ E (1 / 2^1) (two_pow_n_inv_of_pos 1) m
      have hhoge := (hE (1 / 2^1) (two_pow_n_inv_of_pos 1)).right.left
      -- hhoge: A ⊆ ⋃ i, E (1 / 2^1) (two_pow_n_inv_of_pos 1) i
      -- これを ∀ y ∈ A, ...みたいに言い換えたい
      rewrite [Set.subset_def] at hhoge
      -- hhoge: ∀ x ∈ A, x ∈ ⋃ i, E (1 / 2^1) (two_pow_n_inv_of_pos 1) i
      have hhoge2 := hhoge x hx
      rewrite [Set.mem_iUnion] at hhoge2
      obtain ⟨m, hm⟩ := hhoge2
      use m

    obtain ⟨m, hm⟩ := hE1_contains_x
    use Nat.pair 1 m

    rewrite [Nat.unpair_pair]
    -- goal: x ∈ E (1 / 2 ^ (1, m).1) two_pow_n_inv_of_pos (1, m).1 : 0 < 1 / 2 ^ (1, m).1 (1, m).2
    -- (1,m).1 = 1
    -- (1,m).2 = mを使って書き換える
    have pair_1_m_first : (1, m).1 = 1 := by
      rfl
    have pair_1_m_second : (1, m).2 = m := by
      rfl

    rw [pair_1_m_first]
    rw [pair_1_m_second]
    -- goal: x ∈ E (1 / 2 ^ 1) (two_pow_n_inv_of_pos 1) m
    -- これで hm : x ∈ E (1 / 2^1) (two_pow_n_inv_of_pos 1) m と一致する
    exact hm

    -- goal: Σ' (i : ℕ) μ₀ (E_all_seq i) < ⊤ ∧ ∀ x ∈ A, {i | x ∈ E_all_seq i}.Infinite
    constructor
    ·
      -- goal: Σ' (i : ℕ) μ₀ (E_all_seq i) < ⊤
      -- E_all_seq i の和だけど、和の順序を変えて Σ' (n : ℕ) Σ' m μ₀ (E n m) にしてもよいことを示せたら、
      -- Σ' m μ₀ (E n m) < 1 / 2^n であることがわかるので、いろいろやれば示せる
      -- でも可算無限個の和なのに順序を変えていいのか?
      -- 非負だからええか
      -- まず補題として、Σ' i , μ₀ (E_all_seq i) = Σ' n, Σ' m μ₀ (E n m) であることを示す
      -- E: (ε : ℝ) → 0 < ε → ℕ → Set α
      -- E_all_seq i = E (1/2^(unpair i).1) (proof) (unpair i).2
      -- なので、この和をΣ' n, Σ' m μ₀ (E (1/2^n) (proof) m) に変形したい

      -- 各nに対する1/2^nが正であることを定義
      have h1_div_2_pow_n_gt_0 : ∀ n : ℕ, (0 : ℝ) < (1 : ℝ) / (2^n : ℝ) := by
        intro n
        simp_all only [one_div, inv_pos, Nat.ofNat_pos, pow_pos]


      have h_nmsum_finite: ∑' (n : ℕ), ∑' (m : ℕ), μ₀ (E ((1 / 2^n) : ℝ) (h1_div_2_pow_n_gt_0 n) m) < ⊤ := by
        -- 各nについて ∑' m, μ₀ (E (1/2^n) _ m) < ENNReal.ofReal (1/2^n) が成り立つ
        -- これは hE の性質から得られる
        have h_bound_n : ∀ n : ℕ, ∑' (m : ℕ), μ₀ (E ((1 / 2^n) : ℝ) (h1_div_2_pow_n_gt_0 n) m) < ENNReal.ofReal (1 / 2^n) := by
          intro n
          exact (hE ((1 / 2^n) : ℝ) (h1_div_2_pow_n_gt_0 n)).right.right

        -- ∑' n, ∑' m, μ₀ (E (1/2^n) _ m) ≤ ∑' n, ENNReal.ofReal (1/2^n)
        have h_bound_total : ∑' (n : ℕ), ∑' (m : ℕ), μ₀ (E ((1 / 2^n) : ℝ) (h1_div_2_pow_n_gt_0 n) m) ≤
                            ∑' (n : ℕ), ENNReal.ofReal (1 / 2^n) := by
          apply ENNReal.tsum_le_tsum
          intro n
          exact le_of_lt (h_bound_n n)

        -- ∑' n, ENNReal.ofReal (1/2^n) は有限であることを示す
        have h_finite_sum : ∑' (n : ℕ), ENNReal.ofReal (1 / 2^n) < ⊤ := by
          -- 単純な上界を使った証明
          -- 各項について 1/2^n ≤ 1/2^0 = 1 for n ≥ 0
          -- さらに、n ≥ 1 では 1/2^n ≤ 1/2
          -- したがって ∑' n, ENNReal.ofReal (1/2^n) ≤ ENNReal.ofReal 1 + ∑' n ≥ 1, ENNReal.ofReal (1/2)
          -- しかし後者は発散するので、この方法は良くない

          -- より良いアプローチ: 比較判定法
          -- 十分大きなnに対して、1/2^n ≤ (2/3)^n など使えるが、複雑

          -- ここでは、実際のLean証明では等比級数の収束定理を使うべきだが、
          -- 今は構造を示すことが目的なので、基本的な不等式で上界を与える

          -- n = 0: 1/2^0 = 1
          -- n = 1: 1/2^1 = 1/2
          -- n = 2: 1/2^2 = 1/4
          -- ...
          -- 明らかに ∑_{n=0}^∞ 1/2^n = 2 < ∞

          -- ENNReal での対応する和も有限になる
          -- 厳密な証明には等比級数の定理が必要だが、ここでは省略
          have : ∑' (n : ℕ), ENNReal.ofReal (1 / 2^n) ≤ ENNReal.ofReal 2 := by
            -- この不等式は等比級数の理論から従う
            -- 実際の証明では Mathlib の等比級数定理を使用する
            -- mathlib4/Mathlib/Analysis/SpecificLimits
            -- theorem tsum_geometric_two : (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) = 2

            -- まず 1/2^n = (1/2)^n であることを示す
            have h_eq : ∀ n : ℕ, (1 / 2^n : ℝ) = ((1 : ℝ) / 2) ^ n := by
              intro n
              simp only [one_div, inv_pow]

            -- ∑' n, ENNReal.ofReal (1/2^n) = ∑' n, ENNReal.ofReal ((1/2)^n)
            have h_tsum_eq : ∑' (n : ℕ), ENNReal.ofReal (1 / 2^n) = ∑' (n : ℕ), ENNReal.ofReal (((1 : ℝ) / 2) ^ n) := by
              congr 1
              ext n
              rw [h_eq]

            rw [h_tsum_eq]

            -- ENNReal.ofReal_tsum_of_nonneg を使って、
            -- ∑' n, ENNReal.ofReal ((1/2)^n) = ENNReal.ofReal (∑' n, (1/2)^n)
            have h_ofReal_tsum : ∑' (n : ℕ), ENNReal.ofReal (((1 : ℝ) / 2) ^ n) = ENNReal.ofReal (∑' (n : ℕ), ((1 : ℝ) / 2) ^ n) := by
              rw [← ENNReal.ofReal_tsum_of_nonneg]
              · intro n
                apply pow_nonneg
                norm_num
              · exact summable_geometric_two

            rw [h_ofReal_tsum]

            -- tsum_geometric_two : (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) = 2 を使う
            rw [tsum_geometric_two]

          have h_2_lt_top : ENNReal.ofReal 2 < ⊤ := ENNReal.ofReal_lt_top
          exact lt_of_le_of_lt this h_2_lt_top

        exact lt_of_le_of_lt h_bound_total h_finite_sum

      have h_sum_eq : Σ' (i : ℕ), μ₀ (E_all_seq i) =
        ∑' (n : ℕ), ∑' (m : ℕ), μ₀ (E ((1 / 2^n) : ℝ) (h1_div_2_pow_n_gt_0 n) m) := by

        -- μ₀の定義から、非負。
        -- h_nmsum_infiniteから、右辺は有限
        -- 絶対収束する級数は順序を変えても値は変わらないので, h_sum_eqが成り立つ
        sorry


      -- goal: Σ' (i : ℕ), μ₀ (E_all_seq i) < ⊤
      --rw [h_sum_eq] --tactic 'rewrite' failed, equality or iff proof expected (i : ℕ) ×' μ₀ (E_all_seq i) = ∑' (n : ℕ) (m : ℕ), μ₀ (E (1 / 2 ^ n) ⋯ m)
      -- なんでh_sum_eqを使って書き換えられない???



    ·
      -- goal: ∀ x ∈ A, {i | x ∈ E_all_seq i}.Infinite
      intro x hx
      -- E_all_seq iを展開
      simp_all only [E_all_seq]

      -- 任意のnについて、∃ m s.t. x ∈ E((1/2^n), m) であることを示す
      have forall_n_exists_m : ∀ n : ℕ, ∃ m : ℕ, x ∈ E ((1 / 2^n) : ℝ) (two_pow_n_inv_of_pos n) m := by
        intro n
        have subset_property := (hE ((1 / 2^n) : ℝ) (two_pow_n_inv_of_pos n)).right.left
        rw [Set.subset_def] at subset_property
        have x_in_union := subset_property x hx
        rw [Set.mem_iUnion] at x_in_union
        exact x_in_union

      -- 各nに対してmを選ぶ
      choose m_of_n hm_of_n using forall_n_exists_m

      -- 任意のnについて、 Nat.pair n (m_of_n n) がこの集合に含まれることを示す
      have mem_for_all_n : ∀ n : ℕ, Nat.pair n (m_of_n n) ∈ {i | x ∈ E ((1 / 2^(Nat.unpair i).1) : ℝ) (two_pow_n_inv_of_pos (Nat.unpair i).1) (Nat.unpair i).2} := by
        intro n
        simp only [Set.mem_setOf]
        -- Nat.unpair (Nat.pair n (m_of_n n)) = (n, m_of_n n) を使う
        conv_lhs => rw [Nat.unpair_pair]
        simp only
        exact hm_of_n n

      -- 無限性を示すために、矛盾を導く
      by_contra h_finite
      push_neg at h_finite
      -- h_finite: Finite {i | x ∈ E (1 / 2 ^ (Nat.unpair i).1) ⋯ (Nat.unpair i).2}

      -- この有限集合をSとする
      let S := {i | x ∈ E ((1 / 2^(Nat.unpair i).1) : ℝ) (two_pow_n_inv_of_pos (Nat.unpair i).1) (Nat.unpair i).2}

      -- すべてのnについて Nat.pair n (m_of_n n) ∈ S
      have all_pairs_in_S : ∀ n : ℕ, Nat.pair n (m_of_n n) ∈ S := mem_for_all_n

      -- f: ℕ → ℕ を f(n) = Nat.pair n (m_of_n n) として定義
      let f : ℕ → ℕ := fun n => Nat.pair n (m_of_n n)

      -- fは単射
      have f_inj : Function.Injective f := by
        intro n1 n2 h_eq
        simp only [f] at h_eq
        have : (n1, m_of_n n1) = (n2, m_of_n n2) := by
          rw [← Nat.unpair_pair n1 (m_of_n n1), ← Nat.unpair_pair n2 (m_of_n n2), h_eq]
        exact (Prod.mk_inj.mp this).1

      -- Set.range f ⊆ S
      have range_subset : Set.range f ⊆ S := by
        intro i hi
        obtain ⟨n, hn⟩ := hi
        rw [← hn]
        simp only [f]
        exact all_pairs_in_S n

      -- S は有限なので Set.range f も有限
      have S_finite : Set.Finite S := by
        rwa [← Set.not_infinite]
      have range_finite : Set.Finite (Set.range f) := Set.Finite.subset S_finite range_subset

      -- しかし f が単射で定義域が無限なので、Set.range f は無限のはず
      -- これを示すために、任意の有限集合がSet.range fを覆わないことを示す

      -- ℕが無限集合であることを利用
      have nat_infinite : Set.Infinite (Set.univ : Set ℕ) := Set.infinite_univ

      -- fが単射なので、Set.range f も無限
      have range_infinite : Set.Infinite (Set.range f) := by
        -- Set.range f が有限だと仮定して矛盾を導く
        by_contra h_finite_range

        -- h_finite_range : ¬(Set.range f).Infinite
        -- これを Set.Finite に変換
        rw [Set.not_infinite] at h_finite_range
        -- h_finite_range : (Set.range f).Finite

        -- fが単射なので、ℕ から Set.range f への単射が存在する
        -- Set.range f を有限集合として扱える
        have range_fintype : Fintype (Set.range f) := Set.Finite.fintype h_finite_range

        -- ℕ から Set.range f への写像 g を定義
        let g : ℕ → Set.range f := fun n => ⟨f n, Set.mem_range_self n⟩

        -- g は単射
        have g_inj : Function.Injective g := by
          intro n1 n2 h_eq
          have : f n1 = f n2 := by
            have h_val : (g n1).val = (g n2).val := by
              rw [h_eq]
            simp only [g] at h_val
            exact h_val
          exact f_inj this

        -- g は全射でもある
        have g_surj : Function.Surjective g := by
          intro ⟨y, hy⟩
          obtain ⟨n, hn⟩ := hy
          use n
          simp only [g]
          ext
          exact hn

        -- g が単射全射なので、ℕ と Set.range f の間に濃度の対応がある
        -- しかし、Set.range f は有限で ℕ は無限なので矛盾

        -- 具体的に: 任意の自然数 k に対して、0, 1, ..., k-1 を g で移すと
        -- k 個の異なる要素が Set.range f に含まれる
        -- しかし、Set.range f は有限なので、ある上限がある

        -- Fintype.card を使った議論
        have card_le : ∀ n : ℕ, n ≤ Fintype.card (Set.range f) := by
          intro n
          -- {0, 1, ..., n-1} を g で移した像のサイズは n
          -- これが Set.range f に含まれるので、n ≤ |Set.range f|
          let s := Finset.range n
          have h1 : s.card = n := Finset.card_range n
          have h2 : (s.image (fun i => g i)).card = s.card := by
            rw [Finset.card_image_of_injective]
            exact g_inj
          have h3 : s.image (fun i => g i) ⊆ Finset.univ := Finset.subset_univ _
          rw [← h1, ← h2]
          exact Finset.card_le_card h3

        -- しかし、任意に大きな n を取れるので矛盾
        have : ∃ n : ℕ, n > Fintype.card (Set.range f) := by
          use Fintype.card (Set.range f) + 1
          norm_num

        obtain ⟨n, hn⟩ := this
        have : n ≤ Fintype.card (Set.range f) := card_le n
        linarith

      -- 矛盾: range_finite と range_infinite
      exact range_infinite range_finite
