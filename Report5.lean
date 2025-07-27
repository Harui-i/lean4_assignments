import Mathlib.MeasureTheory.MeasurableSpace.Defs -- 可測空間,可測関数の定義
import Mathlib.MeasureTheory.OuterMeasure.Defs -- 外測度の定義
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef --測度の定義 (コレをimportしたら死ぬほどbuildに時間がかかるようになったw)
import Mathlib.Data.Nat.Pairing -- N × N → Nの全単射を作るために必要
import Mathlib.Data.Set.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Basic

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
      sorry
    ·
      -- goal: ∀ x ∈ A, {i | x ∈ E_all_seq i}.Infinite
      intro x hx
      -- E_all_seq iを展開
      simp_all only [E_all_seq]
      -- てか任意のnについて、∃ m s.t. E_{n, m} ∋ xみたいな感じのことが示せる。
      -- でnは可算無限個あるので、示せる
      -- TODO: コレを示す
      -- {i | x ∈ E (1 / 2)}
      sorry
