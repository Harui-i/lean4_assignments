import Mathlib.Order.SymmDiff
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable

variable {α : Type}

/-
解析学Cレポート問題 No. 2
問1 集合 A, Bに対し、

A∆B = (A \ B) ∪ (B \ A)
と定め、A,Bの対称差と呼ぶ。次の(a)-(e)が成り立つことを示しなさい。
ただし、A,B,Cは任意の集合とし、(A_n), (B_n)は任意の集合列とする。

(a): A∆B = B∆A
(b): (A∆B)∆C = A∆(B∆C)
(c): A∆A = ∅, A∆∅ = A
(d): (A∆B)∩C = (A∩C)∆(B∩C)
(e): (⋃ n, A_n)∆(⋃ n, B_n) ⊆ ⋃ n, (A_n∆B_n)
-/

open Set
open scoped symmDiff

section report2
variable {A B : Set α}

/-- (a) symmetric difference is commutative. -/
-- (a): A∆B = B∆A
theorem symmdiff_communitative (A B : Set α) : A ∆ B = B ∆ A := by
  apply Subset.antisymm
  ·
    -- Goal: A
    intro x hx
    rewrite [symmDiff] at hx
    rewrite [symmDiff]
    -- hx: x ∈ A \ B ⊔ A \ B
    -- Goal: x ∈ B \ A ⊔ A \ B
    rcases hx with h1 | h2
    ·
      -- h1: x ∈ A \ B
      right
      exact h1
    ·
      left
      exact h2
  ·
    -- Goal: B ∆ A ⊆ A ∆ B
    intro x hx
    rewrite [symmDiff] at hx
    rewrite [symmDiff]

    rcases hx with h1 | h2
    ·
      right
      exact h1
    ·
      left
      exact h2

-- (b): (A∆B)∆C = A∆(B∆C)
theorem symmdiff_associative (A B C : Set α) : (A ∆ B) ∆ C = A ∆ (B ∆ C) := by
  apply Subset.antisymm
  ·
    -- Goal: A ∆ B ∆ C ⊆ A ∆ B ∆ C
    intro x hx
    rewrite [symmDiff] at hx
    rewrite [symmDiff]
    -- hx: x ∈ A ∆ B \ C ⊔ C \ A ∆ B
    rcases hx with h1 | h2
    ·
      -- h1: x ∈ A \ B ⊔ A \ B
      rewrite [symmDiff] at h1
      rewrite [symmDiff]
      -- h1: x ∈ (A \ B ⊔ B \ A) \ C
      -- Goal: x ∈ A \ (B \ C ⊔ C \ B)

      rewrite [mem_diff] at h1

      simp_all
    ·
      simp_all
      rewrite [symmDiff] at h2
      rewrite [symmDiff]
      simp_all
      -- h2: x ∈ C ∧ (x ∈ A → x ∈ B) ∧ (x ∈ B → x ∈ A)
      have h2rl : (x ∈ A → x ∈ B) := h2.right.left
      have h2rr : (x ∈ B → x ∈ A) := h2.right.right
      simp_all
      by_cases ha: x ∈ A
      ·
        left
        exact And.intro ha (h2rl ha)
      ·
        right
        constructor
        ·
          -- goal: x∉B
          have h2rrc : x∉A → x∉B := by
            simp_all
          exact h2rrc ha
        ·
          exact ha

  ·
    -- Goal: A ∆ B ⊆ A ∆ B ∆ C
    intro x hx
    rewrite [symmDiff] at hx
    rewrite [symmDiff]

    rcases hx with h1 | h2
    ·
      rewrite [symmDiff] at h1
      rewrite [symmDiff]
      simp_all

      by_cases h3: x ∈ B
      ·
        right
        have h4: x ∈ C := h1.2.1 h3
        exact And.intro h4 h3
      ·
        -- neg
        left
        have h4: x ∈ C → x ∈ B := h1.2.2
        -- h4の対偶をとる
        have h5: x ∉ B → x ∉ C := by
          simp_all

        exact And.intro h3 (h5 h3)
    ·
      rewrite [symmDiff] at h2
      rewrite [symmDiff]
      simp_all



-- (c): A∆A = ∅, A∆∅ = A
theorem symmdiff_empty (A: Set α) : A ∆ A = ∅ := by
  -- 集合の等式を ⊆ と ⊇ にわけて示す
  apply Subset.antisymm
  ·
    -- Goal: A ∆ A ⊆ ∅
    intro x hx  -- x ∈ A ∆ A という仮定をhxという名前でとる。
    rewrite [symmDiff] at hx --
    -- Goal: x  ∈ ∅
    -- hx: x ∈ A \ A ⊔ A \ A
    -- hxをばらす
    rcases hx with h1 | h2
    ·
      -- h1: x ∈ A \ A
      -- A \ A = ∅
      -- diff_self: A \ A = ∅
      rewrite [diff_self] at h1
      exact h1
    ·
      -- h2もh1と全く同じ
      rewrite [diff_self] at h2
      exact h2
  ·
    -- Goal: ∅ ⊆ A ∆ A
    intro x hx
    rewrite [symmDiff] -- GoalをsymmDiffの定義をつかって書き換える
    left  -- Goalのleftを証明する
    rewrite [diff_self]
    exact hx

theorem symmdiff_empty2 (A: Set α) : A ∆ ∅ = A := by
  -- 集合の等式を ⊆ と ⊇ にわけて示す
  apply Subset.antisymm
  ·
    -- Goal: A ∆ ∅ ⊆ A
    intro x hx
    rewrite [symmDiff] at hx
    -- hx: x ∈ A \ ∅ ⊔ ∅ \ A
    rcases hx with h1 | h2
    ·
      -- h1: x ∈ A \ ∅
      -- Goal: x ∈ A
      rewrite [diff_empty] at h1
      exact h1
    ·
      --h2: x ∈ ∅ \ A
      rewrite [mem_diff] at h2
      -- h2: x ∈ ∅ ∧ x ∉ A
      -- Goal: x ∈ A
      have h2l : x ∈ ∅ := h2.left
      -- 背理法をする
      by_contra
      -- x ∈ ∅をつかってFalseを導きたい
      -- Goal: False
      rewrite [mem_empty_iff_false] at h2l
      exact h2l

  ·
    -- Goal: A ⊆ A ∆ ∅
    intro x hx
    rewrite [symmDiff]
    left
    -- Goal: x ∈ A \ ∅
    rewrite [diff_empty]
    exact hx

-- (d): (A∆B)∩C = (A∩C)∆(B∩C)

theorem symmdiff_intersection (A B C : Set α) : (A ∆ B) ∩ C = (A ∩ C) ∆ (B ∩ C) := by
  apply Subset.antisymm
  ·
    -- (A∆B)∩C ⊆ (A∩C)∆(B∩C)を示す
    -- Goal: A ∆ B ∩ C ⊆ (A ∩ C) ∆ (B ∩ C)
    intro x hx
    -- hx: x ∈ A ∆ B ∩ C
    -- Goal: x ∈ (A ∩ C) ∆ (B ∩ C)
    rewrite [symmDiff] at hx
    rewrite [symmDiff]
    -- hx: x ∈ (A \ B ⊔ B \ A) ∩ C
    have hxl : x ∈ (A \ B ⊔ B \ A) := hx.left
    have hxr : x ∈ C := hx.right

    rcases hxl with h1 | h2
    ·
      -- h1 : x ∈ A \ B
      rewrite [mem_diff] at h1
      -- h1: x ∈ A ∧ x ∉ B
      left
      -- Goal: x ∈ (A ∩ C) \ (B ∩ C)
      rewrite [mem_diff]
      -- Goal: x ∈ A ∩ C ∧ x ∉ B ∩ C
      rewrite [mem_inter_iff]
      rewrite [mem_inter_iff]
      -- Goal: (x ∈ A ∧ x ∈ C) ∧ ¬(x ∈ B ∧ x ∈ C)
      -- Goalの左側はかんたん
      -- 右側を示す
      have gr: ¬(x ∈ B ∧ x ∈ C) := by
        push_neg
        intro h3
        have h1r: x ∉ B := h1.right
        by_contra
        -- h3: x ∈ B
        -- h1r: x ∉ B
        -- Goal: False
        -- p ∧ ¬p ↔ Falseという定理を右から左に使う
        rewrite [←and_not_self_iff]
        exact And.intro h3 h1r

      exact And.intro (And.intro h1.left hxr) gr
    ·
      -- h2: x ∈ B \ A
      right
      -- Goal: x ∈ (B ∩ C) \ (A ∩ C)
      rewrite [mem_diff]
      -- Goal: x ∈ B ∩ C ∧ x ∉ A ∩ C
      -- Goalの左側はかんたんなので右側を示す
      have gr: x ∉ A ∩ C := by
        -- hxr: x ∈ C
        -- h2 : x ∈ B \ A
        -- Goal: x ∉ A ∩ C
        rewrite [mem_inter_iff]
        push_neg
        -- Goal: x ∈ A → x ∉ C
        intro ha
        rewrite [mem_diff] at h2
        have h2r : x ∉ A := h2.right
        by_contra
        -- ha: x ∈ A
        -- h2r: x ∉ A
        -- Goal: False
        -- p ∧ ¬p ↔ Falseという定理を右から左に使う
        rewrite [←and_not_self_iff]
        exact And.intro ha h2r

      have gl: x ∈ B ∩ C := by
        rewrite [mem_inter_iff]
        exact And.intro h2.left hxr

      exact And.intro gl gr
  ·
    -- (A∩C)∆(B∩C) ⊆ (A∆B)∩Cを示す
    intro x hx
    rewrite [symmDiff] at hx
    rewrite [symmDiff]
    rcases hx with h1 | h2
    ·
      -- h1: x ∈ A ∩ C
      rewrite [mem_diff] at h1
      have gr: x ∈ C := h1.left.right
      have gl: x ∈ (A \ B ⊔ B \ A) := by
        left
        rewrite [mem_diff]
        -- h1: x ∈ A ∩ C ∧ x ∉ B ∩ C
        have h1r: x ∉ B ∩ C := h1.right
        rewrite [mem_inter_iff] at h1r
        push_neg at h1r
        have gr2: x ∉ B := by
          -- h1r: x ∈ B → x ∉ C
          -- h1rの対偶をとる
          contrapose h1r
          -- ¬ x ∉ B
          push_neg
          push_neg at h1r
          exact And.intro h1r gr

        have gl : x ∈ A := h1.left.left
        exact And.intro gl gr2

      exact And.intro gl gr
    ·
      -- h2: x ∈ (B ∩ C) \ (A ∩ C)
      -- Goal: x ∈ (A \ B ⊔ B \ A) ∩ C
      have gr : x ∈ C := h2.left.right
      have gl : x ∈ (A \ B ⊔ B \ A) := by
        right
        rewrite [mem_diff]
        -- h2: x ∈ B ∩ C ∧ x ∉ A ∩ C
        have h2r: x ∉ A ∩ C := h2.right
        rewrite [mem_inter_iff] at h2r
        push_neg at h2r
        have gr2: x ∉ A := by
          -- h2r: x ∈ A → x ∉ C
          -- h2rの対偶をとる
          contrapose h2r
          -- ¬ x ∉ A
          push_neg
          push_neg at h2r
          exact And.intro h2r gr

        have gl1 : x ∈ B := h2.left.left
        exact And.intro gl1 gr2

      exact And.intro gl gr

-- (e): (⋃ n, A_n)∆(⋃ n, B_n) ⊆ ⋃ n, (A_n∆B_n)
-- ⋃で、expected tokenと怒られる
-- (e): (⋃ n, Aₙ) ∆ (⋃ n, Bₙ) ⊆ ⋃ n, (Aₙ ∆ Bₙ)

theorem symmdiff_Union_subset {ι : Type*} (A B : ι → Set α) :
    (⋃ i, A i) ∆ (⋃ i, B i) ⊆ ⋃ i, (A i ∆ B i) := by
  intro x hx
  -- hx: x ∈ (⋃ i, A i) ∆ ⋃ i, B i
  -- Goal: x ∈ ⋃ i, A i ∆ B i
  rewrite [symmDiff] at hx
  rewrite [mem_iUnion]
  -- Goal: ∃ i, x ∈ A i ∆ B i
  rcases hx with h1 | h2
  ·
    -- h1: x ∈ (⋃ i, A i) \ ⋃ i, B i
    rewrite [mem_diff] at h1
    -- h1: x ∈ ⋃ i, A i ∧ x ∉ ⋃ i, B i
    rewrite [mem_iUnion] at h1
    rewrite [mem_iUnion] at h1
    push_neg at h1
    -- h1: (∃ i, x ∈ A i) ∧ ∀ (i : ι), x ∉ B i
    obtain ⟨i, h1l⟩ := h1.left
    -- h1l: x ∈ A i
    -- x ∈ A i ∆ B iを示したい
    -- x ∈ A i ∧ x ∉ B iを示せばいい
    have h3: x ∉ B i := h1.right i
    have h4: x ∈ A i ∆ B i := by
      rewrite [symmDiff]
      -- Goal: x ∈ A i \ B i ⊔ B i \ A i
      left
      rewrite [mem_diff]
      exact And.intro h1l h3


    -- Goal: ∃ i, x ∈ A i ∆ B i
    -- ∃型の命題で実際に構成できた
    exact ⟨i, h4⟩
  ·
    rewrite [mem_diff] at h2
    rewrite [mem_iUnion] at h2
    rewrite [mem_iUnion] at h2
    push_neg at h2
    -- h2: (∃ i, x ∈ B i) ∧ ∀  (i : ι), x ∉ A i
    obtain ⟨i, h2l⟩ := h2.left
    have h3: x ∈ A i ∆ B i := by
      rewrite [symmDiff]
      -- Goal: x ∈ A i \ B i ⊔ B i \ A i
      right
      rewrite [mem_diff]
      exact And.intro h2l (h2.right i)
    -- Goal: ∃ i, x ∈ A i ∆ B i
    exact ⟨i, h3⟩

end report2
