import Mathlib.Order.SymmDiff
import Mathlib.Data.Set.Basic

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
end report2
