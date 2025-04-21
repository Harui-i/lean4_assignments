import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

--set_option diagnostics true

/-
S : 集合、F = { A ⊆ S | A は可算 ∨ S \ A は可算 }
(1) F が σ-加法族である
-/
variable {α : Type*} (S : Set α)

/-- F の定義 -/
def F : Set (Set α) :=
  { A | A.Countable ∨ (Aᶜ).Countable }

-- (1) σ-加法族性
section sigmaAlgebra
open Set

-- 空集合が F に含まれることを示す
lemma empty_mem : (∅: Set α) ∈ F := by
  -- Goalは ∅ ∈ F S.
  -- ∈ F Sってなんだよ。
  -- Fは上で定義されている。

  rewrite [F]
  left
  exact countable_empty


-- 全体集合が F に含まれることを示す
/-
lemma univ_mem : (S : Set α) ∈ F := by
  -- Goalは S ∈ F S.
  constructor
  ·
    -- Goal は S.Countable ∨ (S \ S).Countable
    right
    -- Goalは (S \ S).Countable
    -- S \ S = ∅ を使ってrewrite
    rewrite [diff_self]
    -- Goalは ∅.Countable
    exact countable_empty
  ·
    -- Goalは S ⊆ S
    exact Subset.refl S
-/


-- Aᶜ も F に含まれることを示す
lemma compl_mem {A: Set α} (h : A ∈ F) : (Aᶜ) ∈ F := by
  -- h : A ∈ F S
  rewrite [F] at h
  -- Goalは A ∈ {A | A.Countable ∨ (S \ A).Countable}

  rcases h with h1 | h2

  -- A.Countable と Aᶜ.Countableで場合分け
  ·
    -- h1: A.Countable
    -- Goalは Aᶜ ∈ F
    rewrite [F]
    -- Goal は Aᶜ ∈ {A | A.Countable ∨ (S \ A).Countable}
    -- (Aᶜ)ᶜ = A.　ここで、 Aᶜᶜ がCountableだから、
    -- Aᶜ ∈ F.
    have h3: (Aᶜ)ᶜ.Countable := by
      -- Goalは A.Countable
      rewrite [compl_compl]
      exact h1

    right
    -- Goal: Aᶜᶜ.Countable
    exact h3

  ·
    -- Goal: Aᶜ ∈ F
    -- h2: Aᶜ.Countable
    rewrite [F]
    left
    exact h2


lemma Union_mem {f : ℕ → Set α} (h : ∀ n, f n ∈ F) : (⋃ n, f n) ∈ F := by
  -- Goal: ⋃ n, f n ∈ F
  -- h: ∀( n: ℕ), f n ∈ F
  rewrite [F] at h
  rewrite [F]
  -- h: ∀ (n : ℕ), f n ∈ {A | (A.Countable ∨ Aᶜ.Countable) }

  -- h の右側だけとっておく

  -- Goal: ⋃ n, f n ∈ {A | A.Countable ∨ (Aᶜ).Countable }
  -- ⋃ n, f nってなんやねん。 iUnionとかいうらしいが…
  rewrite [mem_setOf_eq]
  rewrite [compl_iUnion]
  -- Goal: ((⋃ n, f n).Countable ∨ (⋂ i, (f i)ᶜ).Countable)

  by_cases hAll_countable: ∀ n, (f n).Countable
  case pos =>
    -- hAll_countable:
    -- 可算個の集合の可算無限和は可算
    aesop
  case neg =>
    right -- Goal: (⋂ i, (f i)ᶜ).Countable
    push_neg at hAll_countable
    -- hAll_countable: ∃ n, ¬(f n).Countable
    obtain ⟨n1, hN⟩ := hAll_countable

    have hn1: f n1 ∈ {A | A.Countable ∨ (Aᶜ).Countable } := by
      -- Goal: f n ∈ {A | A.Countable ∨ (Aᶜ).Countable }
      -- h: ∀ (n : ℕ), f n ∈ {A | A.Countable ∨ (Aᶜ).Countable }
      exact h n1

    rewrite [mem_setOf_eq] at hn1

    have h2: ((f n1)ᶜ).Countable := by
      exact Or.resolve_left hn1 hN

    have h3: (⋂ i, (f i)ᶜ) ⊆ (f n1)ᶜ := by
      intro x
      intro h4
      -- h4: x ∈ ⋂ i, (f i)ᶜ
      -- Goal: x ∈ (f n1)ᶜ
      rewrite [mem_iInter] at h4
      exact h4 n1

    exact Set.Countable.mono h3 h2

-- (S, F)が可測空間であることを今まで示したlemmaから主張する

instance F_sigmaAlgebra: MeasurableSpace α where
  MeasurableSet' := fun A => A ∈ F
  measurableSet_empty := empty_mem
  measurableSet_compl := fun _A hA => compl_mem hA
  measurableSet_iUnion := fun _f hf => Union_mem hf

end sigmaAlgebra
