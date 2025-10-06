-- filepath: /home/harui/math/learn_lean/anlysis3/Report1.lean
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-
レポート問題 No.1
S : 集合、F = { A ⊆ S | A は可算 ∨ S \ A は可算 }
(1) F が σ-加法族である
(2) Fは有限部分集合族が生成する σ-加法族に他ならない
-/
variable {α : Type*} (S : Set α)

namespace Report1

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


-- (2) 有限集合族が生成する σ-加法族に他ならない

-- filepath: /home/harui/math/learn_lean/anlysis3/Report1.lean
section generatedByFinite
open MeasurableSpace Set

-- our generating family: all finite subsets of α
def gen : Set (Set α) := { s | s.Finite }

-- ① generateFrom gen ⊆ F_sigmaAlgebra
lemma gen_le_F : generateFrom gen ≤ F_sigmaAlgebra := by
  apply generateFrom_le; rintro s hs; dsimp [gen]
  -- a finite set is countable
  change s ∈ F; left; exact hs.countable

-- ② F_sigmaAlgebra ⊆ generateFrom gen
lemma F_le_gen : F_sigmaAlgebra ≤ generateFrom gen := by
  intro s hs; dsimp [MeasurableSet, gen] at hs ⊢
  rcases hs with hc | hcc
  · -- case s.Countable
    rcases eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · -- s = ∅
      exact GenerateMeasurable.empty
    · -- enumerate s by a surjection e : ℕ ↠ {y // y ∈ s}
      rcases exists_surjective_nat { y // y ∈ s } ⟨⟨x,hx⟩⟩ with ⟨e, he⟩
      let f : ℕ → Set α := fun n => {(e n).val}
      have hf : ∀ n, f n ∈ gen := by intro n; dsimp [gen]; exact Set.Finite.singleton _
      -- ⋃ n, {e n} = s
      have : (⋃ n, f n) = s := by
        ext y; constructor
        · rintro ⟨n, hy⟩; dsimp [f] at hy; simpa using hy
        · intro hy; rcases he ⟨y,hy⟩ with ⟨n, rfl⟩; exact ⟨n, rfl⟩
      -- now s ∈ generateFrom gen
      rwa [this] at GenerateMeasurable.iUnion f hf
  · -- case (sᶜ).Countable
    -- then sᶜ is generated in the same way, and we close under complement
    apply GenerateMeasurable.compl
    -- build sᶜ by a countable ⋃ of singletons
    rcases eq_empty_or_nonempty sᶜ with rfl | ⟨x, hx⟩
    · -- sᶜ = ∅ ⇒ s = univ but ∅ is finite so handled by .empty above
      exact GenerateMeasurable.empty
    · rcases exists_surjective_nat { y // y ∈ sᶜ } ⟨⟨x,hx⟩⟩ with ⟨e, he⟩
      let g : ℕ → Set α := fun n => {(e n).val}
      have hg : ∀ n, g n ∈ gen := by intro n; dsimp [gen]; exact Set.Finite.singleton _
      have : (⋃ n, g n) = sᶜ := by
        ext y; constructor
        · rintro ⟨n, hy⟩; dsimp [g] at hy; simpa using hy
        · intro hy; rcases he ⟨y,hy⟩ with ⟨n, rfl⟩; exact ⟨n, rfl⟩
      rwa [this] at GenerateMeasurable.iUnion g hg

-- conclude equality
theorem F_generatedByFinite : F_sigmaAlgebra = generateFrom gen :=
  le_antisymm F_le_gen gen_le_F

end generatedByFinite

end Report1
