-- filepath: /home/harui/math/learn_lean/anlysis3/Report1.lean
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-
レポート問題 No.1
S : 集合、F = { A ⊆ S | A は可算 ∨ S \ A は可算 }
(1) F が σ-加法族である
(2) 有限部分集合族が生成する σ-加法族に他ならない
-/
variable {α : Type*} (S : Set α)

namespace Report1

/-- F の定義 -/
def F : Set (Set α) :=
  { A | (A.Countable ∨ (S \ A).Countable) ∧ A ⊆ S }

-- (1) σ-加法族性
section sigmaAlgebra
open Set

-- 空集合が F に含まれることを示す
lemma empty_mem : (∅ : Set α) ∈ F S := by
  -- Goalは ∅ ∈ F S.
  -- ∈ F Sってなんだよ。
  -- Fは上で定義されている。

  --#check S -- S : Set α
  --#check F S -- F S : Set (Set α)
  --#check F -- Report1.F.{u_1} {α : Type u_1} (S: Set α) : Set (Set α)
  rewrite [F]
  have h1: ∅ ⊆ S := by
    exact empty_subset S

  have h2 : (∅: Set α).Countable := by
    exact countable_empty

  exact And.intro (Or.inl h2) h1


-- 全体集合が F に含まれることを示す
lemma univ_mem : (S : Set α) ∈ F S := by
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

-- S \ A も F に含まれることを示す
lemma compl_mem {A} (h : A ∈ F S) : (S \ A) ∈ F S := by
  -- h : A ∈ F S
  rewrite [F] at h
  have hl : A.Countable ∨ (S \ A).Countable := h.1
  have hr : A ⊆ S := h.2

  -- Goalは A ∈ {A | A.Countable ∨ (S \ A).Countable}

  rcases hl with h1 | h2

  · -- A.Countable ∨ (S \ A).Countable--
    -- Goalは S \ A ∈ F S
    rewrite [F]
    -- Goal は S \ A ∈ {A | A.Countable ∨ (S \ A).Countable}
    -- (S \ A) \ A = A.　ここで、 (S \ A) \ A がCountableだから、
    -- (S \ A) \in F S
    apply And.intro
    ·
      right
      rewrite [diff_diff_cancel_left]
      ·
        exact h1
      ·
        exact hr
    ·
      -- Goal は S \ A ⊆ S.
      intro x
      intro
      aesop

  ·
    -- Goal: S \ A ∈ F S
    rewrite [F]
    constructor
    ·
      -- Goal: (S \ A).Countable ∨ (S \ (S \ A)).Countable
      exact Or.inl h2
    ·
      -- GOal: S \ A ⊆ S
      intro x
      intro
      aesop


lemma Union_mem {f : ℕ → Set α} (h : ∀ n, f n ∈ F S) : (⋃ n, f n) ∈ F S := by
  by_cases H : (⋃ n, f n).Countable
  · left; exact H
  · right
    calc
      S \ ⋃ n, f n = ⋂ n, (S \ f n) := by simp [compl_Union]
      _ = ⋂ n, (S \ f n) : rfl
    -- 交わり側の可算性は各 S\f n が可算なことから
    have h' : ∀ n, (S \ f n).Countable := fun n =>
      (h n).elim (fun _ => by simpa [compl_compl] using (h n).elim id fun _ => by rfl)
                 fun c => c
    exact Countable.countable_iInter h'
    -- (Countable.countable_iInter は Mathlib4 で補題を探すか、自分でそっくり構成してください)
end sigmaAlgebra

/-- (2) 有限集合族が生成する σ-加法族に他ならない -/
section generatedByFinite
open MeasurableSpace

/-- Finset α → Set α の像で生成 -/
def G : MeasurableSpace α := generateFrom (Set.range fun t : Finset α => (t : Set α))

lemma finset_mem (t : Finset α) : (↑t : Set α) ∈ F S := by
  -- 有限集合は可算
  left; exact t.finite_toSet.countable

lemma G_le_F : G ≤ (MeasurableSpace.mkOfClosure _ rfl : MeasurableSpace α) := by
  -- generateFrom_le を使って G ≤ F になる
  refine generateFrom_le ?_; intro t ht
  rcases ht with ⟨u, rfl⟩
  exact finset_mem S u

lemma F_le_G : (MeasurableSpace.mkOfClosure _ rfl) ≤ G := by
  -- F 自身が σ-加法族なので生成空間に含まれる
  intro A hA
  induction hA using GenerateMeasurable.induction_on with
  | basic A h A_in => exact generateFrom.basic _ _ A_in
  | empty => exact generateFrom.empty _
  | compl A _ ih => exact generateFrom.compl _ ih
  | iUnion f _ ih => exact generateFrom.iUnion _ ih

theorem eq_generated : (MeasurableSpace.mkOfClosure _ rfl) = G :=
  le_antisymm F_le_G G_le_F

end generatedByFinite

end Report1
