/-
代数学序論演習 2(2025/10/10)

問題 2.1 ユークリッドの互除法によって次の最大公約数を求めよ

(1) gcd(391, 667)

(2) gcd(2431, 4199)

問題 2.2 391a + 667b = gcd(391, 667)となる整数a,bを一つ求めよ

問題 2.3
(1) Zのイデアルの定義を述べよ
(2) a₁, a₂, ..., a_k ∈ ℤ とする I = {n₁a₁ + ... + n_k a_k | n₁, n₂, ..., n_k ∈ ℤ }はZのイデアルであることを示せ
-/
import Mathlib.Data.Int.GCD -- Nat.xgcd

-- 定理: gcd(391, 667) = 23である
theorem prob_2_1_1: Nat.gcd 391 667 = 23 := by
  -- 定義から明らか
  rfl

-- #eval Nat.gcd 2431 4199 -- 221
-- 定理: gcd(2431, 4199) = 221
theorem prob_2_1_2: Nat.gcd 2431 4199 = 221 := by
  rfl


#eval Nat.gcd 391 667 -- 23
#eval Nat.xgcd 391 667 -- 12, -7
#eval 391 * 12 + 667 * -7 -- 23

theorem prob_2: 391 * 12 + 667 * (-7 : ℤ ) = Int.gcd 391 667 := by
  -- goal: 391 * 7 + 667 * -4 = ↑(Int.gcd 391 667)
  have h1 : Int.gcd 391 667 = 23 := by
    rfl
  simp [h1] -- 証明完了
