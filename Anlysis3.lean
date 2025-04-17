-- This module serves as the root of the `Anlysis3` library.
-- Import modules here that should be built as part of the library.
import Anlysis3.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable

-- 測度論に関するimport

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs -- 可測空間の定義とか

/-
解析学C(測度論)の課題を証明していく。
あれ、測度論でよく出てくる、まがったfというかFraktur?のfってLeanでどうやって出すんだっけ.
AbbreviationViewを検索したけど、なさそう. Set Theory Gameでも集合族はFと表していたし、それに従うか。

レポート問題 No. 1

問1. 集合Sを固定し、F = {A ∈ P(S) | Aは可算集合 ∨ S \ A は可算集合}とする。
以下の問に答えなさい。

(1) FがSを全体集合とするσ-加法族であることを示しなさい。

(2) FはSの有限部分集合の全体が生成するσ-加法族であることを示しなさい。

-/

-- まずは何から始めるべきなんだろうか？
