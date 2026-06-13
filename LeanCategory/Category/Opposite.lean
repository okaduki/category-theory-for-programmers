import LeanCategory.Category.Basic

/-!
# 双対圏 (opposite category)

圏 `C` から、射の向きをすべて逆にした **双対圏** `Cᵒᵖ` を作る。
米田の補題の主張 (`Hom(-, A)` を `Cᵒᵖ ⥤ Type` の対象とみなす) で必要になる。

`Cᵒᵖ` の対象は `C` の対象と 1 対 1 に対応するが、

* `Hom_{Cᵒᵖ} X Y := Hom_C (unop Y) (unop X)` (向きが逆!)
* `𝟙_{Cᵒᵖ} X := 𝟙_C (unop X)`
* `f ≫_{Cᵒᵖ} g := g ≫_C f` (合成の順序も逆!)

と定める。

## このファイルでやること

* `Opposite C` (記法 `Cᵒᵖ`) という、`C` と「同じ要素を持つが別の型」を用意する
  (`op` / `unop` で行き来する)。
* `op_unop` / `unop_op` (`op` と `unop` が互いに逆であること) — ウォームアップ。
* `Cᵒᵖ` に対する `Category` インスタンスを定義する。
  * データ部分 (`Hom`, `id`, `comp`) は与えてあるので、
    **法則 (`id_comp`, `comp_id`, `assoc`) を、元の圏 `C` の法則を使って証明する**
    のがメインの演習。
  * ポイントは「`Cᵒᵖ` での合成 `f ≫ g` は `C` での `g ≫ f` である」ということ。
    `Cᵒᵖ` の単位律・結合律は、`C` の単位律・結合律を「左右反対にしたもの」になる
    (圏論の双対性 (duality) の最も簡単な例)。
-/

namespace CategoryTheory

universe u v

/-- `C` の「双対」の対象の型。`Opposite C` の要素は `C` の要素 1 つを
ラップしただけのものだが、これを使って `Cᵒᵖ` への別の `Category` インスタンスを
定義できるようにする。 -/
structure Opposite (C : Type u) where
  /-- `Opposite C` の要素から、元の `C` の要素を取り出す。 -/
  unop : C

/-- `Cᵒᵖ` : `C` の双対圏の対象の型。 -/
notation:max C "ᵒᵖ" => Opposite C

/-- `op X` : `X : C` に対応する `Cᵒᵖ` の対象。 -/
def op {C : Type u} (X : C) : Cᵒᵖ := ⟨X⟩

/-- ウォームアップ: `op` してから `unop` すると元に戻る。 -/
@[simp] theorem unop_op {C : Type u} (X : C) : (op X).unop = X := by
  sorry

/-- ウォームアップ: `unop` してから `op` すると元に戻る。 -/
@[simp] theorem op_unop {C : Type u} (X : Cᵒᵖ) : op X.unop = X := by
  sorry

variable {C : Type u} [Category C]

/-- `Cᵒᵖ` への `Category` インスタンス。

データ部分 (`Hom`, `id`, `comp`) は定義済み。
`id_comp`, `comp_id`, `assoc` を `C` の対応する法則から証明せよ。 -/
instance : Category Cᵒᵖ where
  Hom X Y := Y.unop ⟶ X.unop
  id X := 𝟙 X.unop
  comp f g := g ≫ f
  -- ヒント: `Cᵒᵖ` での `f ≫ 𝟙 Y` は `C` での `𝟙 Y.unop ≫ f`。
  -- `C` の `id_comp` か `comp_id` のどちらを使えばよいか考えよ。
  id_comp := by
    sorry

  -- `comp_id`: `f ≫ (𝟙 Y) = f`  (`Cᵒᵖ` での合成)
  -- 展開すると `(𝟙 Y.unop) ≫ f = f` (`C` での合成) になる。
  comp_id := by
    sorry
  -- `assoc`: `(f ≫ g) ≫ h = f ≫ (g ≫ h)`  (`Cᵒᵖ` での合成)
  -- 展開すると `C` での結合律の左右が入れ替わった形になる。
  -- `Category.assoc` を使い、`.symm` が必要かどうか考えよ。
  assoc := by
    sorry

end CategoryTheory
