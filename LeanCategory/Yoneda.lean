import LeanCategory.Category.Types
import LeanCategory.NatTrans.Basic

/-!
# 第4章: 米田の補題 (Yoneda Lemma)

圏 `C` の対象 `A` に対して、**共変 Hom 関手 (表現可能関手)**
`yonedaObj A : C ⥤ Type v` を

* `(yonedaObj A).obj X := A ⟶ X`  (`Hom(A,-)` の `X` での値)
* `(yonedaObj A).map g f := f ≫ g`

で定める (`g : X ⟶ Y`, `f : A ⟶ X`)。

**米田の補題**は、任意の関手 `F : C ⥤ Type v` と対象 `A : C` に対して

```
(yonedaObj A ⟹ F) ≃ F.obj A
```

という全単射が存在する、という主張である。

* `→` 方向 (`yonedaEquivToFun`): 自然変換 `α` を、その「`𝟙 A` での値」
  `α.app A (𝟙 A) : F.obj A` に送る。
* `←` 方向 (`yonedaEquivInvFun`): 元 `x : F.obj A` から、
  `f : A ⟶ X` を `F.map f x` に送る自然変換を作る。

この2つが互いに逆であることを示すのが、このファイルのゴール。

## このファイルでやること

1. `Equiv α β` (2つの型の間の全単射) を定義する — 与えてある。
2. `yonedaObj A : C ⥤ Type v` を定義する。
   * `obj`, `map` は与えてあるので、`map_id` / `map_comp` を埋める
     (`Category` の法則を使う)。
3. `yonedaEquivToFun` / `yonedaEquivInvFun` を定義する。
4. これらが互いに逆であることを証明する
   (`yonedaEquivLeftInv` / `yonedaEquivRightInv`)。
5. 上記をまとめて `yonedaEquiv A F : (yonedaObj A ⟹ F) ≃ F.obj A` を作る
   — 与えてある (これが「米田の補題」の最終形)。
-/

namespace CategoryTheory

universe u v

/-- 2つの型 `α`, `β` の間の全単射。 -/
structure Equiv (α : Sort u) (β : Sort v) where
  /-- 順方向の写像。 -/
  toFun : α → β
  /-- 逆方向の写像。 -/
  invFun : β → α
  /-- `invFun` は `toFun` の左逆写像。 -/
  left_inv : ∀ a, invFun (toFun a) = a
  /-- `invFun` は `toFun` の右逆写像。 -/
  right_inv : ∀ b, toFun (invFun b) = b

/-- `α ≃ β` : `α` と `β` の間の全単射の型。 -/
infixr:25 " ≃ " => Equiv

variable {C : Type u} [Category.{u, v} C]

/-- 共変 Hom 関手 `Hom(A,-) : C ⥤ Type v`。 -/
def yonedaObj (A : C) : C ⥤ Type v where
  obj X := A ⟶ X
  map g f := f ≫ g
  -- ヒント: `(yonedaObj A).map (𝟙 X) = fun f => f ≫ 𝟙 X` であり、
  -- これは `fun f => f` (`Category.comp_id`) と等しい。`funext` を使う。
  map_id := by
    sorry
  -- ヒント: `(yonedaObj A).map (f ≫ g) = fun h => h ≫ (f ≫ g)` であり、
  -- `Category.assoc` を使って `fun h => (h ≫ f) ≫ g` と等しいことを示す
  -- (`.symm` が必要かどうか考えよ)。`funext` を使う。
  map_comp := by
    sorry

variable {F : C ⥤ Type v}

/-- 米田写像 (→ 方向): 自然変換 `α : yonedaObj A ⟹ F` を、
`α` の `𝟙 A` での値 `α.app A (𝟙 A) : F.obj A` に送る。 -/
def yonedaEquivToFun (A : C) (F : C ⥤ Type v) (α : yonedaObj A ⟹ F) : F.obj A :=
  sorry

/-- 米田写像の逆 (← 方向): 元 `x : F.obj A` から自然変換を作る。
`f : A ⟶ X` を `F.map f x` に送る。 -/
def yonedaEquivInvFun (A : C) (F : C ⥤ Type v) (x : F.obj A) : yonedaObj A ⟹ F where
  app X f := sorry
  -- ヒント: `F.map_comp` を使う。`(yonedaObj A).map g f = f ≫ g` であることに注意する。
  naturality := by
    sorry

/-- `yonedaEquivInvFun` してから `yonedaEquivToFun` すると元に戻る。
(`F.map_id` を使う。) -/
theorem yonedaEquivRightInv (A : C) (F : C ⥤ Type v) (x : F.obj A) :
    yonedaEquivToFun A F (yonedaEquivInvFun A F x) = x := by
  sorry

/-- `yonedaEquivToFun` してから `yonedaEquivInvFun` すると元に戻る。
(`α.naturality` を使う — `α : yonedaObj A ⟹ F` の自然性から、
`α.app X f` を `α.app A (𝟙 A)` と `F.map f` で書き換える。
`NatTrans.ext` で `app` の等式に帰着させる。) -/
theorem yonedaEquivLeftInv (A : C) (F : C ⥤ Type v) (α : yonedaObj A ⟹ F) :
    yonedaEquivInvFun A F (yonedaEquivToFun A F α) = α := by
  sorry

/-- **米田の補題**: 関手 `F : C ⥤ Type v` と対象 `A : C` に対して、
`yonedaObj A = Hom(A,-)` から `F` への自然変換は、`F.obj A` の元と1対1に対応する。 -/
def yonedaEquiv (A : C) (F : C ⥤ Type v) : (yonedaObj A ⟹ F) ≃ F.obj A where
  toFun := yonedaEquivToFun A F
  invFun := yonedaEquivInvFun A F
  left_inv := yonedaEquivLeftInv A F
  right_inv := yonedaEquivRightInv A F

end CategoryTheory
