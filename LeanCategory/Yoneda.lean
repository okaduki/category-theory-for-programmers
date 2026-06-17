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

/-! ## 演習: 米田埋め込み -/

/-- 米田埋め込みの射の対応: `f : B ⟶ A` を自然変換 `yonedaObj A ⟹ yonedaObj B` に送る。
各成分は `f` による前合成 `g ↦ f ≫ g`。

`yonedaEquivInvFun A (yonedaObj B)` と本質的に同じだが、
こちらは `yonedaObj B` を直接使って自然変換を構成する。 -/
def yonedaMap {A B : C} (f : B ⟶ A) : yonedaObj A ⟹ yonedaObj B where
  app X g := f ≫ g
  -- ヒント: `funext` で `g : A ⟶ X` を導入し、
  -- ゴールが `f ≫ g ≫ h = (f ≫ g) ≫ h` の形になることを確認せよ。
  -- `show` で目標を具体化してから `Category.assoc` を使う。
  naturality := by
    sorry

/-- 米田の補題を `F = yonedaObj B` に特殊化したもの: 自然変換 `yonedaObj A ⟹ yonedaObj B` と
射 `B ⟶ A` の間に全単射がある。これが**米田埋め込みの完全忠実性**を意味する。

ヒント: `(yonedaObj B).obj A` を展開すると `B ⟶ A` になる。
`yonedaEquiv` を適切な引数で適用するだけで示せる。 -/
def yonedaFullyFaithful (A B : C) :
    (yonedaObj A ⟹ yonedaObj B) ≃ (B ⟶ A) :=
  sorry

/-! ## 応用例: 米田の補題を具体的な関手に適用する

米田の補題 `(yonedaObj A ⟹ F) ≃ F.obj A` の `F`・`A` を具体的に選ぶと、
プログラミングでおなじみの型同型が得られる。Haskell 風に書くと米田の補題は

```haskell
forall x. (a -> x) -> F x  ≅  F a
```

であり、`yonedaObj A` の `X` での値 `A ⟶ X` が `a -> x` に、自然変換が
`forall x.` で全称量化された多相関数に対応する。 -/

/-- 応用例1 (継続渡し形式, CPS): 恒等関手 `Id : Type v ⥤ Type v` に米田の補題を適用すると、

```
(yonedaObj A ⟹ Id) ≃ A      -- forall x. (A → x) → x  ≅  A
```

が得られる。左辺は「継続 `A ⟶ x` を任意の `x` について受け取り `x` を返す多相関数」、
すなわち `A` の値の CPS 表現であり、それが元の値 `A` と1対1に対応する。

ヒント: `yonedaEquiv` を恒等関手 `Functor.id (Type v)` に適用するだけ。
`(Functor.id (Type v)).obj A = A` は定義的に等しい。 -/
def cpsEquiv (A : Type v) : (yonedaObj A ⟹ Functor.id (Type v)) ≃ A :=
  sorry

/-- リスト関手 `List : Type v ⥤ Type v`。対象 `X` を `List X` に、射 `f` を `List.map f` に送る。 -/
def listFunctor : Type v ⥤ Type v where
  obj X := List X
  map f := List.map f
  -- ヒント: `funext` でリスト `l` を取り、`l` についての帰納法 (`induction l with`)。
  -- cons の場合は帰納法の仮定 `ih` に cons の頭をかぶせる (`congrArg (a :: ·) ih`)。
  map_id := by
    sorry
  map_comp := by
    sorry

/-- 応用例2 (ユニット型のリスト): リスト関手とユニット型 `PUnit` に米田の補題を適用すると、

```
(yonedaObj PUnit ⟹ listFunctor) ≃ List PUnit
```

が得られる。左辺は「`x` を1つ受け取り `List x` を返す自然な多相関数」全体で、自然性から
`fun x => [x, ..., x]`(長さ `n` のリスト)の形に限られる。右辺 `List PUnit` も要素がすべて
`PUnit.unit` なので長さだけで決まり、本質的に自然数である(下の `listPUnitEquivNat`)。

ヒント: `yonedaEquiv` を `listFunctor` と `PUnit` に適用するだけ。 -/
def listUnitEquiv : (yonedaObj (PUnit : Type v) ⟹ listFunctor) ≃ List (PUnit : Type v) :=
  sorry

/-- `List PUnit` はその長さによって自然数と1対1に対応する。
`listUnitEquiv` と合わせると `(yonedaObj PUnit ⟹ listFunctor) ≃ List PUnit ≃ Nat`、
すなわち「`x → [x]` という形の自然な多相関数の正体は自然数」だと分かる。

ヒント: `toFun` はリストの長さ、`invFun` は `List.replicate n PUnit.unit`。
`left_inv` / `right_inv` はいずれも帰納法。`PUnit` の要素はすべて `PUnit.unit` に等しい。 -/
def listPUnitEquivNat : List (PUnit : Type v) ≃ Nat where
  toFun l := l.length
  invFun n := List.replicate n PUnit.unit
  left_inv := by
    sorry
  right_inv := by
    sorry

end CategoryTheory
