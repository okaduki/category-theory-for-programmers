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

universe u v w

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

/-- 全単射の合成 (推移律)。`α ≃ β` と `β ≃ γ` から `α ≃ γ` を作る。 -/
def Equiv.trans {α : Sort u} {β : Sort v} {γ : Sort w} (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ where
  toFun a := e₂.toFun (e₁.toFun a)
  invFun c := e₁.invFun (e₂.invFun c)
  left_inv := by
    intro a
    show e₁.invFun (e₂.invFun (e₂.toFun (e₁.toFun a))) = a
    rw [e₂.left_inv, e₁.left_inv]
  right_inv := by
    intro c
    show e₂.toFun (e₁.toFun (e₁.invFun (e₂.invFun c))) = c
    rw [e₁.right_inv, e₂.right_inv]

variable {C : Type u} [Category.{u, v} C]

/-- 共変 Hom 関手 `Hom(A,-) : C ⥤ Type v`。 -/
def yonedaObj (A : C) : C ⥤ Type v where
  obj X := A ⟶ X
  map g := fun f => f ≫ g
  map_id := by
    intro X
    funext f
    exact Category.comp_id f
  map_comp := by
    intro X Y Z f g
    funext h
    show h ≫ f ≫ g = (h ≫ f) ≫ g
    rw [Category.assoc]

variable {F : C ⥤ Type v}

/-- 米田写像 (→ 方向): 自然変換 `α : yonedaObj A ⟹ F` を、
`α` の `𝟙 A` での値 `α.app A (𝟙 A) : F.obj A` に送る。 -/
def yonedaEquivToFun (A : C) (F : C ⥤ Type v) (α : yonedaObj A ⟹ F) : F.obj A :=
  α.app A (𝟙 A)

/-- 米田写像の逆 (← 方向): 元 `x : F.obj A` から自然変換を作る。
`f : A ⟶ X` を `F.map f x` に送る。 -/
def yonedaEquivInvFun (A : C) (F : C ⥤ Type v) (Fa : F.obj A) : yonedaObj A ⟹ F where
  app (X : C) (f : A ⟶ X) := F.map f Fa
  naturality := by
    intro X Y f
    funext h
    show F.map (h ≫ f) Fa = F.map f (F.map h Fa)
    rw [F.map_comp]
    rfl

/-- `yonedaEquivInvFun` してから `yonedaEquivToFun` すると元に戻る。
(`F.map_id` を使う。) -/
theorem yonedaEquivRightInv (A : C) (F : C ⥤ Type v) (x : F.obj A) :
    yonedaEquivToFun A F (yonedaEquivInvFun A F x) = x := by
  show F.map (𝟙 A) x = x
  exact congrFun (F.map_id A) x

/-- `yonedaEquivToFun` してから `yonedaEquivInvFun` すると元に戻る。
(`α.naturality` を使う — `α : yonedaObj A ⟹ F` の自然性から、
`α.app X f` を `α.app A (𝟙 A)` と `F.map f` で書き換える。
`NatTrans.ext` で `app` の等式に帰着させる。) -/
theorem yonedaEquivLeftInv (A : C) (F : C ⥤ Type v) (α : yonedaObj A ⟹ F) :
    yonedaEquivInvFun A F (yonedaEquivToFun A F α) = α := by
  apply NatTrans.ext
  funext X f
  show F.map f (α.app A (𝟙 A)) = α.app X f
  have nat := congrFun (α.naturality f) (𝟙 A)
  calc F.map f (α.app A (𝟙 A))
      = α.app X (𝟙 A ≫ f) := nat.symm
    _ = α.app X f := by rw [Category.id_comp]

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
  naturality := by
    intro X Y h
    funext (g : A ⟶ X)
    show f ≫ (g ≫ h) = (f ≫ g) ≫ h
    exact Eq.symm (Category.assoc f g h)

/-- 米田の補題を `F = yonedaObj B` に特殊化したもの: 自然変換 `yonedaObj A ⟹ yonedaObj B` と
射 `B ⟶ A` の間に全単射がある。これが**米田埋め込みの完全忠実性**を意味する。
-/
def yonedaFullyFaithful (A B : C) :
    (yonedaObj A ⟹ yonedaObj B) ≃ (B ⟶ A) :=
  yonedaEquiv A (yonedaObj B)

/-! ## 米田の補題の自然性

`yonedaEquiv A F` の全単射は `A`・`F` について **自然** である。ここでは `→` 方向
`yonedaEquivToFun` について、その自然性の可換図式を等式として示す。 -/

/-- **`F` についての自然性**: 自然変換 `θ : F ⟹ G` に対して、
「`α` に `θ` を垂直合成してから評価する」のと「評価してから `θ.app A` で送る」のは一致する。

ヒント: `yonedaEquivToFun` と `NatTrans.vcomp` の定義を展開すると両辺は定義的に等しく、
`rfl` で示せる。 -/
theorem yonedaEquivToFun_naturalF {F G : C ⥤ Type v} (A : C)
    (θ : F ⟹ G) (α : yonedaObj A ⟹ F) :
    yonedaEquivToFun A G (NatTrans.vcomp α θ)
      = θ.app A (yonedaEquivToFun A F α) :=
  sorry

/-- **`A` についての自然性 (反変)**: 射 `g : A ⟶ B` に対して、
「`yonedaMap g` を前から垂直合成してから評価する」のと「評価してから `F.map g` で送る」のは一致する。
`g : A ⟶ B` が `yonedaObj B ⟹ yonedaObj A` を誘導する点に反変性が表れている。

ヒント: `α.naturality g` を `𝟙 A` で評価すると
`α.app B (𝟙 A ≫ g) = F.map g (α.app A (𝟙 A))` が得られる。
ゴールの `g ≫ 𝟙 B` と `𝟙 A ≫ g` を単位律 (`Category.comp_id` / `Category.id_comp`) で
`g` に揃えればよい。 -/
theorem yonedaEquivToFun_naturalA {A B : C} (g : A ⟶ B)
    (F : C ⥤ Type v) (α : yonedaObj A ⟹ F) :
    yonedaEquivToFun B F (NatTrans.vcomp (yonedaMap g) α)
      = F.map g (yonedaEquivToFun A F α) := by
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
-/
def cpsEquiv (A : Type v) : (yonedaObj A ⟹ Functor.id (Type v)) ≃ A :=
  yonedaEquiv A (Functor.id (Type v))

/-- リスト関手 `List : Type v ⥤ Type v`。対象 `X` を `List X` に、射 `f` を `List.map f` に送る。 -/
def listFunctor : Type v ⥤ Type v where
  obj X := List X
  map f := List.map f
  map_id := by
    intro X
    funext l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      apply congrArg (x :: ·)
      exact ih
  map_comp := by
    intro X Y Z f g
    funext l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      show List.map (f ≫ g) (x :: xs) = (List.map g (List.map f (x :: xs)))
      apply congrArg (g (f x) :: ·)
      exact ih

/-- 応用例2 (ユニット型のリスト): リスト関手とユニット型 `PUnit` に米田の補題を適用すると、

```
(yonedaObj PUnit ⟹ listFunctor) ≃ List PUnit
```

が得られる。左辺は「`x` を1つ受け取り `List x` を返す自然な多相関数」全体で、自然性から
`fun x => [x, ..., x]`(長さ `n` のリスト)の形に限られる。右辺 `List PUnit` も要素がすべて
`PUnit.unit` なので長さだけで決まり、本質的に自然数である(下の `listPUnitEquivNat`)。 -/
def listUnitEquiv : (yonedaObj (PUnit : Type v) ⟹ listFunctor) ≃ List (PUnit : Type v) :=
  yonedaEquiv PUnit listFunctor

/-- `List PUnit` はその長さによって自然数と1対1に対応する。
`listUnitEquiv` と合わせると `(yonedaObj PUnit ⟹ listFunctor) ≃ List PUnit ≃ Nat`、
すなわち「`x → [x]` という形の自然な多相関数の正体は自然数」だと分かる。-/

/-
ヒント: `toFun` はリストの長さ、`invFun` は `List.replicate n PUnit.unit`。
`left_inv` / `right_inv` はいずれも帰納法。`PUnit` の要素はすべて `PUnit.unit` に等しい。 -/
def listPUnitEquivNat : List (PUnit : Type v) ≃ Nat where
  toFun l := l.length
  invFun n := List.replicate n PUnit.unit
  left_inv := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      show PUnit.unit :: List.replicate xs.length PUnit.unit = x :: xs
      rw [ih]
  right_inv := by
    intro n
    exact List.length_replicate

/-- 米田の補題と長さ同型を合成した最終形:

```
(yonedaObj PUnit ⟹ listFunctor) ≃ Nat
```

「`a → [a]` という形の自然な多相関数(米田の左辺 `forall a. (() → a) → [a]` を
`() → a ≅ a` で簡約したもの)は、自然数とちょうど1対1に対応する」という主張の完全形。-/
def listUnitNatEquiv : (yonedaObj (PUnit : Type v) ⟹ listFunctor) ≃ Nat :=
  listUnitEquiv.trans listPUnitEquivNat

end CategoryTheory
