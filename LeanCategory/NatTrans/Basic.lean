import LeanCategory.Functor.Basic

/-!
# 第3章: 自然変換の定義 (Natural Transformation)

同じ圏の組 `C ⥤ D` に属する2つの関手 `F G : C ⥤ D` の間の **自然変換**
`α : F ⟹ G` は

* 各対象 `X : C` ごとの成分 `app X : F.obj X ⟶ G.obj X`

からなり、以下の **自然性 (naturality)** を満たすものである。

* 任意の `f : X ⟶ Y` に対して `F.map f ≫ app Y = app X ≫ G.map f`

(下の図式が可換、ということ)

```
        F.map f
F.obj X ───────► F.obj Y
   │                 │
app X            app Y
   │                 │
   ▼                 ▼
G.obj X ───────► G.obj Y
        G.map f
```

## このファイルでやること

* `NatTrans F G` (記法 `F ⟹ G`) 構造体の定義 — 与えてある。`@[ext]` を付けて
  「`app` が一致すれば自然変換として等しい」という補題 `NatTrans.ext` を使えるようにする。
* 恒等自然変換 `NatTrans.id F : F ⟹ F`
  * `app` は与えてあるので、`naturality` を埋める
    (`Category.id_comp` / `Category.comp_id` で簡単に示せる)。
* 自然変換の縦合成 (vertical composition) `NatTrans.vcomp α β : F ⟹ H`
  * `app` は与えてあるので、`naturality` を埋める
    (`α.naturality` と `β.naturality` を `Category.assoc` でつなぐ
    「図式の張り合わせ」)。
* 関手圏 `C ⥤ D` への `Category` インスタンス (対象 = 関手, 射 = 自然変換)
  * `Hom`, `id`, `comp` は与えてあるので、`id_comp` / `comp_id` / `assoc` を埋める。
  * `NatTrans.ext` (と `funext`) を使って `D` の対応する法則に帰着させる。
-/

namespace CategoryTheory

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category C] {D : Type u₂} [Category D]

/-- 自然変換 `α : F ⟹ G`。各対象ごとの成分 `app` と、自然性 `naturality` の組。 -/
@[ext]
structure NatTrans (F G : C ⥤ D) where
  /-- 各対象 `X` における成分 `app X : F.obj X ⟶ G.obj X`。 -/
  app : (X : C) → (F.obj X ⟶ G.obj X)
  /-- 自然性: 任意の `f : X ⟶ Y` に対して `F.map f ≫ app Y = app X ≫ G.map f`。 -/
  naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f

/-- `F ⟹ G` : 関手 `F` から `G` への自然変換の型。 -/
scoped infixr:50 " ⟹ " => NatTrans

variable {F G H : C ⥤ D}

/-- 恒等自然変換 `NatTrans.id F : F ⟹ F`。各成分は恒等射。 -/
def NatTrans.id (F : C ⥤ D) : F ⟹ F where
  app X := 𝟙 (F.obj X)
  naturality := by
    intro X Y f
    rw [Category.comp_id, Category.id_comp]

/-- 自然変換の縦合成 (vertical composition)。`α : F ⟹ G`, `β : G ⟹ H` から
`F ⟹ H` を作る。各成分は `α.app X ≫ β.app X`。 -/
def NatTrans.vcomp (α : F ⟹ G) (β : G ⟹ H) : F ⟹ H where
  app X := α.app X ≫ β.app X
  naturality := by
    intro X Y f
    rw [← Category.assoc, α.naturality, Category.assoc, β.naturality, Category.assoc]

/-- `α ≫ β` : 自然変換の縦合成 (`NatTrans.vcomp`)。射の合成と同じ記法を使う。 -/
scoped infixr:80 " ≫ " => NatTrans.vcomp

/-- 関手圏 `C ⥤ D`。対象は関手、射は自然変換、合成は縦合成。 -/
instance : Category (C ⥤ D) where
  Hom := NatTrans
  id := NatTrans.id
  comp := NatTrans.vcomp
  id_comp := by
    intro F G α
    apply NatTrans.ext
    funext X
    simp only [NatTrans.vcomp, NatTrans.id]
    rw [Category.id_comp]
  comp_id := by
    intro F G α
    apply NatTrans.ext
    funext X
    simp only [NatTrans.vcomp, NatTrans.id]
    rw [Category.comp_id]
  assoc := by
    intro F G H K α β γ
    apply NatTrans.ext
    funext X
    simp only [NatTrans.vcomp]
    rw [Category.assoc]

end CategoryTheory
