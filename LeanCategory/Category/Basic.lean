/-!
# 第1章: 圏の定義 (Category)

圏論の出発点となる「圏 (category)」を定義する。

圏 `C` は

* 対象 (object) の集まり `Obj`
* 対象 `X Y : Obj` の間の射 (morphism) の集まり `Hom X Y`
* 各対象 `X` に対する恒等射 `𝟙 X : Hom X X`
* 射の合成 `comp : Hom X Y → Hom Y Z → Hom X Z` (`f ≫ g` と書く)

からなり、以下の法則を満たすものである。

* 単位律: `𝟙 X ≫ f = f`, `f ≫ 𝟙 Y = f`
* 結合律: `(f ≫ g) ≫ h = f ≫ (g ≫ h)`

ここでは Mathlib の `CategoryTheory.Category.Basic` を参考にしつつ、
学習目的のため一から定義し直している。
-/

namespace CategoryTheory

universe u v

/-- 圏 (category)。

対象の型 `Obj`、射の型 `Hom`、恒等射 `id`、合成 `comp` に加えて、
単位律 (`id_comp`, `comp_id`) と結合律 (`assoc`) を満たすデータ。 -/
class Category (Obj : Type u) where
  /-- 対象 `X` から `Y` への射の型。 -/
  Hom : Obj → Obj → Type v
  /-- 恒等射 `𝟙 X : Hom X X`。 -/
  id : (X : Obj) → Hom X X
  /-- 射の合成。`f ≫ g` は「`f` を行ってから `g` を行う」を表す
  (図式順, diagrammatic order)。 -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- 左単位律: `𝟙 X ≫ f = f` -/
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  /-- 右単位律: `f ≫ 𝟙 Y = f` -/
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  /-- 結合律: `(f ≫ g) ≫ h = f ≫ (g ≫ h)` -/
  assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
      comp (comp f g) h = comp f (comp g h)

/-- `X ⟶ Y`: 対象 `X` から `Y` への射の型 (`Category.Hom X Y`)。 -/
scoped infixr:10 " ⟶ " => Category.Hom

/-- `f ≫ g`: `f : Hom X Y` と `g : Hom Y Z` の合成。図式順。 -/
scoped infixr:80 " ≫ " => Category.comp

/-- `𝟙 X`: 対象 `X` の恒等射。 -/
scoped notation "𝟙" => Category.id

attribute [simp] Category.id_comp Category.comp_id Category.assoc

end CategoryTheory
