import LeanCategory.Category.Basic

/-!
# 第2章: 関手の定義 (Functor)

圏 `C` から圏 `D` への **関手** `F : C ⥤ D` は

* 対象の対応 `obj : C → D`
* 射の対応 `map : (X ⟶ Y) → (obj X ⟶ obj Y)`

からなり、以下の法則を満たすものである。

* `map (𝟙 X) = 𝟙 (obj X)` (`map_id`)
* `map (f ≫ g) = map f ≫ map g` (`map_comp`)

## このファイルでやること

* `Functor C D` (記法 `C ⥤ D`) 構造体の定義 — 与えてある。
* 恒等関手 `Functor.id C : C ⥤ C`
  * `obj`, `map` は与えてあるので、`map_id` / `map_comp` を埋める。
  * いずれも両辺が **完全に同じ式になる** (`rfl` で解ける) はず。
* 関手の合成 `Functor.comp F G : C ⥤ E` (記法 `F ⋙ G`)
  * `obj`, `map` は与えてあるので、`map_id` / `map_comp` を埋める。
  * `F` と `G` それぞれの `map_id` / `map_comp` を組み合わせて証明する
    (`Opposite.lean` で `C` の法則を使って `Cᵒᵖ` の法則を示したのと同じ発想)。
-/

namespace CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃

/-- 関手 `F : C ⥤ D`。対象の対応 `obj` と射の対応 `map` の組で、
恒等射・合成を保つもの。 -/
structure Functor (C : Type u₁) (D : Type u₂) [Category C] [Category D] where
  /-- 対象の対応。 -/
  obj : C → D
  /-- 射の対応。 -/
  map : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj Y)
  /-- 恒等射を恒等射に送る。 -/
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X)
  /-- 合成を保つ。 -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g

/-- `C ⥤ D` : `C` から `D` への関手の型。 -/
scoped infixr:26 " ⥤ " => Functor

attribute [simp] Functor.map_id Functor.map_comp

variable {C : Type u₁} [Category C] {D : Type u₂} [Category D] {E : Type u₃} [Category E]

/-- 恒等関手 `Functor.id C : C ⥤ C`。対象・射をすべてそのまま送る。 -/
def Functor.id (C : Type u₁) [Category C] : C ⥤ C where
  obj X := X
  map f := f
  map_id := by
    sorry
  map_comp := by
    sorry

/-- 関手の合成 `F ⋙ G : C ⥤ E`。`F : C ⥤ D`, `G : D ⥤ E` をまず `F`, 次に `G`
の順に適用する。 -/
def Functor.comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
  -- ヒント: `F.map_id` で `F.map (𝟙 X)` を `𝟙 (F.obj X)` に書き換えてから、
  -- `G.map_id` を使う。
  map_id := by
    sorry
  -- ヒント: `F.map_comp` で `F.map (f ≫ g)` を `F.map f ≫ F.map g` に書き換えてから、
  -- `G.map_comp` を使う。
  map_comp := by
    sorry

/-- `F ⋙ G` : 関手の合成 (`F` の後に `G`)。 -/
scoped infixr:80 " ⋙ " => Functor.comp

end CategoryTheory
