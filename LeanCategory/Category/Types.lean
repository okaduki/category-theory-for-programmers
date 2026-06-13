import LeanCategory.Category.Basic

/-!
# 例: 型の圏 (the category of types)

`Category` の定義が正しく書けていることを確かめるための最小の例として、
型と関数からなる圏 `Type u` への `Category` インスタンスを与える。

* 対象: 型 `X Y : Type u`
* 射: `Hom X Y := X → Y`
* 恒等射: 恒等関数
* 合成: 関数合成 (図式順, `f ≫ g = fun x => g (f x)`)
-/

namespace CategoryTheory

universe u

instance : Category (Type u) where
  Hom X Y := X → Y
  id _ := fun x => x
  comp f g := fun x => g (f x)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end CategoryTheory
