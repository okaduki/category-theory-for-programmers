# lean-category

Lean 4 で圏論 (category theory) を学ぶための個人用プロジェクト。

**目標**: 「圏 (category) の定義」から始めて、「米田の補題 (Yoneda lemma)」の証明まで、
基本的な概念を **Mathlib に依存せず、自分の手で一から定義・証明する**。
Mathlib には `Mathlib.CategoryTheory` として非常に整備された圏論ライブラリがあるが、
このプロジェクトは学習目的のため意図的にそれを使わず、必要なものをすべて自作する。

## 環境

* Lean: `leanprover/lean4:v4.30.0` (`lean-toolchain` に固定)
* ビルドツール: Lake (`lakefile.toml`)
* 依存パッケージ: なし (Mathlib 未使用)

```sh
# ビルド (全体の型検査)
lake build

# 特定ファイルだけ調べたいとき
lake env lean LeanCategory/Category/Basic.lean
```

エディタ (VS Code の Lean 4 拡張など) を使う場合は、このディレクトリを開けば
`lean-toolchain` を見て自動的に対応するツールチェインが使われる。

## 全体の構成・ロードマップ

`LeanCategory/` 以下に章ごとにファイルを分けている。`LeanCategory.lean` が
ルートファイルで、すべての章を `import` する。

| 章 | ファイル | 内容 | 状態 |
| --- | --- | --- | --- |
| 1 | [`Category/Basic.lean`](LeanCategory/Category/Basic.lean) | 圏 (`Category`) の定義、`≫`・`𝟙` 記法、単位律・結合律 | ✅ 完了 |
| 1' | [`Category/Types.lean`](LeanCategory/Category/Types.lean) | 例: 型と関数の圏 `Type u` への `Category` インスタンス | ✅ 完了 |
| 1'' | [`Category/Opposite.lean`](LeanCategory/Category/Opposite.lean) | 双対圏 `Cᵒᵖ` の定義 (番外編、米田の補題の本筋とは独立) | 🚧 演習中 (`sorry` を埋める) |
| 2 | [`Functor/Basic.lean`](LeanCategory/Functor/Basic.lean) | 関手 `Functor C D` (`C ⥤ D`)、恒等関手・関手の合成 | 🚧 演習中 (`sorry` を埋める) |
| 3 | [`NatTrans/Basic.lean`](LeanCategory/NatTrans/Basic.lean) | 自然変換 `NatTrans F G` (`F ⟹ G`)、関手圏 | 🚧 演習中 (`sorry` を埋める) |
| 4 | [`Yoneda.lean`](LeanCategory/Yoneda.lean) | `Equiv`、共変 Hom 関手 `yonedaObj`、米田の補題 `yonedaEquiv` | 🚧 演習中 (`sorry` を埋める) |

各ファイルの先頭には、その章で何を定義・証明するかの概要を `/-! ... -/` コメント
(モジュールドキュメント) として書いている。

第2〜4章はすべて「データ部分・自明な構成は与えてあり、法則やその応用の証明が
`sorry` になっている」状態になっている。`sorry` の一覧と内容は次の節を参照。

### 演習一覧 (`sorry` の場所)

| ファイル | 演習 | 内容 |
| --- | --- | --- |
| `Category/Opposite.lean` | `unop_op` / `op_unop` | `op` と `unop` が互いに逆であること — ウォームアップ |
| `Category/Opposite.lean` | `Category Cᵒᵖ` の `id_comp` / `comp_id` / `assoc` | 双対圏が圏になること (`C` の対応する法則の「左右反転」) |
| `Functor/Basic.lean` | `Functor.id` の `map_id` / `map_comp` | 恒等関手が関手の法則を満たすこと (`rfl` で解ける) |
| `Functor/Basic.lean` | `Functor.comp` の `map_id` / `map_comp` | 関手の合成が関手の法則を満たすこと (`F`, `G` の `map_id`/`map_comp` を合成する) |
| `NatTrans/Basic.lean` | `NatTrans.id` の `naturality` | 恒等自然変換が自然性を満たすこと (`Category.id_comp`/`comp_id`) |
| `NatTrans/Basic.lean` | `NatTrans.vcomp` の `naturality` | 自然変換の縦合成が自然性を満たすこと (`Category.assoc` で図式をつなぐ) |
| `NatTrans/Basic.lean` | `Category (C ⥤ D)` の `id_comp` / `comp_id` / `assoc` | 関手圏が圏になること (`NatTrans.ext` + `D` の法則) |
| `Yoneda.lean` | `yonedaObj` の `map_id` / `map_comp` | `Hom(A, -) : C ⥤ Type v` が関手であること |
| `Yoneda.lean` | `yonedaEquivToFun` | 米田写像 (→ 方向) の定義 |
| `Yoneda.lean` | `yonedaEquivInvFun` の `app` / `naturality` | 米田写像の逆 (← 方向) の定義と自然性の証明 |
| `Yoneda.lean` | `yonedaEquivRightInv` | `toFun ∘ invFun = id` の証明 (`F.map_id` を使う) |
| `Yoneda.lean` | `yonedaEquivLeftInv` | `invFun ∘ toFun = id` の証明 (自然性 `α.naturality` を使う) — **米田の補題の核心** |
| `Yoneda.lean` | `yonedaMap` の `naturality` | 米田埋め込みの射の対応が自然変換であること (`Category.assoc`) |
| `Yoneda.lean` | `yonedaFullyFaithful` | 米田埋め込みの完全忠実性 (`yonedaEquiv` の特殊化) |

最後の `yonedaEquiv` (`yonedaObj A ⟹ F ≃ F.obj A`) 自体は、これらの部品を
組み立てるだけなので `sorry` なしで完成している。すべての `sorry` が埋まれば、
このプロジェクトの目標 (圏の定義 → 米田の補題の証明) が達成される。

### 大まかな証明の流れ (第4章 米田の補題)

圏 `C` の対象 `A` と、関手 `F : C ⥤ Type` に対して、

```
(yonedaObj A ⟹ F) ≃ F.obj A
```

という自然な全単射を構成・証明する、というのが最終目標。そのために

1. 圏の定義 (第1章)
2. 関手の定義、共変 Hom 関手 `yonedaObj A : C ⥤ Type` (`Hom(A,-)`) (第2章・第4章)
3. 自然変換の定義、関手圏 (第3章)
4. 米田写像 `α ↦ α.app A (𝟙 A)` とその逆写像、両者が逆であることの証明 (第4章)

という順に積み上げていく。

## 記法

`namespace CategoryTheory` 内で以下の `scoped` 記法を定義している
(使うときは `open CategoryTheory` するか、`CategoryTheory` 名前空間内で書く)。

* `X ⟶ Y` : 対象 `X` から `Y` への射の型 (`Category.Hom X Y`)
* `f ≫ g` : 射 `f : Hom X Y` と `g : Hom Y Z` の合成 (図式順、`f` の後に `g`)
* `𝟙 X` : 対象 `X` の恒等射
* `C ⥤ D` : `C` から `D` への関手の型 (`Functor C D`)
* `F ⋙ G` : 関手の合成 (`F` の後に `G`)
* `F ⟹ G` : 関手 `F` から `G` への自然変換の型 (`NatTrans F G`)
* `α ≃ β` : `α` と `β` の間の全単射の型 (`Equiv α β`、`Yoneda.lean` で定義)

## 演習の進め方

`sorry` になっている箇所を埋めていくスタイルで進める。

```sh
# sorry が残っている箇所を一覧する
grep -rn sorry LeanCategory/
```

各 `sorry` の上にはヒントコメントを付けている。詰まったら、関連する補題
(`Category.id_comp` / `Category.comp_id` / `Category.assoc` など) の型を
`#check` で確認し、`f ≫ g`・`𝟙 X` を展開してどちらの形に合うかを考えるとよい。

## 参考

* Mathlib4: [`Mathlib.CategoryTheory.Category.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html) など
  (定義の参考にするが、コードはコピーせず自分で書く)
* 圏論の教科書 (例: Mac Lane "Categories for the Working Mathematician"、
  またはより入門的な書籍) を併読しながら形式化する。
