import Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
import Hironaka.Resolution.HironakaG10HirFlatQuotient

/-!
# P1 — the whole-fibre (germ) flattener of a morphism of reduced complex spaces

Lane G10H, run 0080, round 3 (plan P1 of `work/hironaka-resume-20261111/G10H/PSEUDOFREE-ROUTE.md` §4).
Source: H. Hironaka, *Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975):
(1.14.2) (p. 512) tests flatness on closed-subspace germs of the base; (2.4.2) (p. 526) and (*) of
Def. 4.4.2 (p. 537) are its non-germ forms; Rem. 2.4.4 (p. 529) is uniqueness.

The pointed flattener `IsPointFlattenerAt` and the whole-fibre flattener `IsGermFlattenerAt` are those
of lane G10C's `HironakaG10ChowFlattenerDecrease` (stated there from lane G10H's r2 draft), and its
existence (`germFlattener`, `isGermFlattenerAt_germFlattener`, `eq_germFlattener`) is lane G10C's
`HironakaG10ChowLeavingRounds`; this module adds the base-change calculus:

* `FlatOverAt f x J` — `f` is flat over the germ `V(J)` at every point of the fibre over `x`;
  `FlatOverAt.mono` (smaller germs), `flatOverAt_bot_iff` (the whole germ = flatness at every fibre
  point), `flatOverAt_maximalIdeal` (the reduced point);
* `isGermFlattenerAt_iSup`: the sum of ANY choice of pointed flatteners over the fibre is the
  whole-fibre flattener;
* uniqueness, flatness over the flattener, `le_maximalIdeal`, `ne_top`, and `isGermFlattenerAt_bot_iff`,
  `eq_bot_iff_of_isGermFlattenerAt`: the flattener is `⊥` exactly at points outside the non-flat image.
No named input.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener

open Hironaka HironakaG10HirFlatQuotient
open Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds

noncomputable section

variable {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)

/-- `f` is flat over the closed-subspace germ `V(J)` at every point of the fibre over `x`. -/
def FlatOverAt (x : X.obj.left) (J : Ideal (X.obj.left.presheaf.stalk x)) : Prop :=
  ∀ (y : Y.obj.left) (h : f.hom.left.base y = x), (quotMap (fibreStalkMap f x y h) J).Flat

variable {f}

/-- The whole-fibre flattener, read through `FlatOverAt`. -/
theorem isGermFlattenerAt_iff {x : X.obj.left} {I : Ideal (X.obj.left.presheaf.stalk x)} :
    IsGermFlattenerAt f x I ↔ ∀ J, FlatOverAt f x J ↔ I ≤ J :=
  Iff.rfl

/-- The pointed flattener is the flattener ideal of the fibre stalk map. -/
theorem isPointFlattenerAt_iff {x : X.obj.left} {y : Y.obj.left} {h : f.hom.left.base y = x}
    {I : Ideal (X.obj.left.presheaf.stalk x)} :
    IsPointFlattenerAt f x y h I ↔ IsFlattenerIdeal (fibreStalkMap f x y h) I :=
  Iff.rfl

/-- Flatness over `V(J)` passes to smaller germs `V(K)`, `J ≤ K` (base change). -/
theorem FlatOverAt.mono {x : X.obj.left} {J K : Ideal (X.obj.left.presheaf.stalk x)} (hJK : J ≤ K)
    (h : FlatOverAt f x J) : FlatOverAt f x K :=
  fun y hy => flat_quotMap_of_le _ hJK (h y hy)

/-- Over the whole germ: `FlatOverAt f x ⊥` is flatness of `f` at every point of the fibre. -/
theorem flatOverAt_bot_iff {x : X.obj.left} :
    FlatOverAt f x ⊥ ↔ ∀ y, f.hom.left.base y = x → (f.hom.left.stalkMap y).hom.Flat := by
  refine forall₂_congr fun y hy => ?_
  rw [flat_quotMap_bot_iff, fibreStalkMap,
    RingHom.Flat.comp_iff_of_bijective_right (ConcreteCategory.bijective_of_isIso _)]

/-- Every family is flat over the reduced point. -/
theorem flatOverAt_maximalIdeal (x : X.obj.left) :
    FlatOverAt f x (IsLocalRing.maximalIdeal (X.obj.left.presheaf.stalk x)) :=
  fun _ _ => flat_quotMap_of_isMaximal _ _

/-- `f` is flat over `V(⊥)` at the fibre over `x` iff `x` is not in the non-flat image. -/
theorem flatOverAt_bot_iff_not_mem_nonflatImage {x : X.obj.left} :
    FlatOverAt f x ⊥ ↔ x ∉ nonflatImage f := by
  rw [flatOverAt_bot_iff, mem_nonflatImage_iff]

/-- **The sum of the pointed flatteners over the fibre is the whole-fibre flattener** (Hironaka
p. 527: the flattener of `∏ E^x/J^x`). -/
theorem isGermFlattenerAt_iSup {x : X.obj.left}
    (P : ∀ y : Y.obj.left, f.hom.left.base y = x → Ideal (X.obj.left.presheaf.stalk x))
    (hP : ∀ y h, IsPointFlattenerAt f x y h (P y h)) :
    IsGermFlattenerAt f x (⨆ (y) (h), P y h) := by
  intro J
  simp only [iSup_le_iff]
  exact forall₂_congr fun y h => hP y h J

/-- Uniqueness of the whole-fibre flattener (germ form of Rem. 2.4.4, p. 529). -/
theorem isGermFlattenerAt_unique {x : X.obj.left} {I I' : Ideal (X.obj.left.presheaf.stalk x)}
    (h : IsGermFlattenerAt f x I) (h' : IsGermFlattenerAt f x I') : I = I' :=
  le_antisymm ((h I').1 ((h' I').2 le_rfl)) ((h' I).1 ((h I).2 le_rfl))

/-- `f` is flat over its flattener. -/
theorem flatOverAt_of_isGermFlattenerAt {x : X.obj.left} {I : Ideal (X.obj.left.presheaf.stalk x)}
    (h : IsGermFlattenerAt f x I) : FlatOverAt f x I :=
  (h I).2 le_rfl

/-- The flattener lies in the maximal ideal. -/
theorem le_maximalIdeal_of_isGermFlattenerAt {x : X.obj.left}
    {I : Ideal (X.obj.left.presheaf.stalk x)} (h : IsGermFlattenerAt f x I) :
    I ≤ IsLocalRing.maximalIdeal _ :=
  (h _).1 (flatOverAt_maximalIdeal x)

/-- The flattener is a proper ideal. -/
theorem ne_top_of_isGermFlattenerAt {x : X.obj.left} {I : Ideal (X.obj.left.presheaf.stalk x)}
    (h : IsGermFlattenerAt f x I) : I ≠ ⊤ := fun hI =>
  (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    (top_le_iff.1 (hI ▸ le_maximalIdeal_of_isGermFlattenerAt h))

/-- The flattener is `⊥` exactly over flat points. -/
theorem isGermFlattenerAt_bot_iff {x : X.obj.left} : IsGermFlattenerAt f x ⊥ ↔ FlatOverAt f x ⊥ :=
  ⟨fun h => (h ⊥).2 le_rfl, fun h _ => ⟨fun _ => bot_le, fun _ => h.mono bot_le⟩⟩

/-- The flattener is `⊥` exactly outside the non-flat image. -/
theorem eq_bot_iff_of_isGermFlattenerAt {x : X.obj.left} {I : Ideal (X.obj.left.presheaf.stalk x)}
    (h : IsGermFlattenerAt f x I) : I = ⊥ ↔ x ∉ nonflatImage f := by
  rw [← flatOverAt_bot_iff_not_mem_nonflatImage, ← isGermFlattenerAt_bot_iff]
  exact ⟨fun hI => hI ▸ h, fun h' => isGermFlattenerAt_unique h h'⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
