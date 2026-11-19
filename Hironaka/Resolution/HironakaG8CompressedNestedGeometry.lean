import Hironaka.Resolution.HironakaG8ConsecutiveNestedReorderings
import Hironaka.Resolution.HironakaG3EmptyAwareOpenRestriction

/-! Exact nested geometry is preserved by independently chosen physical compressions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CompressedNestedGeometry

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareOpenRestriction
  HironakaSharpActualCurveComparisonRestriction HironakaG8ConsecutiveNestedReorderings MaxLocusLocal

variable {n : ℕ} {X : CMfd.{0} n} {U V : Opens X} {A B C D : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- The nested comparison of compressed histories uses the same base map.
Its endpoint is the smaller compression followed by the original comparison
and the inverse of the literally restricted larger compression. -/
theorem compressed_nested_comparison
    {S : BlowupTower (CMfd.of (n := n) U) A} {T : BlowupTower (CMfd.of (n := n) V) B}
    {Q : BlowupTower (CMfd.of (n := n) U) C} {R : BlowupTower (CMfd.of (n := n) V) D}
    {f : CMfd.of (n := n) U ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (nestedOpens V U)}
    {e : A ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage T (nestedOpens V U))}
    (h : EmptyAwareTowerIso f S (restrict (nestedOpens V U) T) e)
    {a : C ≃ₘ⟮𝓘c,𝓘c⟯ A} {b : D ≃ₘ⟮𝓘c,𝓘c⟯ B}
    (ha : EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) U) ∞) Q S a)
    (hb : EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) V) ∞) R T b) :
    ∃ bW : CMfd.of (n := n) (openPreimage R (nestedOpens V U)) ≃ₘ⟮𝓘c,𝓘c⟯
          CMfd.of (n := n) (openPreimage T (nestedOpens V U)),
      (∀ y, (bW y).val = b y.val) ∧
      EmptyAwareTowerIso f Q (restrict (nestedOpens V U) R) (a.trans (e.trans bW.symm)) := by
  let W := nestedOpens V U
  let idV := Diffeomorph.refl 𝓘c (CMfd.of (n := n) V) ∞
  let idW := Diffeomorph.refl 𝓘c (CMfd.of (n := n) W) ∞
  let k := openRestriction idV (preimageOpen idV W) W rfl
  have hk : k = idW := Diffeomorph.ext (fun _ => rfl)
  let bW := openRestriction b (openPreimage R (preimageOpen idV W)) (openPreimage T W)
      (emptyAware_openPreimage_eq hb W)
  have hRestr : EmptyAwareTowerIso k (restrict W R) (restrict W T) bW :=
    emptyAware_open_restriction hb W
  rw [hk] at hRestr
  have hComp := G3UniverseEmptyAwareCore.trans ha
    (G3UniverseEmptyAwareCore.trans h (G3UniverseEmptyAwareCore.symm hRestr))
  have hBase : (Diffeomorph.refl 𝓘c (CMfd.of (n := n) U) ∞).trans (f.trans idW.symm) = f :=
    Diffeomorph.ext (fun _ => rfl)
  exact ⟨bW,fun _ => rfl,hBase ▸ hComp⟩

/-- Any independently chosen physical compressions retain literal nested
geometry and its underlying identity on base points. -/
theorem nestedGeometry_of_compressions
    {S : BlowupTower (CMfd.of (n := n) U) A} {T : BlowupTower (CMfd.of (n := n) V) B}
    {Q : BlowupTower (CMfd.of (n := n) U) C} {R : BlowupTower (CMfd.of (n := n) V) D}
    (h : NestedGeometry S T)
    {a : C ≃ₘ⟮𝓘c,𝓘c⟯ A} {b : D ≃ₘ⟮𝓘c,𝓘c⟯ B}
    (ha : EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) U) ∞) Q S a)
    (hb : EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) V) ∞) R T b) :
    NestedGeometry Q R := by
  obtain ⟨f,hf,e,hIso⟩ := h
  obtain ⟨bW,_,hCompressed⟩ := compressed_nested_comparison hIso ha hb
  exact ⟨f,hf,a.trans (e.trans bW.symm),hCompressed⟩

end Hironaka.HironakaG8CompressedNestedGeometry
