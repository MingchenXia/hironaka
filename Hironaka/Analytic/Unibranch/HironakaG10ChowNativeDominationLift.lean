import Hironaka.Analytic.Unibranch.OriginalProperBimeromorphicNative
import Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowupUniversal

/-!
# From native blowup domination to holomorphic lifts of manifold tests

The last step of the proof of `chow:dominating-ideal-existence`
(blueprint `hironaka-g10-chowside-native-flat-iso.tex`): if the native blowup
`Bl_B X → X` of a finite-type ideal of a complex manifold `X` (with dense unit locus)
factors through `f : Y → X` by a native morphism `β`, then every holomorphic map
`h : T → X` from a complex manifold along which the native pull-back of the ideal has
rank-one locally free data factors holomorphically through `f`.  The lift is the
composite of the unique native lift of `h` through the blowup with `β`; its point map is
holomorphic because every native morphism of whole manifold models is
(`OriginalProperBimeromorphicNative.nativePointMap_contMDiff`).

Main declarations:

* `exists_holomorphic_factor_of_native_domination` — the factorization.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowNativeDominationLift

open Hironaka Hironaka
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  SourceReducedComplexSpace OriginalNativeModification OriginalProperBimeromorphicNative
  OriginalFiniteIdealBlowup OriginalFiniteIdealBlowupUniversal

noncomputable section

variable {n m : ℕ} {M Y T : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace T] [ChartedSpace (ComplexModel m) T] [IsComplexManifold m T]

/-- **Native blowup domination gives holomorphic factorization of manifold tests.**
Let `f : Y → M` be holomorphic, `(B, b)` a native finite-type ideal of the whole model of
`M` with dense unit locus, and `β : Bl_B M → Y` a native morphism over `M`.  If
`h : T → M` is holomorphic and the native pull-back of `(B, b)` along `h` has rank-one
locally free data, then `h = f ∘ g` for a holomorphic `g : T → Y`. -/
theorem exists_holomorphic_factor_of_native_domination {f : Y → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (B : SheafOfModules.{0} (forgetRing (wholeModel (n := n) M).obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit
      (forgetRing (wholeModel (n := n) M).obj.left.toSheafedSpace.sheaf))
    [B.IsFiniteType]
    (hDense : Dense {x : (wholeModel (n := n) M).obj.left |
      LinearMap.range (stalkInclusionLinearMap
        (wholeModel (n := n) M).obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (β : sourceObject B b hDense ⟶ wholeModel (n := n) Y)
    (hβ : β ≫ nativeMorphism hf = projectionMorphism B b hDense)
    {h : T → M} (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h)
    (q : (nativePulledIdealModule (nativeMorphism hh).hom.left B b).LocalGeneratorsData.{0})
    (hq : q.IsLocallyFreeData) (huniq : ∀ i, Nonempty (Unique (q.generators i).I)) :
    ∃ g : T → Y, ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧ f ∘ g = h := by
  let : q.IsLocallyFreeData := hq
  let : ∀ i, Unique (q.generators i).I := fun i => Classical.choice (huniq i)
  obtain ⟨L, hL, -⟩ :=
    exists_unique_lift_of_locallyFreeData B b hDense (wholeModel (n := m) T) (nativeMorphism hh) q
  let G : wholeModel (n := m) T ⟶ wholeModel (n := n) Y := L ≫ β
  have hG : G ≫ nativeMorphism hf = nativeMorphism hh := by
    change (L ≫ β) ≫ nativeMorphism hf = _
    rw [Category.assoc, hβ, hL]
  refine ⟨nativePointMap G, nativePointMap_contMDiff G, ?_⟩
  funext t
  have hpt := congrArg (fun H : wholeModel (n := m) T ⟶ wholeModel (n := n) M =>
    (H.hom.left.base ⟨t, mem_univ t⟩).val) hG
  exact hpt

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowNativeDominationLift
