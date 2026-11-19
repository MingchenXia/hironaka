import Hironaka.Resolution.HironakaNativeOriginalRestrictionComparison
import Hironaka.Resolution.HironakaG10PNLayerStep

/-! Exactness of the actual local restriction of native original modules, and restriction to a
smaller original open (lane G10P, runs 0079/0080; ingredient of `G10.PN.5.bottom_exact_restrict` /
`G10.PN.8.exact_restrict`).  Blueprint: `hironaka-g10-pn-restriction-exact.tex`.

* Presheaf pushforward of modules preserves every limit indexed by a small category (limits are
  sectionwise); sheaf pushforward along a continuous functor therefore preserves every finite limit.
* The actual local restriction `localOriginalRestrictionFunctor U D` (restriction over `D`, then the
  accepted local equivalence and native realization) preserves finite limits, all colimits and zero
  morphisms: `overFunctor` is a left adjoint (`overPushforwardOverAdj`), the rest are equivalences.
* `restrictTo W Ω h` is that restriction to `inverseImageOpen W Ω`, transported to the literal open
  `Ω` along `original_image_inverseImage`; it inherits all three properties, and restricting first to
  the image open of `V` and then to `Ω` is naturally isomorphic to restricting directly to `Ω`.
Hence kernel forks and cokernel coforks stay limiting/colimiting after restriction. -/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaG10PNRestrictionExact

open HironakaChowNativeLocalOverStalkTransport HironakaChowNativeLocalOverFiniteDataTransport
  HironakaChowNativeArbitraryOverRealization HironakaSingularModuleSheafStalk
  HironakaNativeCanonicalSupportRestriction HironakaNativeCyclicCokernelRestriction
  HironakaChowNativePrimeSupportContinuation HironakaNativeOriginalRestrictionComparison
  HironakaG10PNLayerStep HironakaChowNativeFreePartContinuation

noncomputable section

universe u₁ u₂ v₁ v₂

section Presheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{0}} {S : Cᵒᵖ ⥤ RingCat.{0}} (φ : S ⟶ F.op ⋙ R)

/-- Presheaf pushforward of modules maps every limit cone indexed by a small category of `Type`
to a limit cone: limits of presheaves of modules are computed sectionwise, and restriction of
scalars preserves limits. -/
def presheafPushforwardIsLimit {I : Type} [SmallCategory I]
    {K : I ⥤ PresheafOfModules.{0} R} {c : Cone K} (hc : IsLimit c) :
    IsLimit ((PresheafOfModules.pushforward.{0} φ).mapCone c) := by
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro X
  exact isLimitOfPreserves (ModuleCat.restrictScalars.{0} (φ.app X).hom)
    (isLimitOfPreserves (PresheafOfModules.evaluation.{0} R (F.op.obj X)) hc)

end Presheaf

section Sheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}} [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{0} J K).obj R)

/-- Sheaf pushforward of modules maps every finite limit cone to a limit cone. -/
def sheafPushforwardIsLimit {I : Type} [SmallCategory I] [FinCategory I]
    {G : I ⥤ SheafOfModules.{0} R} {c : Cone G} (hc : IsLimit c) :
    IsLimit ((SheafOfModules.pushforward.{0} φ).mapCone c) := by
  apply isLimitOfReflects (SheafOfModules.forget.{0} S)
  exact presheafPushforwardIsLimit φ.hom (isLimitOfPreserves (SheafOfModules.forget.{0} R) hc)

/-- Sheaf pushforward of modules preserves finite limits. -/
theorem sheafPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.pushforward.{0} φ) where
  preservesFiniteLimits _ _ _ := ⟨fun {_} => ⟨fun hc => ⟨sheafPushforwardIsLimit φ hc⟩⟩⟩

end Sheaf

section Local

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency.types false in
instance overFunctor_preservesFiniteLimits (U : Opens (ComplexModel n)) (D : Opens U) :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{0} (forgetRing (originalOpenStructureSheaf U)) D) :=
  sheafPushforward_preservesFiniteLimits _

set_option backward.isDefEq.respectTransparency.types false in
instance overFunctor_isLeftAdjoint (U : Opens (ComplexModel n)) (D : Opens U) :
    (SheafOfModules.overFunctor.{0} (forgetRing (originalOpenStructureSheaf U)) D).IsLeftAdjoint :=
  inferInstanceAs (SheafOfModules.pushforward.{0}
    (𝟙 ((forgetRing (originalOpenStructureSheaf U)).over D))).IsLeftAdjoint

set_option backward.isDefEq.respectTransparency.types false in
instance localOverTransport_isEquivalence (U : Opens (ComplexModel n)) (D : Opens U) :
    (localOverTransport (originalSpace n) U D).IsEquivalence := by
  unfold localOverTransport realizationFunctor
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction over `D` followed by the local equivalences is a left adjoint
(`overPushforwardOverAdj` composed with the adjunction of an equivalence). -/
instance localOriginalRestriction_isLeftAdjoint (U : Opens (ComplexModel n)) (D : Opens U) :
    (localOriginalRestrictionFunctor U D).IsLeftAdjoint :=
  ⟨_, ⟨(SheafOfModules.overPushforwardOverAdj
      (R := forgetRing (originalOpenStructureSheaf U)) D).comp
    (localOverTransport (originalSpace n) U D).asEquivalence.toAdjunction⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
instance localOriginalRestriction_preservesFiniteLimits (U : Opens (ComplexModel n))
    (D : Opens U) : PreservesFiniteLimits (localOriginalRestrictionFunctor U D) := by
  change PreservesFiniteLimits
    (SheafOfModules.overFunctor.{0} (forgetRing (originalOpenStructureSheaf U)) D ⋙
      localOverTransport (originalSpace n) U D)
  have hF : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{0} (forgetRing (originalOpenStructureSheaf U)) D) :=
    overFunctor_preservesFiniteLimits U D
  have : PreservesLimitsOfSize.{0, 0} (localOverTransport (originalSpace n) U D) :=
    (localOverTransport (originalSpace n) U D).asEquivalence.symm.toAdjunction.rightAdjoint_preservesLimits
  have hS : PreservesFiniteLimits (localOverTransport (originalSpace n) U D) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hF hS

instance localOriginalRestriction_preservesColimits (U : Opens (ComplexModel n))
    (D : Opens U) : PreservesColimitsOfSize.{0, 0} (localOriginalRestrictionFunctor U D) :=
  inferInstance

instance localOriginalRestriction_preservesZeroMorphisms (U : Opens (ComplexModel n))
    (D : Opens U) : (localOriginalRestrictionFunctor U D).PreservesZeroMorphisms :=
  inferInstance

instance originalModuleCategoryTransport_isEquivalence {B C : Opens (ComplexModel n)}
    (h : B = C) : (originalModuleCategoryTransport h).IsEquivalence := by
  subst h
  exact inferInstanceAs (𝟭 (OriginalModules B)).IsEquivalence

/-- Transports along two equalities of original opens compose to the transport along any third. -/
def transportCompIso {B C E : Opens (ComplexModel n)} (h₁ : B = C) (h₂ : C = E) (h₃ : B = E) :
    originalModuleCategoryTransport h₁ ⋙ originalModuleCategoryTransport h₂ ≅
      originalModuleCategoryTransport h₃ := by
  subst h₁
  subst h₂
  exact Iso.refl _

/-- Restriction of an original module on `W` to a smaller original open `Ω ≤ W`, landing on the
literal open `Ω`. -/
def restrictTo (W Ω : Opens (ComplexModel n)) (h : Ω ≤ W) :
    OriginalModules W ⥤ OriginalModules Ω :=
  localOriginalRestrictionFunctor W (inverseImageOpen W Ω) ⋙
    originalModuleCategoryTransport (original_image_inverseImage W Ω h)

instance originalModuleCategoryTransport_preservesFiniteLimits {B C : Opens (ComplexModel n)}
    (h : B = C) : PreservesFiniteLimits (originalModuleCategoryTransport h) := by
  subst h
  exact inferInstanceAs (PreservesFiniteLimits (𝟭 (OriginalModules B)))

instance restrictTo_preservesFiniteLimits (W Ω : Opens (ComplexModel n)) (h : Ω ≤ W) :
    PreservesFiniteLimits (restrictTo W Ω h) :=
  @comp_preservesFiniteLimits _ _ _ _ _ _ _ _
    (localOriginalRestriction_preservesFiniteLimits W (inverseImageOpen W Ω))
    (originalModuleCategoryTransport_preservesFiniteLimits (original_image_inverseImage W Ω h))

instance restrictTo_isLeftAdjoint (W Ω : Opens (ComplexModel n)) (h : Ω ≤ W) :
    (restrictTo W Ω h).IsLeftAdjoint := by
  unfold restrictTo
  infer_instance

instance restrictTo_preservesColimits (W Ω : Opens (ComplexModel n)) (h : Ω ≤ W) :
    PreservesColimitsOfSize.{0, 0} (restrictTo W Ω h) :=
  inferInstance

instance restrictTo_preservesZeroMorphisms (W Ω : Opens (ComplexModel n)) (h : Ω ≤ W) :
    (restrictTo W Ω h).PreservesZeroMorphisms :=
  inferInstance

/-- A limiting kernel fork on `W` restricts to a limiting kernel fork on `Ω`. -/
def restrictToKernelForkIsLimit (W Ω : Opens (ComplexModel n)) (h : Ω ≤ W)
    {M N : OriginalModules W} {f : M ⟶ N} (c : KernelFork f) (hc : IsLimit c) :
    IsLimit (c.map (restrictTo W Ω h)) :=
  c.mapIsLimit hc (restrictTo W Ω h)

/-- A colimiting cokernel cofork on `W` restricts to a colimiting cokernel cofork on `Ω`. -/
def restrictToCokernelCoforkIsColimit (W Ω : Opens (ComplexModel n)) (h : Ω ≤ W)
    {M N : OriginalModules W} {f : M ⟶ N} (c : CokernelCofork f) (hc : IsColimit c) :
    IsColimit (c.map (restrictTo W Ω h)) :=
  c.mapIsColimit hc (restrictTo W Ω h)

/-- The same statements for the actual local restriction to an image open. -/
def localRestrictionKernelForkIsLimit (W : Opens (ComplexModel n)) (V : Opens W)
    {M N : OriginalModules W} {f : M ⟶ N} (c : KernelFork f) (hc : IsLimit c) :
    IsLimit (c.map (localOriginalRestrictionFunctor W V)) :=
  c.mapIsLimit hc (localOriginalRestrictionFunctor W V)

def localRestrictionCokernelCoforkIsColimit (W : Opens (ComplexModel n)) (V : Opens W)
    {M N : OriginalModules W} {f : M ⟶ N} (c : CokernelCofork f) (hc : IsColimit c) :
    IsColimit (c.map (localOriginalRestrictionFunctor W V)) :=
  c.mapIsColimit hc (localOriginalRestrictionFunctor W V)

theorem image_open_le (W : Opens (ComplexModel n)) (V : Opens W) :
    originalImageOpen W V ≤ W := by
  rintro x ⟨u, _, rfl⟩
  exact u.property

theorem inverseImage_le_of_le_image (W Ω : Opens (ComplexModel n)) (V : Opens W)
    (h : Ω ≤ originalImageOpen W V) : inverseImageOpen W Ω ≤ V := by
  intro x hx
  obtain ⟨u, hu, hux⟩ := h hx
  have : u = x := Subtype.ext hux
  exact this ▸ hu

theorem nested_open_eq (W Ω : Opens (ComplexModel n)) (V : Opens W) :
    originalNestedOpen W (inverseImageOpen W Ω) V =
      inverseImageOpen (originalImageOpen W V) Ω := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting to the image open of `V` and then to `Ω` is naturally isomorphic to restricting
directly to `Ω`. -/
def restrictToNestedIso (W Ω : Opens (ComplexModel n)) (V : Opens W)
    (h : Ω ≤ originalImageOpen W V) :
    localOriginalRestrictionFunctor W V ⋙ restrictTo (originalImageOpen W V) Ω h ≅
      restrictTo W Ω (h.trans (image_open_le W V)) := by
  let D₁ := inverseImageOpen W Ω
  have h₁₂ : D₁ ≤ V := inverseImage_le_of_le_image W Ω V h
  let e₁ := originalNestedImageEq W D₁ V h₁₂
  let e₂ := original_image_inverseImage W Ω (h.trans (image_open_le W V))
  let N := localOriginalNestedRestrictionIso W D₁ V h₁₂
  refine Functor.isoWhiskerLeft
      (localOriginalRestrictionFunctor W V ⋙ localOriginalRestrictionFunctor
        (originalImageOpen W V) (originalNestedOpen W D₁ V))
      (transportCompIso e₁ e₂ (original_image_inverseImage (originalImageOpen W V) Ω h)).symm ≪≫
    ?_
  exact Functor.isoWhiskerRight N (originalModuleCategoryTransport e₂) ≪≫
    Functor.isoWhiskerRight (localOriginalRestrictionIso W D₁).symm
      (originalModuleCategoryTransport e₂)

end Local

end

end Hironaka.HironakaG10PNRestrictionExact
