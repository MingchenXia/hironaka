import Hironaka.Geometry.QuotGrassmannPivotTwisting

/-!
# Actual coordinate frames of the same native positive twisting sheaf

The actual inverse is constructed by homogeneous fraction division on every
original coordinate subopen. No local triviality or frame is supplied as input.
Pure frame construction adapted from BingWangEntropy/ProjectiveTwistingSheaf.lean,
source SHA256 ba9b02873b50ce110c6fea0ce797395a3febfd23a4ab513710120f726844c238.
The native open-subscheme comparison follows NativeLinePullbackFrames.lean,
source SHA256 bc8833ac017958913b75ed024f5d27fca0a7affce371985666b9e4167f1938ca.
-/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopCat TopologicalSpace
open scoped DirectSum

namespace Hironaka.Geometry.QuotGrassmann.Twisting

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Multiplication by the actual coordinate section is a genuine structure-ring linear map. -/
def projectiveTwistingCoordinateMul (k : ℕ) (a : 𝒜 1) (U : (Proj 𝒜).Opens) :
    Γ(Proj 𝒜, U) →ₗ[Γ(Proj 𝒜, U)] projectiveTwistingSections 𝒜 k U :=
  LinearMap.toSpanSingleton _ _ (projectiveTwistingCoordinateSection 𝒜 k a U)

/-- The coordinate is invertible in each actual full prime localization on its true basic open. -/
theorem projectiveTwistingCoordinate_isUnit (a : 𝒜 1) (x : Proj 𝒜)
    (hx : x ∈ Proj.basicOpen 𝒜 a.val) :
    IsUnit (algebraMap A (projectiveTwistingFiber 𝒜 x) a.val) :=
  IsLocalization.map_units (projectiveTwistingFiber 𝒜 x)
    (⟨a.val, (Proj.mem_basicOpen 𝒜 a.val x).mp hx⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)

/-- No injectivity premise is used for the actual local coordinate frame. -/
theorem projectiveTwistingCoordinateMul_injective (k : ℕ) (a : 𝒜 1)
    (U : (Proj 𝒜).Opens) (hU : U ≤ Proj.basicOpen 𝒜 a.val) :
    Function.Injective (projectiveTwistingCoordinateMul 𝒜 k a U) := by
  intro r s h
  apply AlgebraicGeometry.Proj.ext
  funext x
  apply HomogeneousLocalization.val_injective
  have hx : IsUnit (algebraMap A (projectiveTwistingFiber 𝒜 x.val) (a.val ^ k)) := by
    rw [map_pow]
    exact (projectiveTwistingCoordinate_isUnit 𝒜 a x.val (hU x.property)).pow k
  apply hx.mul_left_inj.mp
  exact congrArg (fun t : projectiveTwistingSections 𝒜 k U => t.val x) h

/-- Actual localization arithmetic cancels the inverted coordinate denominator. -/
theorem projectiveTwistingFraction_cancel_coordinate (k : ℕ) (a : 𝒜 1)
    (x : Proj 𝒜) (ha : a.val ∉ x.asHomogeneousIdeal) (p q : A)
    (hq : q ∉ x.asHomogeneousIdeal) :
    Localization.mk p
        (⟨q * a.val ^ k, x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
          hq (x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem ha k)⟩ :
            x.asHomogeneousIdeal.toIdeal.primeCompl) *
      algebraMap A (projectiveTwistingFiber 𝒜 x) (a.val ^ k) =
        Localization.mk p ⟨q, hq⟩ := by
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_eq_r']
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, mul_one]
  ring

/-- A genuine shifted fraction has an actual degree-zero coefficient after coordinate division. -/
theorem projectiveTwistingChartCoefficient_exists (k : ℕ) (a : 𝒜 1)
    (x : Proj 𝒜) (ha : a.val ∉ x.asHomogeneousIdeal)
    (d : ℕ) (p : 𝒜 (d + k)) (q : 𝒜 d) (hq : q.val ∉ x.asHomogeneousIdeal) :
    ∃ r : HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal,
      r.val * algebraMap A (projectiveTwistingFiber 𝒜 x) (a.val ^ k) =
        Localization.mk p.val ⟨q.val, hq⟩ := by
  refine ⟨HomogeneousLocalization.mk ⟨d + k, p,
    ⟨q.val * a.val ^ k, ?_⟩,
    x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hq
      (x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem ha k)⟩, ?_⟩
  · have hp := SetLike.pow_mem_graded k a.property
    have hm := SetLike.mul_mem_graded q.property hp
    simpa using hm
  · exact projectiveTwistingFraction_cancel_coordinate 𝒜 k a x ha p.val q.val hq

/-- Every actual shifted fraction section on a coordinate chart has a produced
actual regular coefficient. This uses local fraction witnesses and coordinate
invertibility, rather than an assumed local trivialization. -/
theorem projectiveTwistingCoordinateMul_surjective (k : ℕ) (a : 𝒜 1)
    (U : (Proj 𝒜).Opens) (hU : U ≤ Proj.basicOpen 𝒜 a.val) :
    Function.Surjective (projectiveTwistingCoordinateMul 𝒜 k a U) := by
  classical
  intro t
  have hex (x : U) : ∃ r : HomogeneousLocalization.AtPrime 𝒜
      x.val.asHomogeneousIdeal.toIdeal,
      r.val * algebraMap A (projectiveTwistingFiber 𝒜 x.val) (a.val ^ k) = t.val x := by
    obtain ⟨V, hxV, i, d, p, q, hq, ht⟩ := t.property x
    have ha := (Proj.mem_basicOpen 𝒜 a.val x.val).mp (hU x.property)
    obtain ⟨r, hr⟩ := projectiveTwistingChartCoefficient_exists 𝒜 k a x.val ha d p q
      (hq ⟨x.val, hxV⟩)
    exact ⟨r, hr.trans (ht ⟨x.val, hxV⟩).symm⟩
  let g (x : U) := Classical.choose (hex x)
  have hg (x : U) : (g x).val *
      algebraMap A (projectiveTwistingFiber 𝒜 x.val) (a.val ^ k) = t.val x :=
    Classical.choose_spec (hex x)
  have hglocal : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred g := by
    intro x
    obtain ⟨V, hxV, i, d, p, q, hq, ht⟩ := t.property x
    have hqa (y : V) : q.val * a.val ^ k ∉ y.val.asHomogeneousIdeal :=
      y.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hq y)
        (y.val.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem
          ((Proj.mem_basicOpen 𝒜 a.val y.val).mp (hU (i y).property)) k)
    have hgrade : q.val * a.val ^ k ∈ 𝒜 (d + k) := by
      simpa using SetLike.mul_mem_graded q.property (SetLike.pow_mem_graded k a.property)
    refine ⟨V, hxV, i, d + k, p, ⟨q.val * a.val ^ k, hgrade⟩, hqa, ?_⟩
    intro y
    apply HomogeneousLocalization.val_injective
    have ha := (Proj.mem_basicOpen 𝒜 a.val y.val).mp (hU (i y).property)
    have hu : IsUnit (algebraMap A (projectiveTwistingFiber 𝒜 y.val) (a.val ^ k)) := by
      rw [map_pow]
      exact (projectiveTwistingCoordinate_isUnit 𝒜 a y.val (hU (i y).property)).pow k
    apply hu.mul_left_inj.mp
    exact (hg (i y)).trans ((ht y).trans
      (projectiveTwistingFraction_cancel_coordinate 𝒜 k a y.val ha p.val q.val (hq y)).symm)
  refine ⟨⟨g, hglocal⟩, ?_⟩
  apply Subtype.ext
  funext x
  exact hg x

/-- A genuine coordinate chart has its actual twisting section linear frame. -/
def projectiveTwistingChartSectionsFrame (k : ℕ) (a : 𝒜 1)
    (U : (Proj 𝒜).Opens) (hU : U ≤ Proj.basicOpen 𝒜 a.val) :
    projectiveTwistingSections 𝒜 k U ≃ₗ[Γ(Proj 𝒜, U)] Γ(Proj 𝒜, U) :=
  (LinearEquiv.ofBijective (projectiveTwistingCoordinateMul 𝒜 k a U)
    ⟨projectiveTwistingCoordinateMul_injective 𝒜 k a U hU,
      projectiveTwistingCoordinateMul_surjective 𝒜 k a U hU⟩).symm

/-- Coordinate section multiplication respects the actual sheaf restrictions. -/
theorem projectiveTwistingCoordinateMul_restrict (k : ℕ) (a : 𝒜 1)
    {U V : (Proj 𝒜).Opens} (i : V ⟶ U) (r : Γ(Proj 𝒜, U)) :
    (projectiveTwistingPresheaf 𝒜 k).map i.op
      (projectiveTwistingCoordinateMul 𝒜 k a U r) =
        projectiveTwistingCoordinateMul 𝒜 k a V ((Proj 𝒜).presheaf.map i.op r) := rfl

/-- Actual homogeneous coordinate division constructs a genuine local sheaf frame
for the actual twisting sheaf on its genuine Proj coordinate chart. -/
def projectiveTwistingCoordinateFrame (k : ℕ) (a : 𝒜 1) :
    (projectiveTwistingSheaf 𝒜 k).over (Proj.basicOpen 𝒜 a.val) ≅
      SheafOfModules.unit ((Proj 𝒜).ringCatSheaf.over (Proj.basicOpen 𝒜 a.val)) := by
  let T := projectiveTwistingSheaf 𝒜 k
  let U := Proj.basicOpen 𝒜 a.val
  let e : (SheafOfModules.unit ((Proj 𝒜).ringCatSheaf.over U)).val ≅ (T.over U).val :=
    PresheafOfModules.isoMk
      (fun V => (projectiveTwistingChartSectionsFrame 𝒜 k a V.unop.left
        V.unop.hom.le).symm.toModuleIso)
      (by
        intro V W i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        exact projectiveTwistingCoordinateMul_restrict 𝒜 k a i.unop.left r)
  exact ((SheafOfModules.fullyFaithfulForget ((Proj 𝒜).ringCatSheaf.over U)).preimageIso
    (X := SheafOfModules.unit ((Proj 𝒜).ringCatSheaf.over U)) (Y := T.over U) e).symm

/-- The same actual coordinate frame on the literal native coordinate-open subscheme. -/
def originalCoordinateRestrictionFrame (k : ℕ) (a : 𝒜 1) :
    (projectiveTwistingSheaf 𝒜 k).restrict (Proj.basicOpen 𝒜 a.val).ι ≅
      SheafOfModules.unit (Proj.basicOpen 𝒜 a.val).toScheme.ringCatSheaf :=
  let U := Proj.basicOpen 𝒜 a.val
  ((Scheme.Modules.overFunctorEquiv U).app (projectiveTwistingSheaf 𝒜 k)).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso (projectiveTwistingCoordinateFrame 𝒜 k a) ≪≫
    (Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit (Proj 𝒜).ringCatSheaf) ≪≫
    Scheme.Modules.restrictUnitIso U.ι

/-- The actual native away-coordinate ratio, after the native Proj section map,
multiplies the original coordinate to the other actual original coordinate. -/
theorem originalCoordinateAwayRatio_mul (a b : 𝒜 1)
    (x : Proj.basicOpen 𝒜 a.val) :
    (((ProjectiveSpectrum.Proj.awayToSection 𝒜 a.val)
      (HomogeneousLocalization.Away.mk 𝒜 a.property 1 b.val
        b.property)).val x).val *
      algebraMap A (projectiveTwistingFiber 𝒜 x.val) a.val =
        algebraMap A (projectiveTwistingFiber 𝒜 x.val) b.val := by
  have ha := (Proj.mem_basicOpen 𝒜 a.val x.val).mp x.property
  change Localization.mk b.val
    (⟨a.val ^ 1, x.val.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem ha 1⟩ :
      x.val.asHomogeneousIdeal.toIdeal.primeCompl) *
      algebraMap A (projectiveTwistingFiber 𝒜 x.val) a.val =
        algebraMap A (projectiveTwistingFiber 𝒜 x.val) b.val
  simp only [pow_one]
  rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_eq_r']
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, mul_one]
  exact mul_comm _ _

/-- The actual original degree-one chart frame sends the other original global
coordinate to its literal native away-coordinate ratio, without reducing the ring. -/
theorem originalCoordinateChartFrame_ratio (a b : 𝒜 1) :
    projectiveTwistingChartSectionsFrame 𝒜 1 a (Proj.basicOpen 𝒜 a.val) le_rfl
      (projectiveTwistingCoordinateSection 𝒜 1 b (Proj.basicOpen 𝒜 a.val)) =
    (ProjectiveSpectrum.Proj.awayToSection 𝒜 a.val)
      (HomogeneousLocalization.Away.mk 𝒜 a.property 1 b.val
        b.property) := by
  apply (projectiveTwistingChartSectionsFrame 𝒜 1 a
    (Proj.basicOpen 𝒜 a.val) le_rfl).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  funext x
  change algebraMap A (projectiveTwistingFiber 𝒜 x.val) (b.val ^ 1) =
    (((ProjectiveSpectrum.Proj.awayToSection 𝒜 a.val)
      (HomogeneousLocalization.Away.mk 𝒜 a.property 1 b.val
        b.property)).val x).val *
      algebraMap A (projectiveTwistingFiber 𝒜 x.val) (a.val ^ 1)
  simpa only [pow_one] using (originalCoordinateAwayRatio_mul 𝒜 a b x).symm

/-- The coefficient formula belongs to the actual native sheaf isomorphism itself. -/
theorem originalNativeCoordinateFrame_ratio (a b : 𝒜 1) :
    (projectiveTwistingCoordinateFrame 𝒜 1 a).hom.val.app
      (.op (Over.mk (𝟙 (Proj.basicOpen 𝒜 a.val))))
      (projectiveTwistingCoordinateSection 𝒜 1 b (Proj.basicOpen 𝒜 a.val)) =
    (ProjectiveSpectrum.Proj.awayToSection 𝒜 a.val)
      (HomogeneousLocalization.Away.mk 𝒜 a.property 1 b.val b.property) := by
  exact originalCoordinateChartFrame_ratio 𝒜 a b

end Hironaka.Geometry.QuotGrassmann.Twisting
