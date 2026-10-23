import DeJongAlterations.Geometry.ProperSteinProjectiveCechSheafEqualizer
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# The actual ORIGINAL native homogeneous-fraction twisting sheaf

Native-only adaptation from same-workspace `BingWangEntropy/ProjectiveTwistingSheaf.lean`,
SHA256 ba9b02873b50ce110c6fea0ce797395a3febfd23a4ab513710120f726844c238.
The actual coordinate frame returns the native sheaf isomorphism itself.
No custom line-atlas definition or other-project module is imported.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopCat TopologicalSpace
open scoped DirectSum

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The actual full prime localization is the ambient fiber for shifted homogeneous fractions. -/
abbrev projectiveTwistingFiber (x : ProjectiveSpectrum 𝒜) : Type u :=
  Localization x.asHomogeneousIdeal.toIdeal.primeCompl

/-- A genuine degree-k homogeneous fraction on an open of Proj. -/
def IsTwistingFraction (k : ℕ) {U : (Proj 𝒜).Opens}
    (f : ∀ x : U, projectiveTwistingFiber 𝒜 x.val) : Prop :=
  ∃ (d : ℕ) (p : 𝒜 (d + k)) (q : 𝒜 d)
    (hq : ∀ x : U, q.val ∉ x.val.asHomogeneousIdeal),
    ∀ x : U, f x = Localization.mk p.val ⟨q.val, hq x⟩

/-- Actual fraction representations restrict to actual subopens. -/
def twistingFractionPrelocal (k : ℕ) :
    PrelocalPredicate (fun x : ProjectiveSpectrum.top 𝒜 => projectiveTwistingFiber 𝒜 x) where
  pred := IsTwistingFraction 𝒜 k
  res := by
    rintro U V i f ⟨d, p, q, hq, hf⟩
    exact ⟨d, p, q, fun x => hq (i x), fun x => hf (i x)⟩

/-- Locally actual degree-k homogeneous fractions form a genuine local predicate. -/
def twistingFractionLocal (k : ℕ) :
    LocalPredicate (fun x : ProjectiveSpectrum.top 𝒜 => projectiveTwistingFiber 𝒜 x) :=
  (twistingFractionPrelocal 𝒜 k).sheafify

/-- The underlying actual sheaf of shifted homogeneous fraction functions. -/
def projectiveTwistingSheafInTypes (k : ℕ) :
    TopCat.Sheaf (Type u) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (twistingFractionLocal 𝒜 k)

/-- The zero function is a genuine local homogeneous fraction of every degree shift. -/
theorem twistingFractionLocal_zero (k : ℕ) (U : (Proj 𝒜).Opens) :
    (twistingFractionLocal 𝒜 k).pred (0 : ∀ x : U, projectiveTwistingFiber 𝒜 x.val) := by
  apply PrelocalPredicate.sheafifyOf
  refine ⟨0, ⟨0, zero_mem _⟩, ⟨1, SetLike.one_mem_graded 𝒜⟩,
    fun x => x.val.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, ?_⟩
  intro x
  exact (Localization.mk_zero _).symm

/-- Addition of actual local shifted fractions is closed by clearing the two actual denominators. -/
theorem twistingFractionLocal_add (k : ℕ) {U : (Proj 𝒜).Opens}
    (f g : ∀ x : U, projectiveTwistingFiber 𝒜 x.val)
    (hf : (twistingFractionLocal 𝒜 k).pred f)
    (hg : (twistingFractionLocal 𝒜 k).pred g) :
    (twistingFractionLocal 𝒜 k).pred (f + g) := by
  apply (twistingFractionPrelocal 𝒜 k).sheafify_inductionOn₂'
    (twistingFractionPrelocal 𝒜 k) (twistingFractionPrelocal 𝒜 k)
    (fun a b => a + b) ?_ hf hg
  rintro V W a b ⟨d, p, q, hq, ha⟩ ⟨e, r, s, hs, hb⟩
  refine ⟨d + e, ⟨q.val * r.val + s.val * p.val, ?_⟩,
    ⟨q.val * s.val, SetLike.mul_mem_graded q.property s.property⟩,
    fun x => x.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hq ⟨x.val, x.property.1⟩) (hs ⟨x.val, x.property.2⟩), ?_⟩
  · apply add_mem
    · convert SetLike.mul_mem_graded q.property r.property using 1; congr 1; omega
    · convert SetLike.mul_mem_graded s.property p.property using 1; congr 1; omega
  · intro x
    exact (congrArg₂ (· + ·) (ha ⟨x.val, x.property.1⟩)
      (hb ⟨x.val, x.property.2⟩)).trans (Localization.add_mk _ _ _ _)

/-- Negation preserves an actual local shifted fraction representation. -/
theorem twistingFractionLocal_neg (k : ℕ) {U : (Proj 𝒜).Opens}
    (f : ∀ x : U, projectiveTwistingFiber 𝒜 x.val)
    (hf : (twistingFractionLocal 𝒜 k).pred f) :
    (twistingFractionLocal 𝒜 k).pred (-f) := by
  apply (twistingFractionPrelocal 𝒜 k).sheafify_inductionOn' (fun a => -a) ?_ hf
  rintro V a ⟨d, p, q, hq, ha⟩
  refine ⟨d, ⟨-p.val, neg_mem p.property⟩, q, hq, ?_⟩
  intro x
  exact (congrArg Neg.neg (ha x)).trans (Localization.neg_mk _ _)

/-- Actual regular Proj functions act through their true degree-zero localization values. -/
def projectiveRegularToTwistingFunctions (U : (Proj 𝒜).Opens) :
    Γ(Proj 𝒜, U) →+* (∀ x : U, projectiveTwistingFiber 𝒜 x.val) where
  toFun r x := (r.val x).val
  map_zero' := by funext x; exact HomogeneousLocalization.val_zero
  map_one' := by funext x; exact HomogeneousLocalization.val_one
  map_add' r s := by funext x; exact HomogeneousLocalization.val_add _ _
  map_mul' r s := by funext x; exact HomogeneousLocalization.val_mul _ _

/-- The ambient fraction functions use the actual structure-ring action. -/
instance projectiveTwistingFunctionsModule (U : (Proj 𝒜).Opens) :
    Module Γ(Proj 𝒜, U) (∀ x : U, projectiveTwistingFiber 𝒜 x.val) :=
  Module.compHom _ (projectiveRegularToTwistingFunctions 𝒜 U)

/-- Multiplication by an actual regular section preserves the local degree shift. -/
theorem twistingFractionLocal_smul (k : ℕ) {U : (Proj 𝒜).Opens}
    (r : Γ(Proj 𝒜, U)) (f : ∀ x : U, projectiveTwistingFiber 𝒜 x.val)
    (hf : (twistingFractionLocal 𝒜 k).pred f) :
    (twistingFractionLocal 𝒜 k).pred (r • f) := by
  intro x
  obtain ⟨V, hxV, iV, d, p, q, hq, hr⟩ := r.property x
  obtain ⟨W, hxW, iW, e, a, b, hb, hfb⟩ := hf x
  refine ⟨V ⊓ W, ⟨hxV, hxW⟩, Opens.infLELeft V W ≫ iV,
    d + e, ⟨p.val * a.val, ?_⟩,
    ⟨q.val * b.val, SetLike.mul_mem_graded q.property b.property⟩,
    fun y => y.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hq ⟨y.val, y.property.1⟩) (hb ⟨y.val, y.property.2⟩), ?_⟩
  · convert SetLike.mul_mem_graded p.property a.property using 1; congr 1; omega
  · intro y
    exact (congrArg₂ (· * ·)
      (congrArg HomogeneousLocalization.val (hr ⟨y.val, y.property.1⟩))
      (hfb ⟨y.val, y.property.2⟩)).trans (Localization.mk_mul _ _ _ _)

/-- The actual shifted fraction section space is a structure-ring submodule of actual functions. -/
def projectiveTwistingSections (k : ℕ) (U : (Proj 𝒜).Opens) :
    Submodule Γ(Proj 𝒜, U) (∀ x : U, projectiveTwistingFiber 𝒜 x.val) where
  carrier := {f | (twistingFractionLocal 𝒜 k).pred f}
  zero_mem' := twistingFractionLocal_zero 𝒜 k U
  add_mem' := by intro f g hf hg; exact twistingFractionLocal_add 𝒜 k f g hf hg
  smul_mem' := twistingFractionLocal_smul 𝒜 k

/-- The genuine shifted-fraction module presheaf has actual pointwise restriction maps. -/
def projectiveTwistingPresheaf (k : ℕ) : (Proj 𝒜).PresheafOfModules where
  obj U := ModuleCat.of Γ(Proj 𝒜, U.unop) (projectiveTwistingSections 𝒜 k U.unop)
  map {U V} i := by
    letI : Module Γ(Proj 𝒜, U.unop) (projectiveTwistingSections 𝒜 k V.unop) :=
      Module.compHom _ ((Proj 𝒜).presheaf.map i).hom
    exact ModuleCat.ofHom {
      toFun := fun s => ⟨fun x => s.val (i.unop x),
        (twistingFractionLocal 𝒜 k).res i.unop s.val s.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id U := by ext s; rfl
  map_comp i j := by ext; rfl

/-- The underlying pointwise fraction functions satisfy the genuine sheaf axiom. -/
theorem projectiveTwistingPresheaf_isSheaf (k : ℕ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (Proj 𝒜))
      (projectiveTwistingPresheaf 𝒜 k).presheaf := by
  change TopCat.Presheaf.IsSheaf (projectiveTwistingPresheaf 𝒜 k).presheaf
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mpr
  exact (projectiveTwistingSheafInTypes 𝒜 k).property

/-- The actual degree-k homogeneous-fraction sheaf of modules on the actual scheme Proj. -/
def projectiveTwistingSheaf (k : ℕ) : (Proj 𝒜).Modules where
  val := projectiveTwistingPresheaf 𝒜 k
  isSheaf := projectiveTwistingPresheaf_isSheaf 𝒜 k

/-- The actual twisting module sections are the actual shifted fraction functions. -/
def projectiveTwistingSectionsEquiv (k : ℕ) (U : (Proj 𝒜).Opens) :
    bundleSections (projectiveTwistingSheaf 𝒜 k) U ≃ₗ[Γ(Proj 𝒜, U)]
      projectiveTwistingSections 𝒜 k U := LinearEquiv.refl _ _

/-- The homogeneous coordinate power is an actual global shifted fraction section. -/
def projectiveTwistingCoordinateSection (k : ℕ) (a : 𝒜 1) (U : (Proj 𝒜).Opens) :
    projectiveTwistingSections 𝒜 k U := by
  refine ⟨fun x => algebraMap A (projectiveTwistingFiber 𝒜 x.val) (a.val ^ k), ?_⟩
  change (twistingFractionLocal 𝒜 k).pred
    (fun x : U => algebraMap A (projectiveTwistingFiber 𝒜 x.val) (a.val ^ k))
  apply PrelocalPredicate.sheafifyOf
  refine ⟨0, ⟨a.val ^ k, ?_⟩, ⟨1, SetLike.one_mem_graded 𝒜⟩,
    fun x => x.val.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, ?_⟩
  · simpa using SetLike.pow_mem_graded k a.property
  · intro x
    exact (Localization.mk_one_eq_algebraMap _).symm

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

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
