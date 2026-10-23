import DeJongAlterations.Geometry.AlgebraicFieldFiniteSNCModel
import DeJongAlterations.Geometry.AlgebraicFieldAlterationRefinement
import DeJongAlterations.Geometry.AlgebraicFieldFiniteComponentModel
import DeJongAlterations.Geometry.AlterationBoundaryScalarDescent
import DeJongAlterations.Theorem
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Full native arbitrary-field reduction, retaining original varieties, closed sets and entire diagrams. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.AlgebraicFieldAlterationReduction

open StableModification.Limits AlgebraicFieldFiniteModel AlgebraicFieldFiniteComponentModel
  AlgebraicFieldFiniteAlterationModel FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

/-- The ACTUAL full scalar theorem INTERNALLY constructs every original arbitrary-field
alteration, compactification, entire prescribed SNC boundary and whole original coefficient maps. -/
theorem deJongAlterationTheorem_of_scalar_theorem
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] [PerfectField L]
    (hL : DeJongAlterationTheorem L) : DeJongAlterationTheorem k := by
  intro X p hp Z hZ
  let : IsVariety p := hp
  obtain ⟨C, E, hE, CE, qE, gE, ιE, hqE, hιE, hιEf, HE, _, hwholeX, hfinE, haltE⟩ :=
    exists_original_finite_component_alteration k L p
  let cL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let XL := pullback p cL
  let CL := reducedComponent XL C
  let ιL : CL ⟶ XL := reducedComponentInclusion XL C
  let qL := ιL ≫ pullback.snd p cL
  let tL := ιL ≫ pullback.fst p cL
  let tE := ιE ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E)))
  change gE ≫ tE = tL at hwholeX
  let : IsVariety qL := ⟨⟩
  let : FiniteDimensional k E := hE
  let : IsVariety qE := hqE
  let : IsAlteration tE := haltE
  let cE : Spec (.of L) ⟶ Spec (.of E) := Spec.map (CommRingCat.ofHom E.val.toRingHom)
  let : Surjective cE := ⟨fun y => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ y⟩⟩
  let : Surjective gE := MorphismProperty.of_isPullback HE.flip inferInstance
  let : Surjective tL := by rw [← hwholeX]; infer_instance
  let ZL : Closeds CL := Z.preimage tL.continuous
  have hZL : ZL ≠ ⊤ := by
    intro heq
    apply hZ
    ext x
    obtain ⟨y, rfl⟩ := tL.surjective x
    have hy : y ∈ ZL := by rw [heq]; trivial
    exact ⟨fun _ => trivial, fun _ => hy⟩
  obtain ⟨d⟩ := hL CL qL inferInstance ZL hZL
  let : IsVariety d.sourceStructure := d.sourceVariety
  let : IsVariety d.compactificationStructure := d.compactificationVariety
  let : IsAlteration d.alteration := d.isAlteration
  let : IsOpenImmersion d.inclusion := d.isOpenImmersion
  let : LocallyOfFinitePresentation qE :=
    SpreadModification.locallyOfFinitePresentation_of_locallyOfFiniteType qE
  let i : Index k L := Opposite.op ⟨E.toSubalgebra,
    ⟨(Subalgebra.fg_iff_finiteType E.toSubalgebra).mpr inferInstance, le_top⟩⟩
  let rC : Model (diagram k L) (scalarCone k L) qL i :=
    { Y := CE, fY := qE, g := gE, isPullback := by rw [scalarCone_π]; exact HE }
  have hrC : rC.IsFP := by
    dsimp only [Model.IsFP, rC]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨j, hj, mA, mC, mB, πC, a₀, b₀, hmA, hmC, hmB, hvA, hvC, hvB,
      ha₀alt, hb₀open, hsB, _, hpB, _, HπC, hπCfin, hgπC, ha₀, hb₀, hga₀, hgb₀, _, _⟩ :=
    exists_finite_alteration_model k L d.sourceStructure qL d.compactificationStructure
      d.alteration d.inclusion d.alterationOver d.inclusionOver d.regular d.projective rC hrC
  let : IsVariety (k := levelField k L j) mA.fY := hvA
  let : IsVariety (k := levelField k L j) mC.fY := hvC
  let : IsVariety (k := levelField k L j) mB.fY := hvB
  let : IsAlteration a₀ := ha₀alt
  let : IsOpenImmersion b₀ := hb₀open
  let : Smooth mB.fY := hsB
  let : LocallyOfFinitePresentation d.compactificationStructure :=
    SpreadModification.locallyOfFinitePresentation_of_locallyOfFiniteType _
  obtain ⟨l, h, D₀, hsnc, hD₀⟩ := AlgebraicFieldFiniteSNCModel.exists_snc_model k L
    d.compactificationStructure d.boundary d.normalCrossings mB hmB
  obtain ⟨a₁, b₁, hvA₁, hvC₁, hvB₁, ha₁alt, hb₁open, _, hregB₁, _, hpB₁,
      hprojfin, ha₁, hb₁, hga₁, hgb₁, _, Hb₁⟩ :=
    AlgebraicFieldAlterationRefinement.refine_diagram k L d.sourceStructure qL
      d.compactificationStructure d.alteration d.inclusion d.alterationOver d.inclusionOver
      mA mC mB hmA hmC hmB hpB a₀ b₀ ha₀ hb₀ hga₀ hgb₀ h
  let MA := mA.baseChange h
  let MC := mC.baseChange h
  let MB := mB.baseChange h
  let : IsVariety (k := levelField k L l) MA.fY := hvA₁
  let : IsVariety (k := levelField k L l) MC.fY := hvC₁
  let : IsVariety (k := levelField k L l) MB.fY := hvB₁
  let : IsAlteration a₁ := ha₁alt
  let : IsOpenImmersion b₁ := hb₁open
  let π : MC.Y ⟶ CE := pullback.fst mC.fY ((diagram k L).map h) ≫ πC
  let : IsFinite πC := hπCfin
  let : IsFinite (pullback.fst mC.fY ((diagram k L).map h)) := hprojfin
  let : IsFinite π := inferInstance
  let : Surjective ((diagram k L).map hj) := by
    change Surjective (show Spec (.of (levelField k L j)) ⟶ Spec (.of E) from
      (diagram k L).map hj)
    exact ⟨fun y => ⟨IsLocalRing.closedPoint (levelField k L j), Subsingleton.elim _ y⟩⟩
  let : Surjective πC := MorphismProperty.of_isPullback HπC.flip inferInstance
  let : Surjective ((diagram k L).map h) := by
    change Surjective (show Spec (.of (levelField k L l)) ⟶ Spec (.of (levelField k L j)) from
      (diagram k L).map h)
    exact ⟨fun y => ⟨IsLocalRing.closedPoint (levelField k L l), Subsingleton.elim _ y⟩⟩
  let : Surjective π := inferInstance
  let : IsAlteration π := isAlteration_of_isFinite π
  let : IsAlteration (π ≫ tE) := IsAlteration.comp π tE
  let f := a₁ ≫ π ≫ tE
  let : IsAlteration f := IsAlteration.comp a₁ (π ≫ tE)
  let qA := MA.fY ≫ Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L l)))
  let qB := MB.fY ≫ Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L l)))
  let : FiniteDimensional k (levelField k L l) := levelField_finiteDimensional k L l
  let : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L l)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hb : b₁ ≫ qB = qA := by
    dsimp only [qA, qB]
    rw [← Category.assoc, hb₁]
  let : IsProper qB := hpB₁.isProper
  let : IsSeparated qA := by rw [← hb]; infer_instance
  let : LocallyOfFiniteType qA := by rw [← hb]; infer_instance
  let : QuasiCompact qA := MorphismProperty.comp_mem (@QuasiCompact) MA.fY
    (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L l)))) hvA₁.toQuasiCompact inferInstance
  let : IsVariety qA := ⟨⟩
  let : IsVariety qB := ⟨⟩
  have ht : tE ≫ p = qE ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
    dsimp only [tE]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hιEf]
  have hπ : π ≫ qE = MC.fY ≫ (diagram k L).map (h ≫ hj) := by
    change (pullback.fst mC.fY ((diagram k L).map h) ≫ πC) ≫ qE = _
    rw [Category.assoc, HπC.w, ← Category.assoc, pullback.condition, Category.assoc,
      ← Functor.map_comp]
    rfl
  have hfield : (diagram k L).map (h ≫ hj) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k E)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L l))) :=
    AlgebraicFieldOriginalScalarModel.diagram_map_coefficient k L (h ≫ hj)
  have hf : f ≫ p = qA := by
    calc
      f ≫ p = a₁ ≫ π ≫ tE ≫ p := by simp only [f, Category.assoc]
      _ = a₁ ≫ π ≫ qE ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by rw [ht]
      _ = a₁ ≫ MC.fY ≫ (diagram k L).map (h ≫ hj) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k E)) := by rw [reassoc_of% hπ]; rfl
      _ = MA.fY ≫ (diagram k L).map (h ≫ hj) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k E)) := by rw [reassoc_of% ha₁]
      _ = qA := by rw [hfield]
  have hgπ : MC.g ≫ π = gE := by
    have hproj : MC.g ≫ pullback.fst mC.fY ((diagram k L).map h) = mC.g := by
      simp [MC, Model.baseChange]
    dsimp only [π]
    rw [← Category.assoc, hproj, hgπC]
  have hfL : MA.g ≫ f = d.alteration ≫ tL := by
    calc
      MA.g ≫ f = (MA.g ≫ a₁) ≫ π ≫ tE := by simp only [f, Category.assoc]
      _ = (d.alteration ≫ MC.g) ≫ π ≫ tE := by rw [hga₁]
      _ = d.alteration ≫ (MC.g ≫ π) ≫ tE := by simp only [Category.assoc]
      _ = d.alteration ≫ gE ≫ tE := by rw [hgπ]
      _ = d.alteration ≫ tL := by rw [hwholeX]
  let cB : Spec (.of L) ⟶ Spec (.of (levelField k L l)) :=
    Spec.map (CommRingCat.ofHom (levelField k L l).val.toRingHom)
  let : Surjective cB := ⟨fun y => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ y⟩⟩
  have HB : IsPullback MB.g d.compactificationStructure MB.fY cB := by
    simpa only [scalarCone_π] using MB.isPullback
  let : Surjective MB.g := MorphismProperty.of_isPullback HB.flip inferInstance
  have hpre : (d.alteration ≫ tL) ⁻¹' (Z : Set X) = d.alteration ⁻¹' (ZL : Set CL) := by
    ext x
    rfl
  have hsupportL : (d.boundary.support : Set d.compactification) =
      d.inclusion '' ((d.alteration ≫ tL) ⁻¹' (Z : Set X)) ∪ (Set.range d.inclusion)ᶜ := by
    rw [hpre]
    exact d.boundarySupport
  have hsupport := AlterationBoundaryScalarDescent.boundary_support_of_isPullback Hb₁
    (d.alteration ≫ tL) f hfL (Z : Set X) D₀ d.boundary hD₀ hsupportL
  exact ⟨{
    source := MA.Y
    compactification := MB.Y
    sourceStructure := qA
    compactificationStructure := qB
    alteration := f
    inclusion := b₁
    boundary := D₀
    sourceVariety := inferInstance
    compactificationVariety := inferInstance
    alterationOver := hf
    inclusionOver := hb
    isAlteration := inferInstance
    isOpenImmersion := inferInstance
    projective := hpB₁
    regular := hregB₁
    normalCrossings := hsnc
    boundarySupport := hsupport }⟩

/-- The actual algebraic-closure theorem suffices for the full native theorem over ANY original field. -/
theorem deJongAlterationTheorem_of_algebraicClosure (k : Type u) [Field k]
    (h : DeJongAlterationTheorem (AlgebraicClosure k)) : DeJongAlterationTheorem k :=
  deJongAlterationTheorem_of_scalar_theorem k (AlgebraicClosure k) h

end DeJongAlterations.Geometry.AlgebraicFieldAlterationReduction
