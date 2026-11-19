import Hironaka.Geometry.AlgebraicFieldFiniteAlterationModel
import Hironaka.Geometry.AlgebraicFieldFiniteComponentModel
import Hironaka.Geometry.AlterationTheorem

/-! The scalar theorem INTERNALLY constructs an actual regular alteration of ORIGINAL arbitrary-field X. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.AlgebraicFieldRegularAlterationReduction

open StableModification.Limits AlgebraicFieldFiniteModel AlgebraicFieldFiniteComponentModel
  AlgebraicFieldFiniteAlterationModel FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- The actual scalar theorem INTERNALLY chooses the component and finite field and produces an
ACTUAL alteration of ORIGINAL X from an open in a regular projective ORIGINAL k-variety. -/
theorem exists_original_regular_projective_alteration
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] [PerfectField L]
    (hL : DeJongAlterationTheorem L) {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsVariety p] :
    ∃ (A B : Scheme.{u}) (qA : A ⟶ Spec (.of k)) (qB : B ⟶ Spec (.of k))
      (f : A ⟶ X) (b : A ⟶ B),
      IsVariety qA ∧ IsVariety qB ∧ f ≫ p = qA ∧ b ≫ qB = qA ∧
      IsAlteration f ∧ IsOpenImmersion b ∧ IsProjectiveOver qB ∧ IsRegularScheme B := by
  obtain ⟨C, E, hE, CE, qE, gE, ιE, hqE, hιE, hιEf, HE, _, _, hfinE, haltE⟩ :=
    exists_original_finite_component_alteration k L p
  let cL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let XL := pullback p cL
  let CL := reducedComponent XL C
  let ιL : CL ⟶ XL := reducedComponentInclusion XL C
  let qL := ιL ≫ pullback.snd p cL
  let : IsVariety qL := ⟨⟩
  have hempty : (⊥ : Closeds CL) ≠ ⊤ := by
    intro heq
    have hmem : genericPoint CL ∈ (⊤ : Closeds CL) := trivial
    rw [← heq] at hmem
    exact hmem
  obtain ⟨d⟩ := hL CL qL inferInstance ⊥ hempty
  let : IsVariety d.sourceStructure := d.sourceVariety
  let : IsVariety d.compactificationStructure := d.compactificationVariety
  let : IsAlteration d.alteration := d.isAlteration
  let : IsOpenImmersion d.inclusion := d.isOpenImmersion
  let : FiniteDimensional k E := hE
  let : IsVariety qE := hqE
  let : LocallyOfFinitePresentation qE :=
    SpreadModification.locallyOfFinitePresentation_of_locallyOfFiniteType qE
  let i : Index k L := Opposite.op ⟨E.toSubalgebra,
    ⟨(Subalgebra.fg_iff_finiteType E.toSubalgebra).mpr inferInstance, le_top⟩⟩
  let rC : Model (diagram k L) (scalarCone k L) qL i :=
    { Y := CE, fY := qE, g := gE, isPullback := by
        rw [scalarCone_π]
        exact HE }
  have hrC : rC.IsFP := by
    dsimp only [Model.IsFP, rC]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨j, h, mA, mC, mB, πC, a₀, b₀, _, _, _, hvA, hvC, hvB, ha₀alt, hb₀open,
      _, hregB, _, hprojB, HπC, hπCfin, _, ha₀, hb₀, _, _, _, _⟩ :=
    exists_finite_alteration_model k L d.sourceStructure qL d.compactificationStructure
      d.alteration d.inclusion d.alterationOver d.inclusionOver d.regular d.projective rC hrC
  let : IsVariety (k := levelField k L j) mA.fY := hvA
  let : IsVariety (k := levelField k L j) mC.fY := hvC
  let : IsVariety (k := levelField k L j) mB.fY := hvB
  let : IsFinite πC := hπCfin
  let : Surjective ((diagram k L).map h) := by
    change Surjective (show Spec (.of (levelField k L j)) ⟶ Spec (.of E) from
      (diagram k L).map h)
    exact ⟨fun y => ⟨IsLocalRing.closedPoint (levelField k L j), Subsingleton.elim _ y⟩⟩
  let : Surjective πC := MorphismProperty.of_isPullback HπC.flip inferInstance
  let : IsAlteration πC := isAlteration_of_isFinite πC
  let t : CE ⟶ X := ιE ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E)))
  let : IsAlteration t := haltE
  let : IsAlteration a₀ := ha₀alt
  let : IsAlteration (πC ≫ t) := IsAlteration.comp πC t
  let f := a₀ ≫ πC ≫ t
  let : IsAlteration f := IsAlteration.comp a₀ (πC ≫ t)
  let qA := mA.fY ≫ Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L j)))
  let qB := mB.fY ≫ Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L j)))
  let : FiniteDimensional k (levelField k L j) := levelField_finiteDimensional k L j
  let : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L j)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hb : b₀ ≫ qB = qA := by
    dsimp only [qA, qB]
    rw [← Category.assoc, hb₀]
  let : IsProper qB := hprojB.isProper
  let : IsOpenImmersion b₀ := hb₀open
  let : IsSeparated qA := by rw [← hb]; infer_instance
  let : LocallyOfFiniteType qA := by rw [← hb]; infer_instance
  let : QuasiCompact qA := MorphismProperty.comp_mem (@QuasiCompact) mA.fY
    (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L j)))) hvA.toQuasiCompact inferInstance
  let : IsVariety qA := ⟨⟩
  let : IsVariety qB := ⟨⟩
  have ht : t ≫ p = qE ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
    dsimp only [t]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hιEf]
  have hπ : πC ≫ qE = mC.fY ≫ (diagram k L).map h := HπC.w
  have hfield : (diagram k L).map h ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L j))) :=
    AlgebraicFieldOriginalScalarModel.diagram_map_coefficient k L h
  have hf : f ≫ p = qA := by
    calc
      f ≫ p = a₀ ≫ πC ≫ t ≫ p := by simp only [f, Category.assoc]
      _ = a₀ ≫ πC ≫ qE ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by rw [ht]
      _ = a₀ ≫ mC.fY ≫ (diagram k L).map h ≫
          Spec.map (CommRingCat.ofHom (algebraMap k E)) := by rw [reassoc_of% hπ]; rfl
      _ = mA.fY ≫ (diagram k L).map h ≫
          Spec.map (CommRingCat.ofHom (algebraMap k E)) := by rw [reassoc_of% ha₀]
      _ = qA := by rw [hfield]
  exact ⟨mA.Y, mB.Y, qA, qB, f, b₀, inferInstance, inferInstance, hf, hb,
    inferInstance, hb₀open, hprojB, hregB⟩

/-- The scalar full theorem gives the native ORIGINAL regular alteration core, without assumed
components or finite-model descent data and without geometric integrality of original X. -/
theorem regularAlterationTheorem_of_scalar_theorem
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] [PerfectField L]
    (hL : DeJongAlterationTheorem L) : RegularAlterationTheorem k := by
  intro X p hp
  let : IsVariety p := hp
  obtain ⟨A, B, qA, qB, f, b, hA, _, hf, _, halt, hb, _, hreg⟩ :=
    exists_original_regular_projective_alteration k L hL p
  let : IsOpenImmersion b := hb
  exact ⟨A, qA, f, hA, hf, halt, hreg.of_isOpenImmersion b⟩

end Hironaka.Geometry.AlgebraicFieldRegularAlterationReduction
