import DeJongAlterations.Geometry.AlgebraicFieldFiniteBoundaryFamily
import DeJongAlterations.Geometry.AlgebraicFieldFiniteIntegralModel
import DeJongAlterations.Geometry.FlatScalarIdealSheafDescent
import DeJongAlterations.Geometry.SNCLocality

/-! Actual split boundary models retain WHOLE original ideals and EVERY scheme-theoretic intersection. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.AlgebraicFieldFiniteBoundaryIdeals

open StableModification.Limits AlgebraicFieldFiniteModel AlgebraicFieldFiniteBoundaryFamily
  FlatScalarIdealSheafDescent

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- The actual nonempty finite subsets of the ORIGINAL native geometric divisor components. -/
abbrev IntersectionIndex {Y : Scheme.{u}} (D : Y.IdealSheafData) :=
  {J : Finset (DivisorComponent D) // J.Nonempty}

/-- The actual original singleton component, retained without a chosen enumeration. -/
def singletonIndex {Y : Scheme.{u}} {D : Y.IdealSheafData} (C : DivisorComponent D) :
    IntersectionIndex D := ⟨{C}, Finset.singleton_nonempty C⟩

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] [PerfectField L]
  {Y : Scheme.{u}} (p : Y ⟶ Spec (.of L))
  [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]

omit [PerfectField L] [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p] in
private theorem scalar_cover {i : Index k L}
    (m : Model (diagram k L) (scalarCone k L) p i) :
    Surjective m.g ∧ Flat m.g ∧ IsAffineHom m.g := by
  let c : Spec (.of L) ⟶ Spec (.of (levelField k L i)) :=
    Spec.map (CommRingCat.ofHom (levelField k L i).val.toRingHom)
  let : Surjective c := ⟨fun y => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ y⟩⟩
  let : Flat c := inferInstance
  let : IsAffineHom c := inferInstance
  have H : IsPullback m.g p m.fY c := by simpa only [scalarCone_π] using m.isPullback
  exact ⟨MorphismProperty.of_isPullback H.flip inferInstance,
    MorphismProperty.of_isPullback H.flip inferInstance,
    MorphismProperty.of_isPullback H.flip inferInstance⟩

/-- ORIGINAL actual SNC geometry INTERNALLY produces genuine finite-field component ideals,
ALL actual regular intersections and their ENTIRE original defining ideal/scalar identities. -/
theorem exists_snc_intersection_ideals (D : Y.IdealSheafData) (hD : IsStrictNormalCrossings D)
    {i : Index k L} (m : Model (diagram k L) (scalarCone k L) p i) (hm : m.IsFP) :
    ∃ (j : Index k L) (h : j ⟶ i)
      (I : IntersectionIndex D → (m.baseChange h).Y.IdealSheafData),
      (∀ J, (I J).comap (m.baseChange h).g = componentIntersection D J.val ∧
        IsRegularScheme (I J).subscheme ∧
        I J = ⨆ C ∈ J.val, I (singletonIndex C)) ∧
      ∀ C : DivisorComponent D, IsIntegral (I (singletonIndex C)).subscheme := by
  classical
  obtain ⟨j, h, n, b, H⟩ := exists_snc_intersection_family k L p D hD m hm
  let M := m.baseChange h
  let I (J : IntersectionIndex D) := (b J).ker
  let : ∀ J, IsClosedImmersion (b J) := fun J => (H J).2.2.2.1
  have hI (J : IntersectionIndex D) : (I J).comap M.g = componentIntersection D J.val := by
    have hh := ker_comap_of_isPullback (H J).2.2.2.2.2.2
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using hh
  have hreg (J : IntersectionIndex D) : IsRegularScheme (I J).subscheme :=
    (H J).2.2.1.of_isOpenImmersion (inv (b J).toImage)
  obtain ⟨hSurj, hFlat, hAffine⟩ := scalar_cover k L p M
  let := hSurj
  let := hFlat
  let := hAffine
  refine ⟨j, h, I, ?_, ?_⟩
  · intro J
    refine ⟨hI J, hreg J, ?_⟩
    apply comap_injective M.g
    change (I J).comap M.g = (⨆ C ∈ J.val, I (singletonIndex C)).comap M.g
    rw [hI J]
    simp only [(Scheme.IdealSheafData.map_gc M.g).l_iSup, hI]
    simp [componentIntersection, singletonIndex]
  · intro C
    let V := Scheme.IdealSheafData.vanishingIdeal C.val
    let : IsReduced V.subscheme := ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme C.val
    let : IrreducibleSpace V.subscheme :=
      Subtype.irreducibleSpace (SNCLocality.divisorComponent_isIrreducible D C)
    let : IsIntegral V.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
    have hsingle : componentIntersection D (singletonIndex C).val = V := by
      simp [componentIntersection, singletonIndex, V]
    let : IsIntegral (componentIntersection D (singletonIndex C).val).subscheme := by
      rw [hsingle]
      infer_instance
    have Hscalar := (n (singletonIndex C)).isPullback
    rw [scalarCone_π] at Hscalar
    let : IsIntegral (n (singletonIndex C)).Y :=
      AlgebraicFieldFiniteIntegralModel.isIntegral_of_scalar_pullback
        (levelField k L j).val.toRingHom (n (singletonIndex C)).fY Hscalar
    let : Nonempty (I (singletonIndex C)).subscheme :=
      Nonempty.map (b (singletonIndex C)).toImage inferInstance
    exact isIntegral_of_isOpenImmersion (inv (b (singletonIndex C)).toImage)

end DeJongAlterations.Geometry.AlgebraicFieldFiniteBoundaryIdeals
