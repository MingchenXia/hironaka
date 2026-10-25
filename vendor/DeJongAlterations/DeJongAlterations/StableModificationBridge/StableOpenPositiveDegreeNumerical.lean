import DeJongAlterations.StableModificationBridge.StableOpenRationalSpecialCount
import DeJongAlterations.StableModificationBridge.StableMarkedComponentDegree

/-! Genuine native positive marked Euler degree implies ORIGINAL numerical stability. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenPositiveDegreeNumerical

open StableModification Projectivity Cohomology CurvesField CurvesField.Genus
open Omega.ComponentNormalization Omega.ComponentDegree BlowDown.ClosureComponent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every original marking exactness/cokernel input is internally produced from the ORIGINAL
semi-stable pair; the sole positivity premise is native Euler degree of the SAME actual L. -/
theorem numericallyStableFibre_of_positive_lineBundle_degree {X C S : Scheme.{u}}
    (β : X ⟶ C) (g : C ⟶ S) [DeJong.IsNodalCurve (β ≫ g)] [IsProper (β ≫ g)]
    [IsIntegral S] [IsLocallyNoetherian S]
    (hS : IsNormalScheme S)
    (hgen : ∀ x : X, (β ≫ g) x = genericPoint S → DeJong.IsSmoothAt (β ≫ g) x)
    (D' : X.IdealSheafData) (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (E : LocalEquations X)
    (hEi : ∀ i, ∃ h : IsAffineOpen (E.U i), D'.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i})
    (hEs : ∀ x : X, x ∈ E.canonicalSection.nonvanishingLocus ↔ x ∉ (D'.support : Set X))
    (L : LineBundleData X)
    (e : L.twist (unitModule X) 1 ≅ E.toLineBundleData.twist (Omega.dualizingSheaf (β ≫ g)) 1)
    {K : Type u} [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
    [CompactSpace (pullback (C := Scheme.{u}) (β ≫ g) a)]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) (β ≫ g) a)))]
    (hp : IsProjectiveOver (pullback.snd (β ≫ g) a))
    (hpos : ∀ v ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) a),
      (Curves.pullbackCompMap β g a '' closure {v}).Subsingleton →
        0 < DualityScheme.eulerCharOf ((L.pullback (componentMap (β ≫ g) a v)).twist
          (unitModule (componentNormalization (β ≫ g) a v)) 1)
          (structureCoeff (componentStructure (β ≫ g) a v)) -
        eulerChar (componentNormalization (β ≫ g) a v)
          (structureCoeff (componentStructure (β ≫ g) a v))) :
    Global.NumericallyStableFibre β g D' a := by
  intro Z hZ hcon _ _ hpa
  obtain ⟨v, hv⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have heq : closure {v} = Z := hv
  subst Z
  have hvG : v ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) a) := hZ
  have hpT : IsProjectiveOver (closureι v ≫ pullback.snd (β ≫ g) a) :=
    DeJong.IsProjectiveOver.comp_isClosedImmersion hp _
  have hN : IsProjectiveOver (componentStructure (β ≫ g) a v) :=
    isProjectiveOver_normalizationPoints v (pullback.snd (β ≫ g) a) hp
  have hg := (StableOpenRationalNormalization.genus_and_delta_eq_zero
    (pullback.snd (β ≫ g) a) (topologicalKrullDim_fibre_le_one (β ≫ g) a) v hpT
    (exists_mem_closure_ne (β ≫ g) a hvG) hpa).1
  obtain ⟨P, M, hP, hM, hdeg⟩ := StableMarkedComponentDegree.exists_lineBundle_component_degree
    (β ≫ g) D' a v hvG hN hS hgen hpair E hEi hEs L e
  have hpositive := hpos v hvG hcon
  rw [hdeg, hg] at hpositive
  have h3 : 3 ≤ P.card + M.card := by omega
  rw [StableOpenRationalSpecialCount.specialPoints_encard_eq β g D' hpair a v hvG hpT hpa
    P M hP hM]
  exact_mod_cast h3

/-- ONE internally chosen original marked line bundle, before every field/fibre/component,
supplies the genuine native positive-degree criterion. -/
theorem exists_markedLineBundle_numerical_criterion {X C S : Scheme.{u}}
    (β : X ⟶ C) (g : C ⟶ S) [DeJong.IsNodalCurve (β ≫ g)] [IsProper (β ≫ g)]
    [IsIntegral S] [IsLocallyNoetherian S]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hS : IsNormalScheme S)
    (hgen : ∀ x : X, (β ≫ g) x = genericPoint S → DeJong.IsSmoothAt (β ≫ g) x)
    (D' : X.IdealSheafData) (hpair : DeJong.IsSemistablePair (β ≫ g) D') :
    ∃ E : LocalEquations X,
      (∀ i, ∃ h : IsAffineOpen (E.U i), IsRegular (E.f i) ∧
        D'.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i}) ∧
      (∀ x : X, x ∈ E.canonicalSection.nonvanishingLocus ↔ x ∉ (D'.support : Set X)) ∧
      ∃ L : LineBundleData X,
        Nonempty (L.twist (unitModule X) 1 ≅ E.toLineBundleData.twist (Omega.dualizingSheaf (β ≫ g)) 1) ∧
        ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
          [CompactSpace (pullback (C := Scheme.{u}) (β ≫ g) a)]
          [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) (β ≫ g) a)))],
          IsProjectiveOver (pullback.snd (β ≫ g) a) →
          (∀ v ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) a),
            (Curves.pullbackCompMap β g a '' closure {v}).Subsingleton →
              0 < DualityScheme.eulerCharOf ((L.pullback (componentMap (β ≫ g) a v)).twist
                (unitModule (componentNormalization (β ≫ g) a v)) 1)
                (structureCoeff (componentStructure (β ≫ g) a v)) -
              eulerChar (componentNormalization (β ≫ g) a v)
                (structureCoeff (componentStructure (β ≫ g) a v))) →
          Global.NumericallyStableFibre β g D' a := by
  obtain ⟨E, hEi, hEs, L, ⟨e⟩⟩ := StableMarkedDualizingBundle.exists_markedDualizingBundle
    (β ≫ g) hS hgen D' hpair
  refine ⟨E, hEi, hEs, L, ⟨e⟩, ?_⟩
  intro K _ _ a _ _ hp hpos
  apply numericallyStableFibre_of_positive_lineBundle_degree β g hS hgen D' hpair E ?_ hEs L e a hp hpos
  intro i
  obtain ⟨ha, _, hi⟩ := hEi i
  exact ⟨ha, hi⟩

end DeJongAlterations.StableModificationBridge.StableOpenPositiveDegreeNumerical
