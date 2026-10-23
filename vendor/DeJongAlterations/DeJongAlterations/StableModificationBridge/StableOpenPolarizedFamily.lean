import DeJongAlterations.StableModificationBridge.StableOpenNearbyNormalizedDegree
import DeJongAlterations.StableModificationBridge.StableOpenPositiveDegreeNumerical
import DeJongAlterations.StableModificationBridge.StableOpenFibreNeighbourhood
import DeJongAlterations.StableModificationBridge.GeneratedSectionHyperplane
import DeJongAlterations.Geometry.CurveFibrationMarkedOpenSmooth

/-! Concrete original affine polarizations of ONE marked L give the actual stable base open. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenPolarizedFamily

open StableModification Projectivity Cohomology CurvesField
open Omega.ComponentDegree GeneratedSectionHyperplane

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- This consumer takes ACTUAL original maps and whole positive-power module isomorphisms;
all nearby normalized positivity, original numerical stability and the base open are produced. -/
theorem exists_open_of_original_affine_polarizations {K : Type u} [Field K] [IsAlgClosed K]
    {V : Scheme.{u}} (pV : V ⟶ Spec (.of K)) [IsVariety pV] (hV : IsNormalScheme V)
    {C : Scheme.{u}} (q : C ⟶ V) (hq : DeJong.IsRelativelyProjective pV q)
    {X : Scheme.{u}} (β : X ⟶ C) (hβ : DeJong.IsRelativelyProjective (q ≫ pV) β)
    [DeJong.IsNodalCurve (β ≫ q)]
    (D' : X.IdealSheafData) (hss : DeJong.IsSemistablePair (β ≫ q) D')
    (hsm : Smooth ((β ≫ q).fiberToSpecResidueField (genericPoint V)))
    (E : LocalEquations X)
    (hEi : ∀ i, ∃ h : IsAffineOpen (E.U i), D'.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i})
    (hEs : ∀ x : X, x ∈ E.canonicalSection.nonvanishingLocus ↔ x ∉ (D'.support : Set X))
    (L : LineBundleData X)
    (e : L.twist (unitModule X) 1 ≅ E.toLineBundleData.twist (Omega.dualizingSheaf (β ≫ q)) 1)
    (z : V) (hzc : IsClosed ({z} : Set V))
    (hpol : ∀ y : C, IsClosed ({y} : Set C) → q y = z →
      ∃ W : C.Opens, y ∈ W ∧ ∃ m : ℕ, 0 < m ∧ ∃ (n : ℕ)
        (h : (β ⁻¹ᵁ W).toScheme ⟶ projectiveSpace K n), IsAffineHom h ∧
        Nonempty ((L.pullback (β ⁻¹ᵁ W).ι).twist (unitModule (β ⁻¹ᵁ W).toScheme) (m : ℤ) ≅
          ((nativeHyperplane K n).pullback h).twist (unitModule (β ⁻¹ᵁ W).toScheme) 1)) :
    ∃ O : V.Opens, z ∈ O ∧ ∀ z' ∈ O, Global.IsNumericallyStableAt β q D' z' := by
  classical
  let : IsProper q := hq.isProper
  let : IsProper β := hβ.isProper
  let : IsProper (β ≫ q) := inferInstance
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian pV
  let : CompactSpace V := Ample.compactSpace_of_quasiCompact pV
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
  let : V.IsSeparated := ⟨by rw [← terminal.comp_from pV]; infer_instance⟩
  let : Smooth ((β ≫ q).fiberToSpecResidueField (genericPoint V)) := hsm
  have hgen : ∀ x : X, (β ≫ q) x = genericPoint V → DeJong.IsSmoothAt (β ≫ q) x := by
    intro x hx
    exact (DeJong.isSmoothAt_iff_mem_smoothLocus (β ≫ q) x).mpr
      (Geometry.CurveFibrationMarkedOpen.genericFiber_le_smoothLocus (β ≫ q) x hx)
  let I := {y : C // IsClosed ({y} : Set C) ∧ q y = z}
  choose W hyW m hm n h hAff hIso using (fun i : I => hpol i.1 i.2.1 i.2.2)
  let T : C.Opens := ⨆ i : I, W i
  have hT (y : C) (hy : IsClosed ({y} : Set C)) (hya : q y = z) : y ∈ T :=
    Opens.mem_iSup.mpr ⟨⟨y, hy, hya⟩, hyW ⟨y, hy, hya⟩⟩
  obtain ⟨O, hzO, hOT⟩ := StableOpenFibreNeighbourhood.exists_base_open_of_closed_fibre_le
    q z hzc T hT
  refine ⟨O, hzO, ?_⟩
  intro z' hz' K' _ _ a ha
  let F := pullback (C := Scheme.{u}) (β ≫ q) a
  let : CompactSpace F := Ample.compactSpace_of_quasiCompact (pullback.snd (β ≫ q) a)
  let : IsAffineHom (pullback.diagonal (terminal.from F)) :=
    Ample.isAffineHom_diagonal_of_isSeparated (pullback.snd (β ≫ q) a)
  have hRP := Gluing.IsRelativelyProjective.comp hq hβ
  have hp := StableOpenPolarizationPullback.isProjectiveOver_geometric_fibre pV (β ≫ q) hRP a
  apply StableOpenPositiveDegreeNumerical.numericallyStableFibre_of_positive_lineBundle_degree
    β q hV hgen D' hss E hEi hEs L e a hp
  intro v hv hcon
  have hpoint : q (β (pullback.fst (β ≫ q) a v)) = z' := by
    have hs := congrArg (fun b : F ⟶ V => b v)
      (pullback.condition (f := β ≫ q) (g := a))
    change q (β (pullback.fst (β ≫ q) a v)) = a (pullback.snd (β ≫ q) a v) at hs
    exact hs.trans (ha _)
  have hin : β (pullback.fst (β ≫ q) a v) ∈ T :=
    hOT (by change q (β (pullback.fst (β ≫ q) a v)) ∈ O; rw [hpoint]; exact hz')
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hin
  let : IsAffineHom (h i) := hAff i
  obtain ⟨ei⟩ := hIso i
  exact StableOpenNearbyNormalizedDegree.degree_pos_of_original_affine_polarization
    β q a hp v hv hcon L (W i) hi (nativeCoordinates K (n i)) (h i) (m i) (hm i) ei

end DeJongAlterations.StableModificationBridge.StableOpenPolarizedFamily
