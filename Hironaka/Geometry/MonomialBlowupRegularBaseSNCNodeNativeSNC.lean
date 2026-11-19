import Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeFamily
import Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeCodimension

/-! Genuine full SNC for the original several-component boundary pullback to a node. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeNativeSNC

open Algebra.NodeBlowupChart Algebra.NodeNormalCoordinates
open MonomialBlowupRegularBaseSNCNodeAlgebra MonomialBlowupRegularBaseSNCParameters
open MonomialBlowupRegularBaseSNCNodeFamily MonomialBlowupRegularBaseSNCIntersection
open MonomialBlowupRegularBaseSNCIndependence MonomialBlowupRegularBaseSNCNodeIntersections
open MonomialBlowupRegularBaseSNCNodeCodimension
open SpecIdealSheaf ReducedClosedSubscheme Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A]

local instance componentDecidableEq (D : (Spec (CommRingCat.of A)).IdealSheafData) :
    DecidableEq (DivisorComponent D) := Classical.typeDecidableEq _

/-- The actual original base components selected by the coefficient indices. -/
def otherComponents (D : (Spec (CommRingCat.of A)).IdealSheafData)
    (F : Finset (DivisorComponent D)) (s : Finset (Fin 2 ⊕ F)) : Finset (DivisorComponent D) :=
  s.toRight.image Subtype.val

/-- Their equations remain the specified original equations, with only subtype membership transported. -/
def otherEquation (D : (Spec (CommRingCat.of A)).IdealSheafData)
    (F : Finset (DivisorComponent D)) (s : Finset (Fin 2 ⊕ F)) (a : F → A)
    (B : otherComponents D F s) : A :=
  a ⟨B.val, by obtain ⟨B', _, heq⟩ := Finset.mem_image.mp B.property; exact heq ▸ B'.property⟩

/-- The full original selected-factor ideal is literally the actual base-component intersection plus coordinates. -/
theorem factorIdeal_eq_mixed
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (F : Finset (DivisorComponent D))
    (t : A) (a : F → A)
    (ha : ∀ B, specIdealSheaf A (Ideal.span {a B}) = vanishingIdeal B.val.val)
    (s : Finset (Fin 2 ⊕ F)) :
    factorIdeal t a s = mixedIdeal (intersectionIdeal D (otherComponents D F s)) t s.toLeft := by
  classical
  have himage : Finset.univ.image (fun B : s.toRight ↦ B.val.val) = otherComponents D F s := by
    ext B
    simp [otherComponents]
  have hrange : Set.range (fun B : s.toRight ↦ a B.val) = a '' (s.toRight : Set F) := by
    ext x
    simp
  have hI := intersectionIdeal_eq_span D (fun B : s.toRight ↦ B.val.val)
    (fun B ↦ a B.val) (fun B ↦ ha B.val)
  rw [himage, hrange] at hI
  rw [factorIdeal, mixedIdeal, hI, Ideal.map_span, nodeIdeal, ← Ideal.span_union]
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    cases i with
    | inl i =>
      exact Or.inr ⟨i, by simpa using hi, rfl⟩
    | inr B =>
      exact Or.inl ⟨a B, ⟨B, by simpa using hi, rfl⟩, rfl⟩
  · rintro (⟨b, ⟨B, hB, rfl⟩, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨.inr B, by simpa using hB, rfl⟩
    · exact ⟨.inl i, by simpa using hi, rfl⟩

/-- Distinct original component indices preserve the actual number of selected coefficient components. -/
theorem otherComponents_card
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (F : Finset (DivisorComponent D))
    (s : Finset (Fin 2 ⊕ F)) : (otherComponents D F s).card = s.toRight.card :=
  Finset.card_image_of_injective _ Subtype.val_injective

/-- The original singled-out node component is absent from every selected remaining-component family. -/
theorem not_mem_otherComponents
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (F : Finset (DivisorComponent D))
    (C : DivisorComponent D) (hC : C ∉ F) (s : Finset (Fin 2 ⊕ F)) :
    C ∉ otherComponents D F s := by
  rintro h
  obtain ⟨B, _, hB⟩ := Finset.mem_image.mp h
  exact hC (hB ▸ B.property)

/-- The specified original equations remain exactly the equations of the actual selected base components. -/
theorem otherEquation_equation
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (F : Finset (DivisorComponent D))
    (s : Finset (Fin 2 ⊕ F)) (a : F → A)
    (ha : ∀ B, specIdealSheaf A (Ideal.span {a B}) = vanishingIdeal B.val.val)
    (B : otherComponents D F s) :
    specIdealSheaf A (Ideal.span {otherEquation D F s a B}) = vanishingIdeal B.val.val :=
  ha _

/-- The empty actual component-intersection ideal is the zero ideal. -/
theorem intersectionIdeal_empty (D : (Spec (CommRingCat.of A)).IdealSheafData) :
    intersectionIdeal D ∅ = ⊥ := by simp [intersectionIdeal, componentIntersection]

variable [IsRegularRing A] [IsDomain A]

section ActualBoundary

variable (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
variable (F : Finset (DivisorComponent D)) (C : DivisorComponent D) (hC : C ∉ F)
variable (t : A) (ht : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
variable (a : F → A) (ha : ∀ B, specIdealSheaf A (Ideal.span {a B}) = vanishingIdeal B.val.val)

include hD hC ht ha

omit [IsDomain A] in
/-- All nonempty original factor-intersection quotients are actual regular rings. -/
theorem factorIdeal_quotient_isRegularRing (s : Finset (Fin 2 ⊕ F)) (hs : s.Nonempty) :
    IsRegularRing (Node A t ⧸ factorIdeal t a s) := by
  rw [factorIdeal_eq_mixed D F t a ha s]
  by_cases hJ : (otherComponents D F s).Nonempty
  · exact mixed_quotient_isRegularRing D hD _ hJ C (not_mem_otherComponents D F C hC s) t ht s.toLeft
  · have hJE : otherComponents D F s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    have hright : s.toRight = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [← otherComponents_card D F s, hJE]
      rfl
    have hleft : s.toLeft.Nonempty := by
      obtain ⟨i, hi⟩ := hs
      cases i with
      | inl i => exact ⟨i, by simpa using hi⟩
      | inr i => have h : i ∈ s.toRight := by simpa using hi
                 simp [hright] at h
    rw [hJE, intersectionIdeal_empty, mixedIdeal, Ideal.map_bot, bot_sup_eq]
    let : IsRegularRing (ParameterQuotient t) := (component_equation_data D hD C t ht).2.2
    exact nodeIdeal_quotient_isRegularRing t s.toLeft hleft

omit [IsDomain A] in
/-- The original factor-intersection support has the precise actual native stalk codimension. -/
theorem factorIdeal_support_hasPureCodimension (s : Finset (Fin 2 ⊕ F)) :
    HasPureCodimension (specIdealSheaf (Node A t) (factorIdeal t a s)).support s.card := by
  rw [factorIdeal_eq_mixed D F t a ha s]
  have h := mixed_support_hasPureCodimension D hD (otherComponents D F s)
    (otherEquation D F s a) (otherEquation_equation D F s a ha)
    C (not_mem_otherComponents D F C hC s) t ht s.toLeft
  convert h using 1
  rw [otherComponents_card, Nat.add_comm, Finset.card_toLeft_add_card_toRight]

/-- The literal nonzero boundary product gives the actual Cartier equation on the genuine affine top open. -/
theorem boundary_isEffectiveCartier : IsEffectiveCartierDivisor (boundary t a) := by
  let : IsDomain (Node A t) := Algebra.NodeDomain.nodeQuotient_isDomain t
    (component_equation_ne_zero D hD C t ht)
  intro x
  let e : Node A t ≃+* Γ(Spec (CommRingCat.of (Node A t)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Node A t))).symm.commRingCatIsoToRingEquiv
  have hp : (∏ i, factor t a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ (factor_prime D hD F C hC t ht a ha i).ne_zero)
  have hr : IsRegular (e (∏ i, factor t a i)) := by
    constructor
    · intro b c hbc
      apply e.symm.injective
      apply mul_left_cancel₀ hp
      simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm hbc
    · intro b c hbc
      apply e.symm.injective
      apply mul_right_cancel₀ hp
      simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm hbc
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, e (∏ i, factor t a i), hr, ?_⟩
  rw [boundary, specIdealSheaf_ideal_top, Ideal.map_span, Set.image_singleton]
  rfl

/-- The genuine native intersection of actual components is its full original factor-ideal sum. -/
theorem componentIntersection_boundary
    (J : Finset (DivisorComponent (boundary t a))) :
    componentIntersection (boundary t a) J = specIdealSheaf (Node A t)
      (factorIdeal t a (J.image (componentIndex D hD F C hC t ht a ha))) := by
  classical
  let idx := componentIndex D hD F C hC t ht a ha
  have hfactor : (⨆ B ∈ J, factorIdeal t a {idx B}) = factorIdeal t a (J.image idx) := by
    apply le_antisymm
    · refine iSup_le fun B ↦ iSup_le fun hB ↦ ?_
      apply Ideal.span_mono
      apply Set.image_mono
      intro i hi
      have hi' : i = idx B := by simpa using hi
      rw [hi']
      exact Finset.mem_image_of_mem idx hB
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hi
      have hinc : factorIdeal t a {idx B} ≤ ⨆ B ∈ J, factorIdeal t a {idx B} :=
        le_iSup_of_le B (le_iSup_of_le hB le_rfl)
      exact hinc (Ideal.subset_span (Set.mem_image_of_mem _ (Finset.mem_singleton_self _)))
  calc
    componentIntersection (boundary t a) J =
        ⨆ B ∈ J, specIdealSheaf (Node A t) (factorIdeal t a {idx B}) := by
      simp only [componentIntersection, componentIndex_closed D hD F C hC t ht a ha,
        vanishingIdeal_factorClosed_singleton D hD F C hC t ht a ha]
      rfl
    _ = specIdealSheaf (Node A t) (⨆ B ∈ J, factorIdeal t a {idx B}) :=
      ((specIdealSheafEquiv (Node A t)).symm.map_iSup₂ _).symm
    _ = _ := congrArg _ hfactor

/-- The actual several-component product boundary on the original node is strict normal crossings. -/
theorem boundary_isStrictNormalCrossings : IsStrictNormalCrossings (boundary t a) := by
  refine ⟨boundary_isEffectiveCartier D hD F C hC t ht a ha,
    boundary_isReduced D hD F C hC t ht a ha, ?_, ?_, ?_⟩
  · intro x _
    exact RegularNode.isRegularScheme_nodeQuotient t (component_equation_parameter D hD C t ht) x
  · intro J hJ
    rw [componentIntersection_boundary D hD F C hC t ht a ha]
    let : IsRegularRing (Node A t ⧸ factorIdeal t a (J.image (componentIndex D hD F C hC t ht a ha))) :=
      factorIdeal_quotient_isRegularRing D hD F C hC t ht a ha _
        (hJ.image (componentIndex D hD F C hC t ht a ha))
    exact CoordinateSNC.isRegularScheme_specIdealSheaf_subscheme _ _
  · intro J _
    rw [componentIntersection_boundary D hD F C hC t ht a ha]
    have hc : (J.image (componentIndex D hD F C hC t ht a ha)).card = J.card :=
      Finset.card_image_of_injective _ (componentIndex_injective D hD F C hC t ht a ha)
    rw [← hc]
    exact factorIdeal_support_hasPureCodimension D hD F C hC t ht a ha _

/-- The literal original coefficient ideal pullback is SNC, with no chart or boundary output certificate. -/
theorem original_comap_isStrictNormalCrossings : IsStrictNormalCrossings
    ((specIdealSheaf A (Ideal.span {t * ∏ B, a B})).comap
      (Spec.map (CommRingCat.ofHom (algebraMap A (Node A t))))) := by
  rw [← boundary_eq_original_comap]
  exact boundary_isStrictNormalCrossings D hD F C hC t ht a ha

end ActualBoundary

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeNativeSNC
