import DeJongAlterations.Geometry.CurveBoundaryBasic

/-!
# The actual reduced proper boundary on a normal curve is strict normal crossings

Actual irreducible support components are single closed points. Intersections
retain their original sum-of-ideals structure; two distinct components have
unit sum and therefore empty actual intersection scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData

namespace DeJongAlterations.Geometry.CurveBoundary

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in
/-- Each actual boundary component lies in the original support. -/
theorem component_subset (D : X.IdealSheafData) (C : DivisorComponent D) :
    (C.val : Set X) ⊆ D.support := by
  obtain ⟨S, _, hS⟩ := C.property
  rw [← hS]
  rintro x ⟨y, _, rfl⟩
  exact y.property

/-- Every actual irreducible component of a proper curve support is a single
nongeneric, hence closed, point. -/
theorem component_singleton (hdim : topologicalKrullDim X ≤ 1)
    (D : X.IdealSheafData) (hD : D.support ≠ ⊤) (C : DivisorComponent D) :
    ∃ x : X, (C.val : Set X) = {x} ∧ x ≠ genericPoint X := by
  obtain ⟨S, hS, hC⟩ := C.property
  have hi : IsIrreducible (C.val : Set X) := by
    rw [← hC]
    exact hS.1.image Subtype.val continuous_subtype_val.continuousOn
  let x := hi.genericPoint
  have hg : IsGenericPoint x (C.val : Set X) := hi.isGenericPoint_genericPoint C.val.isClosed
  have hx : x ≠ genericPoint X := by
    intro h
    exact genericPoint_not_mem D.support hD (h ▸ component_subset D C hg.mem)
  refine ⟨x, ?_, hx⟩
  rw [← hg.def, (isClosed_singleton_of_ne_genericPoint hdim x hx).closure_eq]

/-- Any proper closed support on an integral curve has pure codimension one. -/
theorem hasPureCodimension_one (hdim : topologicalKrullDim X ≤ 1)
    (Z : Closeds X) (hZ : Z ≠ ⊤) : HasPureCodimension Z 1 := by
  intro C hC x hx
  obtain ⟨y, _, hy⟩ := hx.mem
  apply ringKrullDim_stalk_eq_one hdim x
  intro h
  apply genericPoint_not_mem Z hZ
  have hm : x ∈ Z := hy ▸ y.property
  exact h ▸ hm

omit [IsIntegral X] in
/-- A component itself has proper support whenever the original boundary does. -/
theorem component_ne_top (D : X.IdealSheafData) (hD : D.support ≠ ⊤)
    (C : DivisorComponent D) : C.val ≠ ⊤ := by
  intro h
  apply hD
  apply top_unique
  intro x hx
  apply component_subset D C
  rw [h]
  trivial

/-- A nonsingleton family of distinct actual point components has empty support. -/
theorem componentIntersection_support_eq_bot (hdim : topologicalKrullDim X ≤ 1)
    (D : X.IdealSheafData) (hD : D.support ≠ ⊤)
    (J : Finset (DivisorComponent D)) (hJ : J.Nonempty) (hcard : J.card ≠ 1) :
    (componentIntersection D J).support = ⊥ := by
  classical
  rw [componentIntersection_support]
  apply Closeds.ext
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨C₀, hC₀⟩ := hJ
  have hall (C : DivisorComponent D) (hC : C ∈ J) : C = C₀ := by
    obtain ⟨y, hy, _⟩ := component_singleton hdim D hD C
    obtain ⟨z, hz, _⟩ := component_singleton hdim D hD C₀
    have hxy : x = y := by
      have hm : x ∈ C.val := (SetLike.le_def.mp (iInf_le_of_le C (iInf_le _ hC))) hx
      change x ∈ (C.val : Set X) at hm
      rw [hy] at hm
      exact hm
    have hxz : x = z := by
      have hm : x ∈ C₀.val := (SetLike.le_def.mp (iInf_le_of_le C₀ (iInf_le _ hC₀))) hx
      change x ∈ (C₀.val : Set X) at hm
      rw [hz] at hm
      exact hm
    apply Subtype.ext
    apply Closeds.ext
    rw [hy, hz, ← hxy, ← hxz]
  have heq : J = {C₀} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hC₀, hall⟩
  apply hcard
  rw [heq, Finset.card_singleton]

/-- Native strict normal crossings for the actual reduced induced boundary,
without supplied component, Cartier, codimension or intersection witnesses. -/
theorem isStrictNormalCrossings_vanishingIdeal [IsLocallyNoetherian X]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 1)
    (Z : Closeds X) (hZ : Z ≠ ⊤) :
    IsStrictNormalCrossings (vanishingIdeal Z) := by
  classical
  let D := vanishingIdeal Z
  have hD : D.support ≠ ⊤ := hZ
  have hreg := isRegularScheme_of_isNormalScheme_of_topologicalKrullDim_le_one X hnormal hdim
  refine ⟨isEffectiveCartier_of_support_ne_top hnormal hdim D hD,
    ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme Z,
    fun x _ => hreg x, ?_, ?_⟩
  · intro J hJ
    by_cases hc : J.card = 1
    · obtain ⟨C, rfl⟩ := Finset.card_eq_one.mp hc
      simpa only [componentIntersection, Finset.mem_singleton, iSup_iSup_eq_left] using
        isRegular_vanishingIdeal hdim C.val (component_ne_top D hD C)
    · have heq : componentIntersection D J = ⊤ :=
        (support_eq_bot_iff _).mp (componentIntersection_support_eq_bot hdim D hD J hJ hc)
      rw [heq]
      intro x
      exact isEmptyElim x
  · intro J hJ
    by_cases hc : J.card = 1
    · obtain ⟨C, rfl⟩ := Finset.card_eq_one.mp hc
      simp only [componentIntersection, Finset.mem_singleton, iSup_iSup_eq_left,
        Finset.card_singleton]
      change HasPureCodimension C.val 1
      exact hasPureCodimension_one hdim C.val (component_ne_top D hD C)
    · rw [componentIntersection_support_eq_bot hdim D hD J hJ hc]
      intro C hC
      obtain ⟨x, _⟩ := hC.1.nonempty
      exact (show False from x.property).elim

end DeJongAlterations.Geometry.CurveBoundary
