import DeJongAlterations.Geometry.CartierLocality
import DeJongAlterations.Geometry.ReducedClosedSubscheme
import Mathlib.Order.CompleteLattice.Finset

/-!
# Strict normal crossings under actual scheme isomorphisms

The component sets, scheme-theoretic intersections, and stalk codimensions
are transported through the native pullback of ideal sheaves.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open Scheme.IdealSheafData
open DeJongAlterations.Geometry.ReducedClosedSubscheme

namespace DeJongAlterations.Geometry.SNCIso

universe u

variable {X Y : Scheme.{u}}

/-- The actual pullback closed subscheme is isomorphic to the original one. -/
def subschemeIso (e : X ≅ Y) (D : Y.IdealSheafData) :
    (D.comap e.hom).subscheme ≅ D.subscheme :=
  D.comapIso e.hom ≪≫ asIso (pullback.snd e.hom D.subschemeι)

theorem isReduced_comap (e : X ≅ Y) (D : Y.IdealSheafData) [IsReduced D.subscheme] :
    IsReduced (D.comap e.hom).subscheme :=
  isReduced_of_isOpenImmersion (subschemeIso e D).hom

theorem isRegularScheme_comap (e : X ≅ Y) (D : Y.IdealSheafData)
    (hD : IsRegularScheme D.subscheme) : IsRegularScheme (D.comap e.hom).subscheme :=
  hD.of_isOpenImmersion (subschemeIso e D).hom

/-- The two genuine ideal-sheaf pullbacks give an order isomorphism. -/
def idealSheafComapOrderIso (e : X ≅ Y) : Y.IdealSheafData ≃o X.IdealSheafData where
  toFun D := D.comap e.hom
  invFun D := D.comap e.inv
  left_inv D := by
    change (D.comap e.hom).comap e.inv = D
    rw [← comap_comp, e.inv_hom_id, comap_id]
  right_inv D := by
    change (D.comap e.inv).comap e.hom = D
    rw [← comap_comp, e.hom_inv_id, comap_id]
  map_rel_iff' := by
    intro I J
    change I.comap e.hom ≤ J.comap e.hom ↔ I ≤ J
    constructor
    · intro h
      have h' := comap_mono e.inv h
      simpa only [← comap_comp, e.inv_hom_id, comap_id] using h'
    · intro h
      exact comap_mono e.hom h

theorem comap_iSup {ι : Sort*} (e : X ≅ Y) (D : ι → Y.IdealSheafData) :
    (⨆ i, D i).comap e.hom = ⨆ i, (D i).comap e.hom :=
  (idealSheafComapOrderIso e).map_iSup D

theorem comap_vanishingIdeal (e : X ≅ Y) (T : Closeds Y) :
    (vanishingIdeal T).comap e.hom = vanishingIdeal (T.preimage e.hom.continuous) := by
  let : IsReduced (vanishingIdeal T).subscheme := isReduced_vanishingIdeal_subscheme T
  let : IsReduced ((vanishingIdeal T).comap e.hom).subscheme :=
    isReduced_comap e _
  let : IsReduced (vanishingIdeal (T.preimage e.hom.continuous)).subscheme :=
    isReduced_vanishingIdeal_subscheme _
  apply idealSheaf_eq_of_isReduced_of_support_eq
  simp only [support_comap, support_vanishingIdeal]

theorem isEffectiveCartierDivisor_comap (e : X ≅ Y) (D : Y.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) : IsEffectiveCartierDivisor (D.comap e.hom) := by
  have h : IsEffectiveCartierDivisor ((D.comap e.hom).comap e.inv) := by
    simpa only [← comap_comp, e.inv_hom_id, comap_id] using hD
  intro x
  have hlocal := CartierLocality.exists_affine_neighborhood_of_isOpenImmersion
    e.inv (D.comap e.hom) h (e.hom x)
  have hx : e.inv (e.hom x) = x := (Scheme.homeoOfIso e).symm_apply_apply x
  simpa only [hx] using hlocal

section Topology

variable {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]

theorem homeomorph_image_component (h : P ≃ₜ Q) {S : Set P}
    (hS : S ∈ irreducibleComponents P) : h '' S ∈ irreducibleComponents Q := by
  rw [h.image_eq_preimage_symm]
  apply preimage_mem_irreducibleComponents hS h.symm.isOpenEmbedding
  simpa only [h.symm.surjective.range_eq, Set.inter_univ] using hS.1.nonempty

theorem homeomorph_image_genericPoint (h : P ≃ₜ Q) {S : Set P} {x : P}
    (hx : IsGenericPoint x S) : IsGenericPoint (h x) (h '' S) := by
  change closure {h x} = h '' S
  have heq : closure {x} = S := hx
  simpa only [h.image_closure, Set.image_singleton] using congrArg (Set.image h) heq

theorem subtypeHomeomorph_image (h : P ≃ₜ Q) {S : Set P} {T : Set Q}
    (hST : S = h ⁻¹' T) (C : Set S) :
    Subtype.val '' (h.sets hST '' C) = h '' (Subtype.val '' C) := by
  rw [Set.image_image, Set.image_image]
  rfl

end Topology

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A support homeomorphism transports the actual ambient closed component. -/
def componentMap {D : X.IdealSheafData} {E : Y.IdealSheafData} (h : X ≃ₜ Y)
    (hDE : (D.support : Set X) = h ⁻¹' (E.support : Set Y))
    (C : DivisorComponent D) : DivisorComponent E := by
  refine ⟨⟨h '' (C.val : Set X), h.isClosedMap _ C.val.isClosed⟩, ?_⟩
  obtain ⟨S, hS, hC⟩ := C.property
  refine ⟨h.sets hDE '' S, homeomorph_image_component _ hS, ?_⟩
  exact (subtypeHomeomorph_image h hDE S).trans (congrArg (Set.image h) hC)

theorem componentMap_coe {D : X.IdealSheafData} {E : Y.IdealSheafData} (h : X ≃ₜ Y)
    (hDE : (D.support : Set X) = h ⁻¹' (E.support : Set Y))
    (C : DivisorComponent D) :
    ((componentMap h hDE C).val : Set Y) = h '' (C.val : Set X) := rfl

/-- The isomorphism transports all actual irreducible components bijectively. -/
def divisorComponentEquiv (e : X ≅ Y) (D : Y.IdealSheafData) :
    DivisorComponent (D.comap e.hom) ≃ DivisorComponent D := by
  let h := Scheme.homeoOfIso e
  have hDE : ((D.comap e.hom).support : Set X) = h ⁻¹' (D.support : Set Y) := by
    rw [support_comap]
    rfl
  have hED : (D.support : Set Y) = h.symm ⁻¹' ((D.comap e.hom).support : Set X) := by
    rw [hDE]
    ext y
    simp only [Set.mem_preimage, h.apply_symm_apply]
  refine ⟨componentMap h hDE, componentMap h.symm hED, ?_, ?_⟩
  · intro C
    apply Subtype.ext
    apply Closeds.ext
    simp only [componentMap_coe, Set.image_image, h.symm_apply_apply]
    change id '' (C.val : Set X) = (C.val : Set X)
    exact Set.image_id _
  · intro C
    apply Subtype.ext
    apply Closeds.ext
    simp only [componentMap_coe, Set.image_image, h.apply_symm_apply]
    change id '' (C.val : Set Y) = (C.val : Set Y)
    exact Set.image_id _

theorem divisorComponentEquiv_coe (e : X ≅ Y) (D : Y.IdealSheafData)
    (C : DivisorComponent (D.comap e.hom)) :
    (((divisorComponentEquiv e D) C).val : Set Y) = e.hom '' (C.val : Set X) := rfl

theorem divisorComponentEquiv_preimage (e : X ≅ Y) (D : Y.IdealSheafData)
    (C : DivisorComponent (D.comap e.hom)) :
    (((divisorComponentEquiv e D) C).val).preimage e.hom.continuous = C.val := by
  apply Closeds.ext
  rw [Closeds.coe_preimage, divisorComponentEquiv_coe]
  exact Set.preimage_image_eq _ (Scheme.homeoOfIso e).injective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact scheme-theoretic intersections commute with the actual pullback. -/
theorem componentIntersection_comap (e : X ≅ Y) (D : Y.IdealSheafData)
    (J : Finset (DivisorComponent (D.comap e.hom))) :
    (componentIntersection D (J.map (divisorComponentEquiv e D).toEmbedding)).comap e.hom =
      componentIntersection (D.comap e.hom) J := by
  classical
  simp only [Finset.map_eq_image, componentIntersection, Finset.iSup_finset_image, comap_iSup]
  apply iSup_congr
  intro C
  apply iSup_congr
  intro _
  rw [comap_vanishingIdeal]
  exact congrArg vanishingIdeal (divisorComponentEquiv_preimage e D C)

/-- The expected codimension is preserved by actual stalk ring isomorphisms. -/
theorem hasPureCodimension_preimage (e : X ≅ Y) (T : Closeds Y) {r : ℕ}
    (hT : HasPureCodimension T r) : HasPureCodimension (T.preimage e.hom.continuous) r := by
  intro C hC x hx
  let h := Scheme.homeoOfIso e
  have hEq : (T.preimage e.hom.continuous : Set X) = h ⁻¹' (T : Set Y) := rfl
  let hT' := h.sets hEq
  have hC' : hT' '' C ∈ irreducibleComponents T := homeomorph_image_component hT' hC
  have hx' : IsGenericPoint (e.hom x) (Subtype.val '' (hT' '' C)) := by
    rw [subtypeHomeomorph_image h hEq C]
    exact homeomorph_image_genericPoint h hx
  have hdim := hT _ hC' (e.hom x) hx'
  exact (ringKrullDim_eq_of_ringEquiv
    (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv).symm.trans hdim

/-- Native strict normal crossings pull back along any actual scheme isomorphism. -/
theorem isStrictNormalCrossings_comap (e : X ≅ Y) (D : Y.IdealSheafData)
    (hD : IsStrictNormalCrossings D) : IsStrictNormalCrossings (D.comap e.hom) := by
  let : IsReduced D.subscheme := hD.reduced
  refine ⟨isEffectiveCartierDivisor_comap e D hD.cartier, isReduced_comap e D,
    ?_, ?_, ?_⟩
  · intro x hx
    have hmem : e.hom x ∈ D.support := by
      rw [support_comap] at hx
      exact hx
    let : IsRegularLocalRing (Y.presheaf.stalk (e.hom x)) := hD.regularAlong _ hmem
    exact IsRegularLocalRing.of_ringEquiv
      (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
  · intro J hJ
    let J' := J.map (divisorComponentEquiv e D).toEmbedding
    have hJ' : J'.Nonempty := Finset.map_nonempty.mpr hJ
    have hregular := isRegularScheme_comap e (componentIntersection D J')
      (hD.intersectionsRegular J' hJ')
    simpa only [J', componentIntersection_comap] using hregular
  · intro J hJ
    let J' := J.map (divisorComponentEquiv e D).toEmbedding
    have hJ' : J'.Nonempty := Finset.map_nonempty.mpr hJ
    have hcodim := hasPureCodimension_preimage e (componentIntersection D J').support
      (hD.intersectionsCodimension J' hJ')
    rw [← support_comap, show J'.card = J.card from Finset.card_map _] at hcodim
    simpa only [J', componentIntersection_comap] using hcodim

/-- All native SNC conditions are invariant under scheme isomorphism. -/
theorem isStrictNormalCrossings_comap_iff (e : X ≅ Y) (D : Y.IdealSheafData) :
    IsStrictNormalCrossings (D.comap e.hom) ↔ IsStrictNormalCrossings D := by
  constructor
  · intro hD
    have h := isStrictNormalCrossings_comap e.symm (D.comap e.hom) hD
    simpa only [Iso.symm_hom, ← comap_comp, e.inv_hom_id, comap_id] using h
  · exact isStrictNormalCrossings_comap e D

end DeJongAlterations.Geometry.SNCIso
