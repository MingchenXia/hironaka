import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Resolution.HironakaActualAnalyticSubspaceMaps
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction
import Hironaka.Resolution.HironakaReducedComplexAnalyticSpaces
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Blowup.BlowupRestrictOpen

/-!
# Manifold test maps lift into a singular analytic strict transform

The universal property of an actual ambient blowup constructs a unique
holomorphic lift. Invertibility of the pulled centre ideal makes its zero
locus thin, so continuity forces the SAME lift into the geometric strict
transform of the original analytic subspace, even at points over the centre.
It therefore induces an actual morphism of the reduced locally ringed
subspaces, with its full projection square.

This is the manifold-test part of the intrinsic blowup construction shared
by Hironaka G10 and G11. It does not construct analytic Projan or prove the
universal property for arbitrary singular complex-space test sources.
Blueprint: `hironaka-singular-subspace-blowup-lift.tex`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaSingularSubspaceBlowupLift

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupStrictSubmanifold BlowupExceptionalDivisor

noncomputable section

section Invertible

variable {m : ℕ} {T : Type u} [TopologicalSpace T]
  [ChartedSpace (ComplexModel m) T] [IsComplexManifold m T]

omit [IsComplexManifold m T] in
/-- An invertible ideal cannot vanish on a nonempty open set. -/
theorem interior_zeroLocus_eq_empty {I : GermIdeal m T} (hI : I.IsInvertible) :
    interior I.zeroLocus = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨U, hU, hxU, a, ha, hnon, hgen⟩ := hI x
  obtain ⟨y, hy, hay⟩ := hnon (interior I.zeroLocus ∩ U)
    (isOpen_interior.inter hU) inter_subset_right ⟨x, hx, hxU⟩
  have hhol : HolomorphicAt m a y :=
    eventually_of_mem (hU.mem_nhds hy.2) fun z hz =>
      (ha z hz).mdifferentiableAt (hU.mem_nhds hz)
  have hmem := (hgen y hy.2 a).mpr
    (InvertibleIdealQuotient.isInSpanAt_self rfl hhol)
  exact hay (interior_subset hy.1 a hmem)

end Invertible

section Lift

variable {n m : ℕ} {M Y T : Type u}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace T] [ChartedSpace (ComplexModel m) T] [IsComplexManifold m T]
  {C W : Set M} {π : Y → M} {h : T → M}

/-- Invertibility on a test manifold forces the original inverse image of the
centre to have empty interior, in the original test manifold. -/
theorem interior_preimage_centre_eq_empty (hπ : IsBlowupAlong n C π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h)
    (hinv : (GermIdeal.pullback (m := m) h (vanishingIdeal (n := n) C)).IsInvertible) :
    interior (h ⁻¹' C) = ∅ := by
  have heq := zeroLocus_pullback hh (isCoherent_vanishingIdeal_centre hπ)
  rw [zeroLocus_vanishingIdeal hπ.1.1] at heq
  rw [← heq]
  exact interior_zeroLocus_eq_empty hinv

/-- Every actual ambient lift lands in the geometric strict transform;
containment over the centre is derived by density, not supplied. -/
theorem mapsTo_geoStrictTransform_of_lift (hπ : IsBlowupAlong n C π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h)
    (hinv : (GermIdeal.pullback (m := m) h (vanishingIdeal (n := n) C)).IsInvertible)
    (hW : ∀ t, h t ∈ W) {k : T → Y}
    (hk : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ k)
    (hcomm : π ∘ k = h) : ∀ t, k t ∈ geoStrictTransform π C W := by
  have hthin := interior_preimage_centre_eq_empty hπ hh hinv
  have hdense : Dense ((h ⁻¹' C)ᶜ) := interior_eq_empty_iff_dense_compl.mp hthin
  have hclosed : IsClosed (k ⁻¹' geoStrictTransform π C W) :=
    isClosed_closure.preimage hk.continuous
  have hsub : (h ⁻¹' C)ᶜ ⊆ k ⁻¹' geoStrictTransform π C W := by
    intro t ht
    apply subset_closure
    change π (k t) ∈ W ∧ π (k t) ∉ C
    have hcomm_t : π (k t) = h t := congrFun hcomm t
    rw [hcomm_t]
    exact ⟨hW t, ht⟩
  have hwhole : (univ : Set T) ⊆ k ⁻¹' geoStrictTransform π C W := by
    rw [← hdense.closure_eq]
    exact closure_minimal hsub hclosed
  exact fun t => hwhole (mem_univ t)

/-- The unique ambient blowup lift automatically takes values in the SAME
library strict transform of the original, possibly singular subspace. -/
theorem exists_unique_lift_strictTransform (hπ : IsBlowupAlong n C π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h)
    (hinv : (GermIdeal.pullback (m := m) h (vanishingIdeal (n := n) C)).IsInvertible)
    (hW : ∀ t, h t ∈ W) :
    ∃! k : T → Y,
      ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ k ∧
      π ∘ k = h ∧ ∀ t, k t ∈ strictTransform n π W := by
  obtain ⟨k, ⟨hk, hcomm⟩, huniq⟩ := hπ.2.2.2.2 m T h hh hinv
  have hland := mapsTo_geoStrictTransform_of_lift hπ hh hinv hW hk hcomm
  refine ⟨k, ⟨hk, hcomm, fun t =>
    BlowupStrictIdeal.geoStrictTransform_subset_strictTransform hπ W (hland t)⟩, ?_⟩
  intro k' hk'
  exact huniq k' ⟨hk'.1, hk'.2.1⟩

/-- The original unique ambient lift; it is independent of a choice of `W`. -/
def lift (hπ : IsBlowupAlong n C π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h)
    (hinv : (GermIdeal.pullback (m := m) h (vanishingIdeal (n := n) C)).IsInvertible) : T → Y :=
  Classical.choose (hπ.2.2.2.2 m T h hh hinv)

omit [IsComplexManifold n M] [IsComplexManifold n Y] in
theorem lift_contMDiff (hπ : IsBlowupAlong n C π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h)
    (hinv : (GermIdeal.pullback (m := m) h (vanishingIdeal (n := n) C)).IsInvertible) :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (lift hπ hh hinv) :=
  (Classical.choose_spec (hπ.2.2.2.2 m T h hh hinv)).1.1

omit [IsComplexManifold n M] [IsComplexManifold n Y] in
theorem lift_projection (hπ : IsBlowupAlong n C π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h)
    (hinv : (GermIdeal.pullback (m := m) h (vanishingIdeal (n := n) C)).IsInvertible) :
    π ∘ lift hπ hh hinv = h :=
  (Classical.choose_spec (hπ.2.2.2.2 m T h hh hinv)).1.2

theorem lift_mem_strictTransform (hπ : IsBlowupAlong n C π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h)
    (hinv : (GermIdeal.pullback (m := m) h (vanishingIdeal (n := n) C)).IsInvertible)
    (hW : ∀ t, h t ∈ W) (t : T) : lift hπ hh hinv t ∈ strictTransform n π W :=
  BlowupStrictIdeal.geoStrictTransform_subset_strictTransform hπ W
    (mapsTo_geoStrictTransform_of_lift hπ hh hinv hW (lift_contMDiff hπ hh hinv)
      (lift_projection hπ hh hinv) t)

end Lift

section Morphism

open CategoryTheory AlgebraicGeometry HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces

variable {n m : ℕ} {M Y T : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace T] [ChartedSpace (ComplexModel m) T] [IsComplexManifold m T]
  {C W : Set M} {π : Y → M} {h : T → M}

/-- The literal ambient projection restricts to the reduced singular strict
transform. Its range containment uses closedness of the original carrier. -/
def strictTransformProjection (hπ : IsBlowupAlong n C π) (hW : IsClosed W) :
    actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W) ⟶
      actualSubspaceLocallyRingedSpace (n := n) W :=
  actualSubspaceMap hπ.contMDiff (fun _ hy =>
    (closure_minimal sdiff_subset (hW.preimage hπ.contMDiff.continuous)) hy)

/-- The singular projection preserves the original complex structural map. -/
theorem strictTransformProjection_point (hπ : IsBlowupAlong n C π) (hW : IsClosed W) :
    strictTransformProjection hπ hW ≫ subspacePointMap (n := n) W =
      subspacePointMap (n := n) (strictTransform n π W) :=
  actualSubspaceMap_point _ _

/-- The constructed lift induces the full quotient-sheaf morphism from the
whole test manifold into the reduced, possibly singular strict transform. -/
def liftMorphism (hπ : IsBlowupAlong n C π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h)
    (hinv : (GermIdeal.pullback (m := m) h (vanishingIdeal (n := n) C)).IsInvertible)
    (hW : ∀ t, h t ∈ W) :
    actualSubspaceLocallyRingedSpace (n := m) (univ : Set T) ⟶
      actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W) :=
  actualSubspaceMap (lift_contMDiff hπ hh hinv)
    (fun t _ => lift_mem_strictTransform hπ hh hinv hW t)

/-- The actual constructed lift is a complex morphism over the same scalar point. -/
theorem liftMorphism_point (hπ : IsBlowupAlong n C π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h)
    (hinv : (GermIdeal.pullback (m := m) h (vanishingIdeal (n := n) C)).IsInvertible)
    (hW : ∀ t, h t ∈ W) :
    liftMorphism hπ hh hinv hW ≫
      subspacePointMap (n := n) (strictTransform n π W) =
        subspacePointMap (n := m) (univ : Set T) :=
  actualSubspaceMap_point _ _

/-- The exact original ambient lift is retained on points. -/
theorem liftMorphism_base_val (hπ : IsBlowupAlong n C π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h)
    (hinv : (GermIdeal.pullback (m := m) h (vanishingIdeal (n := n) C)).IsInvertible)
    (hW : ∀ t, h t ∈ W) (t : (univ : Set T)) :
    ((liftMorphism hπ hh hinv hW).base t).val = lift hπ hh hinv t.val := rfl

/-- The whole locally ringed space square commutes, including its quotient
structure-sheaf maps, with the same original `h`. -/
theorem liftMorphism_projection (hπ : IsBlowupAlong n C π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h)
    (hinv : (GermIdeal.pullback (m := m) h (vanishingIdeal (n := n) C)).IsInvertible)
    (hW : ∀ t, h t ∈ W) (hWc : IsClosed W) :
    liftMorphism hπ hh hinv hW ≫ strictTransformProjection hπ hWc =
      actualSubspaceMap hh (fun t (_ : t ∈ (univ : Set T)) => hW t) := by
  unfold liftMorphism strictTransformProjection
  rw [← actualSubspaceMap_comp]
  congr 1
  exact lift_projection hπ hh hinv

/-! ### The intrinsic singular projection -/

/-- The actual blowup projection on the strict transform is proper, with no
compactness hypothesis on the ambient manifold. -/
theorem strictTransformProjection_isProperMap (hπ : IsBlowupAlong n C π)
    (hWc : IsClosed W) : IsProperMap (strictTransformProjection hπ hWc).base := by
  change IsProperMap (fun y : strictTransform n π W => (⟨π y.val, _⟩ : W))
  refine isProperMap_of_comp_of_t2 (g := (Subtype.val : W → M))
    ((hπ.contMDiff.continuous.comp continuous_subtype_val).subtype_mk _)
    continuous_subtype_val ?_
  exact (HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ).comp
    (isClosed_closure.isClosedEmbedding_subtypeVal.isProperMap)

/-- Density of the part outside the centre gives the WHOLE original carrier
as the exact image of its singular strict transform. -/
theorem image_strictTransform (hπ : IsBlowupAlong n C π) (hWc : IsClosed W)
    (hdense : W ⊆ closure (W \ C)) : π '' strictTransform n π W = W := by
  apply Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact (closure_minimal sdiff_subset (hWc.preimage hπ.contMDiff.continuous)) hy
  · refine hdense.trans (closure_minimal ?_ ?_)
    · rintro x ⟨hxW, hxC⟩
      have hiso := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
      obtain ⟨y, hy, heq⟩ := hiso.1.surjOn hxC
      refine ⟨y, subset_closure ⟨?_, ?_⟩, heq⟩
      · change π y ∈ W
        rwa [heq]
      · exact fun hexc => disjoint_left.mp hiso.2 hy hexc
    · exact (HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ).isClosedMap
        _ isClosed_closure

/-- The reduced singular projection is surjective onto the original analytic
subspace, rather than merely onto a chosen dense subset. -/
theorem strictTransformProjection_surjective (hπ : IsBlowupAlong n C π)
    (hWc : IsClosed W) (hdense : W ⊆ closure (W \ C)) :
    Function.Surjective (strictTransformProjection hπ hWc).base := by
  intro x
  have hx : x.val ∈ π '' strictTransform n π W := by
    rw [image_strictTransform hπ hWc hdense]
    exact x.property
  obtain ⟨y, hy, heq⟩ := hx
  exact ⟨⟨y, hy⟩, Subtype.ext heq⟩

/-- The actual complement of the ambient centre. -/
def centreComplement (hπ : IsBlowupAlong n C π) : TopologicalSpace.Opens M :=
  ⟨Cᶜ, hπ.1.1.isOpen_compl⟩

/-- Its literal preimage in the ambient blowup. -/
def centreComplementPreimage (hπ : IsBlowupAlong n C π) : TopologicalSpace.Opens Y :=
  ⟨π ⁻¹' Cᶜ, hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous⟩

/-- The existing ambient blowup inverse is a biholomorphism of the two
actual complement opens. -/
def offCentreBiholomorphism (hπ : IsBlowupAlong n C π) :
    centreComplementPreimage hπ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      centreComplement hπ :=
  let hs := BlowupIsomorphismOff.exists_section_compl hπ
  let s := Classical.choose hs
  have hspec := Classical.choose_spec hs
  have hπs : ∀ x : centreComplement hπ, π (s x) = x.val :=
    fun x => congrFun hspec.2.1 x
  { toFun := fun y => ⟨π y.val, y.property⟩
    invFun := fun x => ⟨s x, by
      change π (s x) ∉ C
      rw [hπs x]
      exact x.property⟩
    left_inv := fun y => Subtype.ext (hspec.2.2 y.val y.property)
    right_inv := fun x => Subtype.ext (hπs x)
    contMDiff_toFun :=
      BlowupRestrictOpen.contMDiff_opens_mk (hπ.contMDiff.comp contMDiff_subtype_val)
        (fun y => y.property)
    contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk hspec.1 (fun x => by
      change π (s x) ∉ C
      rw [hπs x]
      exact x.property) }

/-- Over the actual centre complement, the SAME singular strict transform
is exactly the inverse image of the original carrier. -/
theorem mem_strictTransform_iff_of_not_mem_centre (hπ : IsBlowupAlong n C π)
    (hWc : IsClosed W) (y : centreComplementPreimage hπ) :
    y.val ∈ strictTransform n π W ↔ π y.val ∈ W := by
  constructor
  · intro hy
    exact (closure_minimal sdiff_subset (hWc.preimage hπ.contMDiff.continuous)) hy
  · intro hy
    apply subset_closure
    exact ⟨hy, fun he =>
      y.property (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ he)⟩

/-- The actual reduced singular strict transform is isomorphic to the
original reduced subspace off the centre, including full structure sheaves. -/
def offCentreIso (hπ : IsBlowupAlong n C π) (hWc : IsClosed W) :
    actualSubspaceLocallyRingedSpace (n := n)
      ((Subtype.val : centreComplementPreimage hπ → Y) ⁻¹' strictTransform n π W) ≅
    actualSubspaceLocallyRingedSpace (n := n)
      ((Subtype.val : centreComplement hπ → M) ⁻¹' W) :=
  actualSubspaceBiholomorphicIso (offCentreBiholomorphism hπ) _ _
    (fun y => mem_strictTransform_iff_of_not_mem_centre hπ hWc y)

/-- The complement isomorphism is the restriction of the SAME whole
singular blowup projection. -/
theorem offCentreIso_comm (hπ : IsBlowupAlong n C π) (hWc : IsClosed W) :
    HironakaActualAnalyticSubspaceOpenRestriction.actualOpenSubspaceMap
      (n := n) (strictTransform n π W) (centreComplementPreimage hπ) ≫
        strictTransformProjection hπ hWc =
      (offCentreIso hπ hWc).hom ≫
        HironakaActualAnalyticSubspaceOpenRestriction.actualOpenSubspaceMap
          (n := n) W (centreComplement hπ) := by
  unfold HironakaActualAnalyticSubspaceOpenRestriction.actualOpenSubspaceMap
    strictTransformProjection offCentreIso actualSubspaceBiholomorphicIso
  dsimp only
  rw [← actualSubspaceMap_comp, ← actualSubspaceMap_comp]
  rfl

/-- The inverse image of the complement of the centre is genuinely dense
in the SAME singular strict-transform subtype. -/
theorem dense_preimage_compl_centre (hπ : IsBlowupAlong n C π) (hWc : IsClosed W)
    (hdense : W ⊆ closure (W \ C)) :
    Dense ((strictTransformProjection hπ hWc).base ⁻¹' {x : W | x.val ∉ C}) := by
  rw [dense_iff_closure_eq, eq_univ_iff_forall]
  intro y
  rw [closure_subtype]
  have heq : strictTransform n π W = closure (π ⁻¹' (W \ C)) :=
    (BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hdense).symm
  have hy : y.val ∈ closure (π ⁻¹' (W \ C)) := heq ▸ y.property
  refine closure_mono ?_ hy
  intro z hz
  have hz' : z ∈ strictTransform n π W := by
    rw [heq]
    exact subset_closure hz
  exact ⟨⟨z, hz'⟩, hz.2, rfl⟩

/-- The actual pulled centre ideal is locally principal and cancellable along
the possibly singular strict transform. Its relative nonvanishing is produced
from the original density, with no smoothness/irreducibility certificate. -/
theorem isInvertibleAlong_strictTransform (hπ : IsBlowupAlong n C π)
    (hdense : W ⊆ closure (W \ C)) :
    RestrictedIdealQuotient.IsInvertibleAlong n (strictTransform n π W)
      (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) := by
  apply RestrictLeCalculus.isInvertibleAlong_of_isInvertible hπ.2.2.2.1
  intro O hO hOW
  obtain ⟨y, hyO, hyW⟩ := hOW
  have heq : strictTransform n π W = closure (π ⁻¹' (W \ C)) :=
    (BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hdense).symm
  have hy : y ∈ closure (π ⁻¹' (W \ C)) := heq ▸ hyW
  obtain ⟨z, hzO, hz⟩ := mem_closure_iff.mp hy O hO hyO
  refine ⟨z, ⟨hzO, ?_⟩, ?_⟩
  · rw [heq]
    exact subset_closure hz
  · rw [zeroLocus_pullback hπ.contMDiff (isCoherent_vanishingIdeal_centre hπ),
      zeroLocus_vanishingIdeal hπ.1.1]
    exact hz.2

end Morphism

end

end Hironaka.HironakaSingularSubspaceBlowupLift
