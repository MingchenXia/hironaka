import Hironaka.Resolution.HironakaSingularSubspaceBlowupLift
import Hironaka.Resolution.HironakaActualAnalyticSubspaceLocalFunctions
import Mathlib.Algebra.Regular.Basic

/-!
# Actual Cartier stalks of the singular-subspace blowup candidate

The ideal is always the image under the EXISTING actual inclusion/projection
stalk maps, in the actual quotient structure sheaf. One original holomorphic
section on one open generates the whole ideal on every nearby singular stalk.
Its nonzerodivisor property follows from the actual inclusion kernel and
relative cancellation; no regular-generator or free-rank certificate is input.

Blueprint: `hironaka-singular-subspace-blowup-cartier.tex`.
This does not construct arbitrary singular-source chart ratios or their gluing.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartier

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualWholeStalkHolomorphicPullback
  HironakaHolomorphicJetRankLoci
  InvertibleIdealQuotient RestrictedIdealQuotient

noncomputable section

section ActualGerms

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem originalGerm_congr (x : M) {f g : M → ℂ}
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (heq : f =ᶠ[𝓝 x] g) :
    actualOriginalFunctionGerm x f hf = actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original x f g hf hg heq

private theorem originalGerm_mul (x : M) (f g : M → ℂ)
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) :
    actualOriginalFunctionGerm x (fun z => f z * g z) (hf.mul hg) =
      actualOriginalFunctionGerm x f hf * actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [map_mul, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

private theorem exists_original_representative (x : M)
    (r : actualComplexStructureStalk (n := n) x) :
    ∃ (f : M → ℂ) (hf : HolomorphicAt n f x), actualOriginalFunctionGerm x f hf = r := by
  obtain ⟨U, hxU, s, hr⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  exact ⟨sectionExtension U s, sectionExtension_holomorphicAt U s x hxU,
    (actualOriginalFunctionGerm_eq_section U x hxU s (sectionExtension U s)
      (sectionExtension_holomorphicAt U s x hxU) Filter.EventuallyEq.rfl).trans hr⟩

/-- The whole actual vanishing stalk retains precisely the original
holomorphic germs vanishing on the original subset near the same point. -/
theorem actualOriginalGerm_mem_vanishingIdeal_iff (W : Set M) (x : M)
    (f : M → ℂ) (hf : HolomorphicAt n f x) :
    actualOriginalFunctionGerm x f hf ∈
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) x ↔
      (vanishingIdeal (n := n) W).mem x f := by
  constructor
  · intro hmem
    let F := (actualComplexStructureSheaf (n := n) M).presheaf
    obtain ⟨U, hxU, s, hs⟩ := exists_actual_section_of_original_holomorphicAt x f hf
    have hgs := actualOriginalFunctionGerm_eq_section U x hxU s f hf hs
    rw [hgs] at hmem
    have himg : F.germ U x hxU s ∈
        actualIdealSectionGermImage (vanishingIdeal (n := n) W) x := by
      rw [actualCentreIdealSectionGermImage_eq_whole W x]
      exact hmem
    obtain ⟨V, hxV, t, ht⟩ := himg
    obtain ⟨Z, hxZ, iU, iV, heq⟩ := F.germ_eq x hxU hxV s t.val ht.symm
    refine ⟨hf, ?_⟩
    filter_upwards [Z.isOpen.mem_nhds hxZ, hs] with z hz hsf hzW
    have hzU : z ∈ U := leOfHom iU hz
    have hzV : z ∈ V := leOfHom iV hz
    calc
      f z = sectionExtension U s z := hsf.symm
      _ = s ⟨z, hzU⟩ := sectionExtension_apply U s z hzU
      _ = (F.map iU.op s) ⟨z, hz⟩ := rfl
      _ = (F.map iV.op t.val) ⟨z, hz⟩ := congrArg (fun a => a ⟨z, hz⟩) heq
      _ = t.val ⟨z, hzV⟩ := rfl
      _ = 0 := (actualSectionIdeal_vanishing_iff W V t.val).mp t.property z hzV hzW
  · intro hfW
    exact Ideal.subset_span ⟨f, hf, hfW, rfl⟩

private theorem actualWholeStalkIdeal_eq_span_generator (A : GermIdeal n M) (x : M)
    (a : M → ℂ) (ha : HolomorphicAt n a x)
    (hgen : ∀ f, A.mem x f ↔ IsInSpanAt (n := n) (· = a) x f) :
    actualWholeSheafStalkIdeal A x = Ideal.span {actualOriginalFunctionGerm x a ha} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f, hf, hmem, rfl⟩
    obtain ⟨_, b, hb, heq⟩ := isInSpanAt_eq_iff.mp ((hgen f).mp hmem)
    have hfac : actualOriginalFunctionGerm x f hf =
        actualOriginalFunctionGerm x b hb * actualOriginalFunctionGerm x a ha :=
      (originalGerm_congr x hf (hb.mul ha) heq).trans (originalGerm_mul x b a hb ha)
    rw [hfac]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (mem_singleton _))
  · apply Ideal.span_le.mpr
    intro r hr
    have heq : r = actualOriginalFunctionGerm x a ha := mem_singleton_iff.mp hr
    rw [heq]
    exact Ideal.subset_span ⟨a, ha, (hgen a).mpr (isInSpanAt_self rfl ha), rfl⟩

private theorem actualSubspace_generator_isRegular {W U : Set M} (hU : IsOpen U)
    {a : M → ℂ}
    (hnon : ∀ V : Set M, IsOpen V → V ⊆ U → (V ∩ W).Nonempty →
      ∃ z ∈ V ∩ W, a z ≠ 0)
    (x : W) (hxU : x.val ∈ U) (ha : HolomorphicAt n a x.val) :
    IsRegular (((actualSubspaceInclusion (n := n) W).stalkMap x)
      (actualOriginalFunctionGerm x.val a ha)) := by
  let q := ((actualSubspaceInclusion (n := n) W).stalkMap x).hom
  let alpha := q (actualOriginalFunctionGerm x.val a ha)
  have hzero : ∀ b, alpha * b = 0 → b = 0 := by
    intro b hb
    obtain ⟨r, hr⟩ := actualSubspaceInclusionRingedHom_stalk_surjective (n := n) W x b
    obtain ⟨f, hf, hfr⟩ := exists_original_representative x.val r
    have hr' : q r = b := hr
    have hprod : q (actualOriginalFunctionGerm x.val (fun z => a z * f z) (ha.mul hf)) = 0 := by
      rw [originalGerm_mul x.val a f ha hf, map_mul, hfr, hr']
      exact hb
    have hmem : actualOriginalFunctionGerm x.val (fun z => a z * f z) (ha.mul hf) ∈
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) x.val := by
      rw [← actualSubspaceInclusion_stalk_kernel W x]
      exact hprod
    have hvan := (actualOriginalGerm_mem_vanishingIdeal_iff W x.val _ (ha.mul hf)).mp hmem
    have hcancel : ∀ᶠ z in 𝓝 x.val, z ∈ W → f z = 0 :=
      eventuallyEq_within_of_mul_eventuallyEq_within hU hnon hxU hf (holomorphicAt_const 0)
        (by simpa only [mul_zero] using hvan.2)
    have hfmem : actualOriginalFunctionGerm x.val f hf ∈
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) x.val :=
      (actualOriginalGerm_mem_vanishingIdeal_iff W x.val f hf).mpr ⟨hf, hcancel⟩
    have hmapf : q (actualOriginalFunctionGerm x.val f hf) = 0 := by
      rw [← actualSubspaceInclusion_stalk_kernel W x] at hfmem
      exact hfmem
    rw [hfr, hr'] at hmapf
    exact hmapf
  have hleft : IsLeftRegular alpha := by
    intro b c hbc
    apply sub_eq_zero.mp
    apply hzero
    change alpha * b = alpha * c at hbc
    rw [mul_sub, hbc, sub_self]
  refine ⟨hleft, ?_⟩
  intro b c hbc
  apply hleft
  simpa only [mul_comm] using hbc

/-- One actual ambient section on one open gives a principal nonzerodivisor
generator for the WHOLE restricted ideal at EVERY nearby singular stalk. -/
theorem exists_local_actual_cartier_generator {W : Set M} {A : GermIdeal n M}
    (hA : IsInvertibleAlong n W A) (x : W) :
    ∃ (U : Opens M) (_hxU : x.val ∈ U) (a : actualComplexSection (n := n) U),
      ∀ (y : W) (hy : y.val ∈ U),
        let alpha := ((actualSubspaceInclusion (n := n) W).stalkMap y)
          ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y.val hy a)
        Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap y).hom
          (actualWholeSheafStalkIdeal A y.val) = Ideal.span {alpha} ∧ IsRegular alpha := by
  obtain ⟨U, hU, hxU, a, ha, hnon, hgen⟩ := hA x.val x.property
  let O : Opens M := ⟨U, hU⟩
  let s : actualComplexSection (n := n) O := ⟨fun z : O => a z.val, by
    change ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (fun z : O => a z.val)
    intro z
    apply contMDiffAt_subtype_iff.mpr
    exact contMDiffAt_of_eventually_mdifferentiableAt
      (holomorphicAt_of_mdifferentiableOn hU ha z.property)⟩
  refine ⟨O, hxU, s, ?_⟩
  intro y hy
  have hay := holomorphicAt_of_mdifferentiableOn hU ha hy
  have hs : sectionExtension O s =ᶠ[𝓝 y.val] a := by
    filter_upwards [hU.mem_nhds hy] with z hz
    rw [sectionExtension_apply O s z hz]
  have hsec := actualOriginalFunctionGerm_eq_section O y.val hy s a hay hs
  change Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap y).hom
      (actualWholeSheafStalkIdeal A y.val) =
        Ideal.span {((actualSubspaceInclusion (n := n) W).stalkMap y)
          ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y.val hy s)} ∧ _
  rw [← hsec]
  refine ⟨?_, actualSubspace_generator_isRegular hU hnon y hy hay⟩
  rw [actualWholeStalkIdeal_eq_span_generator A y.val a hay (hgen y.val hy),
    Ideal.map_span, Set.image_singleton]

end ActualGerms

section Pullback

variable {n m : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

/-- The WHOLE ideal image dictionary for the actual native structure-sheaf
stalk map, using the genuine preferred-chart conjugacy only in its proof. -/
theorem map_actualWholeSheafStalkIdeal_native_pullback {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    (A : GermIdeal m Y) (hA : A.IsCoherent) (x : X) :
    Ideal.map ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x).hom
      (actualWholeSheafStalkIdeal A (f x)) =
        actualWholeSheafStalkIdeal (GermIdeal.pullback (m := n) f A) x := by
  let F : actualComplexStructureStalk (n := m) (f x) →+*
      actualComplexStructureStalk (n := n) x :=
    ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x).hom
  let E := actualStalkChartEquiv (n := n) x
  change Ideal.map F (actualWholeSheafStalkIdeal A (f x)) = _
  apply E.idealComapOrderIso.symm.injective
  change Ideal.map E.toRingHom
      (Ideal.map F (actualWholeSheafStalkIdeal A (f x))) =
    Ideal.map E.toRingHom (actualWholeSheafStalkIdeal (GermIdeal.pullback (m := n) f A) x)
  rw [Ideal.map_map, map_actualWholeSheafStalkIdeal]
  have hconj : E.toRingHom.comp F =
      (actualHolomorphicGermPullback hf x).toRingHom.comp
        (actualStalkChartEquiv (n := m) (f x)).toRingHom := by
    apply RingHom.ext
    intro r
    exact actualNativeStalk_chart_pullback hf x r
  rw [hconj, ← Ideal.map_map, map_actualWholeSheafStalkIdeal,
    map_wholeChartStalkIdeal_actual_pullback hf A hA x]

/-- The actual projection and inclusion stalk maps retain the ENTIRE
restricted original ideal through the genuine subspace morphism. -/
theorem map_actualSubspace_stalk_ideal_pullback {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set X} {D : Set Y} (hCD : ∀ x ∈ C, f x ∈ D)
    (A : GermIdeal m Y) (hA : A.IsCoherent) (x : C) :
    Ideal.map ((actualSubspaceMap hf hCD).stalkMap x).hom
      (Ideal.map ((actualSubspaceInclusion (n := m) D).stalkMap
        (actualSubspaceMapTop hf hCD x)).hom
          (actualWholeSheafStalkIdeal A (f x.val))) =
    Ideal.map ((actualSubspaceInclusion (n := n) C).stalkMap x).hom
      (actualWholeSheafStalkIdeal (GermIdeal.pullback (m := n) f A) x.val) := by
  let z : D := actualSubspaceMapTop hf hCD x
  let p : ((actualSubspaceSheaf (n := m) D).presheaf.stalk z).carrier →+*
      ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier :=
    ((actualSubspaceMap hf hCD).stalkMap x).hom
  let qD : actualComplexStructureStalk (n := m) (f x.val) →+*
      ((actualSubspaceSheaf (n := m) D).presheaf.stalk z).carrier :=
    ((actualSubspaceInclusion (n := m) D).stalkMap z).hom
  let qC : actualComplexStructureStalk (n := n) x.val →+*
      ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier :=
    ((actualSubspaceInclusion (n := n) C).stalkMap x).hom
  let F : actualComplexStructureStalk (n := m) (f x.val) →+*
      actualComplexStructureStalk (n := n) x.val :=
    ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val).hom
  change Ideal.map p (Ideal.map qD (actualWholeSheafStalkIdeal A (f x.val))) =
    Ideal.map qC (actualWholeSheafStalkIdeal (GermIdeal.pullback (m := n) f A) x.val)
  rw [Ideal.map_map]
  have hsquare : p.comp qD = qC.comp F := by
    ext r
    exact ConcreteCategory.congr_hom (actualSubspaceRingedMap_stalk_square hf hCD x) r
  rw [hsquare, ← Ideal.map_map]
  have hnative : Ideal.map F (actualWholeSheafStalkIdeal A (f x.val)) =
      actualWholeSheafStalkIdeal (GermIdeal.pullback (m := n) f A) x.val :=
    map_actualWholeSheafStalkIdeal_native_pullback hf A hA x.val
  rw [hnative]

end Pullback

section Projection

open HironakaSingularSubspaceBlowupLift

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

/-- The actual ideal pulled through the SAME singular projection stalk map
has one actual section generator which is a nonzerodivisor at ALL nearby
singular quotient stalks. No target ideal equality or free-rank premise. -/
theorem exists_local_projection_cartier_generator
    (hπ : IsBlowupAlong n C π) (hWc : IsClosed W)
    (hdense : W ⊆ closure (W \ C)) (x : strictTransform n π W) :
    ∃ (U : Opens Y) (_hxU : x.val ∈ U) (a : actualComplexSection (n := n) U),
      ∀ (y : strictTransform n π W) (hy : y.val ∈ U),
        let p := strictTransformProjection hπ hWc
        let alpha := ((actualSubspaceInclusion (n := n) (strictTransform n π W)).stalkMap y)
          ((actualComplexStructureSheaf (n := n) Y).presheaf.germ U y.val hy a)
        Ideal.map (p.stalkMap y).hom
          (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (p.base y)).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (π y.val))) =
          Ideal.span {alpha} ∧ IsRegular alpha := by
  obtain ⟨U, hxU, a, ha⟩ := exists_local_actual_cartier_generator
    (isInvertibleAlong_strictTransform hπ hdense) x
  refine ⟨U, hxU, a, ?_⟩
  intro y hy
  have hmap := map_actualSubspace_stalk_ideal_pullback hπ.contMDiff
    (fun z (hz : z ∈ strictTransform n π W) =>
      (closure_minimal sdiff_subset (hWc.preimage hπ.contMDiff.continuous)) hz)
    (vanishingIdeal (n := n) C)
    (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ) y
  change Ideal.map ((strictTransformProjection hπ hWc).stalkMap y).hom
      (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap
        ((strictTransformProjection hπ hWc).base y)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (π y.val))) = _ ∧ _
  exact ⟨hmap.trans (ha y hy).1, (ha y hy).2⟩

end Projection

end

end Hironaka.HironakaSingularSubspaceBlowupCartier
