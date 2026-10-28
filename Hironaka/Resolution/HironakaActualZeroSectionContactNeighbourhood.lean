/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualZeroSectionSubmanifoldCoefficients
import Hironaka.Analytic.AnalyticSubsetOpens

/-!
# Actual closed-section contact neighbourhoods for the same original direction

At an original point of the closed regular carrier, the source tangent
field and the true product-flattening chain rule internally construct a
base neighbourhood on which the SAME restricted source function is a genuine
tangent direction. The actual lower contact carrier is closed regular on
that open, with the literal whole source-lift equality. No target direction,
canonical value, centre or history certificate is supplied. No global target
closedness or arbitrary pullback-boundary wellformedness is asserted.
Blueprint: `hironaka-actual-zero-section-contact-neighbourhood-extension.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualZeroSectionContactNeighbourhood
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaRelativeNormalIdeal HironakaActualIntrinsicStableAmbientIso HironakaActualCentreJointJets
  HironakaActualZeroSectionSubmanifoldDifferentials DerivativeIdealAlongCoherent
  BlowupFlatCoordinates GiraudAlong TangentDirectionAlong DerivativeIdealAlong
  RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient
variable {n : ℕ}

private theorem join_plane_iff (a : ComplexModel n) (b : ComplexModel 1) {k : ℕ} (hk : k ≤ n) :
    HironakaActualIntrinsicStableAmbientIso.join a b∈complexCoordinatePlane (n+1) k ↔
      a∈complexCoordinatePlane n k ∧ b=0 := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro i hi
      simpa [HironakaActualIntrinsicStableAmbientIso.join] using h (i.castAdd 1) hi
    · ext i
      simpa [HironakaActualIntrinsicStableAmbientIso.join] using h (i.natAdd n) (by simp;omega)
  · rintro ⟨ha,hb⟩ i hi
    refine Fin.addCases (fun j hj => ?_) (fun j _hj => ?_) i hi
    · simpa [HironakaActualIntrinsicStableAmbientIso.join] using ha j hj
    · simp [HironakaActualIntrinsicStableAmbientIso.join,hb]

private theorem productFlat_carrier (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    {A : Set (ComplexModel n)} {k : ℕ} (hk : k ≤ n)
    (hflat : ∀ {y : ComplexModel n},y∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y∈Φ.source →
      (y∈A ↔ Φ.toFun (chartAt (ComplexModel n) x y)∈complexCoordinatePlane n k))
    {z : ComplexModel (n+1)} (hz : z∈(productFlat x Φ).source) :
    z∈liftedCarrier A ↔ (productFlat x Φ).toFun z∈complexCoordinatePlane (n+1) k := by
  have hy : tangentProjection n 1 z∈(chartAt (ComplexModel n) x).source := by simp
  have hΦ : chartAt (ComplexModel n) x (tangentProjection n 1 z)∈Φ.source := hz
  have h := hflat hy hΦ
  change (tangentProjection n 1 z∈A ∧ actualJointNormalProjection n 1 z=0) ↔
    HironakaActualIntrinsicStableAmbientIso.join (Φ.toFun (tangentProjection n 1 z))
      (actualJointNormalProjection n 1 z)∈complexCoordinatePlane (n+1) k
  rw [join_plane_iff _ _ hk]
  exact and_congr_left fun _ => h

private theorem section_single (n : ℕ) (i : Fin n) :
    tangentInclusion n 1 (EuclideanSpace.single i 1)=EuclideanSpace.single (i.castAdd 1) 1 := by
  ext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp
  · have hne : k.natAdd n≠i.castAdd 1 := by
      intro he
      have h := congrArg Fin.val he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at h
      omega
    simp [hne]

private theorem productFlat_domain_iff (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (z : ComplexModel (n+1)) :
    z ∈ flatDomain (productFlat x Φ) ↔ tangentProjection n 1 z ∈ flatDomain Φ := by
  change (z∈Set.univ ∧ tangentProjection n 1 z∈Φ.source) ↔
    (tangentProjection n 1 z∈Set.univ ∧ tangentProjection n 1 z∈Φ.source)
  simp only [mem_univ, true_and]

private theorem productFlat_map_section (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (u : ComplexModel n) :
    flatMap (productFlat x Φ) (tangentInclusion n 1 u)=tangentInclusion n 1 (flatMap Φ u) :=
  productFlat_section x Φ u

private theorem productFlat_inv_section (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (u : ComplexModel n) :
    flatInv (productFlat x Φ) (tangentInclusion n 1 u)=tangentInclusion n 1 (flatInv Φ u) :=
  productFlat_inverse_section x Φ u

theorem product_flat_partial_zero_section (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    {y : ComplexModel n} (hy : y∈flatDomain Φ) (g : ComplexModel (n+1) → ℂ)
    (hg : HolomorphicAt (n+1) g (tangentInclusion n 1 y)) (i : Fin n) :
    flatPartial (productFlat x Φ) (i.castAdd 1) g (tangentInclusion n 1 y)=
      flatPartial Φ i (g ∘ tangentInclusion n 1) y := by
  have hsy : tangentInclusion n 1 y∈flatDomain (productFlat x Φ) := by
    apply (productFlat_domain_iff x Φ _).mpr
    rwa [tangentProjection_tangentInclusion]
  have hcomp : HolomorphicAt n (g ∘ tangentInclusion n 1) y :=
    hg.comp_contMDiff (Eventually.of_forall fun _ => (tangentInclusion n 1).contMDiff.contMDiffAt)
  rw [flatPartial_eq hsy hg,flatPartial_eq hy hcomp]
  have hΓsrc : (productFlat x Φ).source⊆
      (chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x)).target := by
    change _ ⊆ (Set.univ : Set (ComplexModel (n+1)))
    exact subset_univ _
  have hgd := differentiableAt_comp_flatInv (flatMap_mem_target hsy) hΓsrc
    (show HolomorphicAt (n+1) g (flatInv (productFlat x Φ)
      (flatMap (productFlat x Φ) (tangentInclusion n 1 y))) by
        rw [flatInv_flatMap hsy];exact hg)
  rw [productFlat_map_section] at hgd
  have heq : (g ∘ flatInv (productFlat x Φ)) ∘ tangentInclusion n 1=
      (g ∘ tangentInclusion n 1) ∘ flatInv Φ := by
    funext u
    simp only [Function.comp_apply,productFlat_inv_section]
  have hc := (hgd.hasFDerivAt.comp (flatMap Φ y) (tangentInclusion n 1).hasFDerivAt).fderiv
  rw [heq] at hc
  have h := congrArg (fun L => L (EuclideanSpace.single i 1)) hc
  simp only [ContinuousLinearMap.comp_apply,section_single] at h
  rw [productFlat_map_section]
  exact h.symm

/-- The SAME original source direction internally constructs a genuine
base tangent direction on one actual neighbourhood of the original point. -/
theorem exists_actual_zero_section_contact_neighbourhood {A : Set (ComplexModel n)}
    (hA : IsClosedSubmanifold n A) (J : GermIdeal (n+1) (ComplexModel (n+1)))
    (hJ : J.IsCoherent) {μ : ℕ} {U : Set (ComplexModel (n+1))}
    {u : ComplexModel (n+1) → ℂ} (hu : IsTangentDirectionAlong (liftedCarrier A) J μ U u)
    (x : ComplexModel n) (hx : x∈A) (hxU : tangentInclusion n 1 x∈U)
    (hu0 : u (tangentInclusion n 1 x)=0) :
    ∃ W : Opens (ComplexModel n), x∈W ∧ (W : Set (ComplexModel n))⊆tangentInclusion n 1 ⁻¹' U ∧
      IsTangentDirectionAlong A (GermIdeal.pullback (m := n) (tangentInclusion n 1) J)
        μ W (u ∘ tangentInclusion n 1) := by
  obtain ⟨k,hkn,_hx,Φ,hΦsrc,_h0,hflat⟩ := hA.2 x hx
  have hΓsrc : (productFlat x Φ).source⊆
      (chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x)).target := by
    change _ ⊆ (Set.univ : Set (ComplexModel (n+1)))
    exact subset_univ _
  have hΓflat : ∀ {z : ComplexModel (n+1)},
      z∈(chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x)).source →
      chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x) z∈(productFlat x Φ).source →
      (z∈liftedCarrier A ↔ (productFlat x Φ).toFun
        (chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x) z)∈complexCoordinatePlane (n+1) k) := by
    intro z _ hz
    exact productFlat_carrier x Φ hkn hflat hz
  have hholJ : ∀ z g,J.mem z g → HolomorphicAt (n+1) g z :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hg
  have huhol : ∀ z∈U,HolomorphicAt (n+1) u z :=
    fun z hz => holomorphicAt_of_mem_iterDerivIdealAlong hholJ (μ-1) z u (hu.mem z hz)
  obtain ⟨e,ξ,hξ,hne⟩ := hu.multiplicity_one _ hxU hu0
  obtain ⟨j,hjk,hj⟩ := exists_flatPartial_ne_zero hΓsrc hΓflat (mem_flatDomain_self _)
    ((section_mem_liftedCarrier_iff A x).mpr hx) (huhol _ hxU) hξ hne
  let i : Fin n := ⟨j.val,by omega⟩
  have hij : i.castAdd 1=j := Fin.ext rfl
  have hi : i.val<k := hjk
  have hbase : flatPartial Φ i (u ∘ tangentInclusion n 1) x≠0 := by
    rw [←hij,product_flat_partial_zero_section x Φ (mem_flatDomain_self Φ) u (huhol _ hxU)] at hj
    exact hj
  have hcomp : HolomorphicAt n (u ∘ tangentInclusion n 1) x :=
    (huhol _ hxU).comp_contMDiff (Eventually.of_forall fun _ => (tangentInclusion n 1).contMDiff.contMDiffAt)
  have hcont := (holomorphicAt_flatPartial i (mem_flatDomain_self Φ) hcomp).self_of_nhds.continuousAt
  obtain ⟨V,hVsub,hVo,hxV⟩ := mem_nhds_iff.mp (hcont.eventually (isOpen_ne.mem_nhds hbase))
  let W : Opens (ComplexModel n) := ⟨(V∩tangentInclusion n 1 ⁻¹' U)∩flatDomain Φ,
    (hVo.inter (hu.isOpen.preimage (tangentInclusion n 1).continuous)).inter (isOpen_flatDomain Φ)⟩
  refine ⟨W,⟨⟨hxV,hxU⟩,mem_flatDomain_self Φ⟩,fun _ hy => hy.1.2,⟨W.isOpen,?_,?_⟩⟩
  · intro y hy
    rw [←zero_section_submanifold_iterDerivIdealAlong hA J hJ (μ-1)]
    apply GermIdeal.mem_pullback_iff.mpr
    exact isInSpanAt_self ⟨u,hu.mem _ hy.1.2,rfl⟩
      ((huhol _ hy.1.2).comp_contMDiff
        (Eventually.of_forall fun _ => (tangentInclusion n 1).contMDiff.contMDiffAt))
  · intro y hy _
    exact ⟨complexChartAt x,flatField Φ (EuclideanSpace.single i 1),
      isTangentField_flatField hΦsrc hflat (single_mem_complexCoordinatePlane hi) hy.2,hVsub hy.1.1⟩

private theorem lifted_contact_eq (A : Set (ComplexModel n)) (u : ComplexModel (n+1) → ℂ) :
    liftedCarrier A∩{z | u z=0}=liftedCarrier (A∩{x | u (tangentInclusion n 1 x)=0}) := by
  ext z
  change (tangentProjection n 1 z∈A ∧ actualJointNormalProjection n 1 z=0)∧u z=0 ↔
    (tangentProjection n 1 z∈A ∧ u (tangentInclusion n 1 (tangentProjection n 1 z))=0)∧
      actualJointNormalProjection n 1 z=0
  have hsec (hz : actualJointNormalProjection n 1 z=0) :
      tangentInclusion n 1 (tangentProjection n 1 z)=z := by
    simpa only [HironakaActualIntrinsicStableAmbientIso.join,hz,map_zero,add_zero]
      using join_projections (n := n) (m := 1) z
  constructor
  · rintro ⟨⟨hzA,hzq⟩,hzu⟩
    exact ⟨⟨hzA,by rwa [hsec hzq]⟩,hzq⟩
  · rintro ⟨⟨hzA,hzu⟩,hzq⟩
    exact ⟨⟨hzA,hzq⟩,by rwa [←hsec hzq]⟩

/-- The internally constructed original contact carrier is a genuine closed
submanifold of W; its source lift is the SAME literal source zero carrier. -/
theorem exists_actual_zero_section_regular_contact {A : Set (ComplexModel n)}
    (hA : IsClosedSubmanifold n A) (J : GermIdeal (n+1) (ComplexModel (n+1)))
    (hJ : J.IsCoherent) {μ : ℕ} {U : Set (ComplexModel (n+1))}
    {u : ComplexModel (n+1) → ℂ} (hu : IsTangentDirectionAlong (liftedCarrier A) J μ U u)
    (x : ComplexModel n) (hx : x∈A) (hxU : tangentInclusion n 1 x∈U)
    (hu0 : u (tangentInclusion n 1 x)=0) :
    ∃ W : Opens (ComplexModel n), x∈W ∧ (W : Set (ComplexModel n))⊆tangentInclusion n 1 ⁻¹' U ∧
      IsTangentDirectionAlong A (GermIdeal.pullback (m := n) (tangentInclusion n 1) J)
        μ W (u ∘ tangentInclusion n 1) ∧
      IsClosedSubmanifold n ((Subtype.val : W → ComplexModel n) ⁻¹'
        (A∩{y | u (tangentInclusion n 1 y)=0}∩(W : Set (ComplexModel n)))) ∧
      liftedCarrier A∩{z | u z=0}=liftedCarrier (A∩{y | u (tangentInclusion n 1 y)=0}) := by
  obtain ⟨W,hxW,hWsub,hw⟩ := exists_actual_zero_section_contact_neighbourhood hA J hJ hu x hx hxU hu0
  have hJP := isCoherent_pullback (tangentInclusion n 1).contMDiff hJ
  have hholJ : ∀ y g,(GermIdeal.pullback (m := n) (tangentInclusion n 1) J).mem y g →
      HolomorphicAt n g y := fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJP hg
  have hholu : ∀ y∈(W : Set (ComplexModel n)),HolomorphicAt n (u ∘ tangentInclusion n 1) y :=
    fun y hy => holomorphicAt_of_mem_iterDerivIdealAlong hholJ (μ-1) y _ (hw.mem y hy)
  refine ⟨W,hxW,hWsub,hw,⟨isClosed_preimage_val_inter_zeroSet hA.1 hholu,?_⟩,lifted_contact_eq A u⟩
  intro y hy
  obtain ⟨k,_hk,hcontact⟩ := hw.regularAtDim_contact hholJ hA hy
  exact ⟨k-1,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hcontact⟩

end
end Hironaka.HironakaActualZeroSectionContactNeighbourhood
