/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaDisjointControlledNormalPivot
import Hironaka.Resolution.HironakaActualClosedContactControlledRestriction

/-! Matched coordinates on the EXISTING native intrinsic atlas, and whole
coherent-ideal plane trace. No radicalization or desired trace certificate. -/
set_option autoImplicit false
open Set Filter Classical IsManifold
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaDisjointMatchedControlledTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.RegularLocusDense
  SubmanifoldChartedSpace HironakaRelativeNormalIdeal
  HironakaSmoothSubmersionGermIdealColon HironakaActualSingularChartTransport
  RelativePrincipalizationSpan GermIdealPullbackCalculus HolGerm HironakaHolomorphicJetChartInvariance
  ManifoldFiniteSpanChartTransport EuclideanHolomorphicGermSpan InvertibleIdealQuotient

private def matchedPartial {d : ℕ} {S Z : Type} [TopologicalSpace S] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel d) S] [ChartedSpace (ComplexModel d) Z]
    (E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ S)
    (e : OpenPartialHomeomorph S (ComplexModel d)) (z : Z) :=
  (chartAt (ComplexModel d) z).symm.trans (E.toHomeomorph.toOpenPartialHomeomorph.trans e)

private theorem matchedPartial_holomorphic {d : ℕ} {S Z : Type}
    [TopologicalSpace S] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel d) S] [ChartedSpace (ComplexModel d) Z]
    [IsComplexManifold d S] [IsComplexManifold d Z]
    (E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ S)
    (e : OpenPartialHomeomorph S (ComplexModel d))
    (he : e    ∈    maximalAtlas 𝓘(ℂ,ComplexModel d) ∞ S) (z : Z) :
    DifferentiableOn ℂ (matchedPartial E e z) (matchedPartial E e z).source ∧
    DifferentiableOn ℂ (matchedPartial E e z).symm (matchedPartial E e z).target := by
  constructor
  · intro u hu
    have h1:=contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ComplexModel d)) (n:=∞) z) hu.1
    have h2:=E.contMDiff.contMDiffAt.comp _ h1
    have h3:=contMDiffAt_of_mem_maximalAtlas he hu.2.2
    have hh:=h3.comp u h2
    exact ((mdifferentiableAt_iff_differentiableAt).mp (hh.mdifferentiableAt (by simp))).differentiableWithinAt
  · intro u hu
    have h1:=contMDiffAt_symm_of_mem_maximalAtlas he hu.1.1
    have h2:=E.symm.contMDiff.contMDiffAt.comp _ h1
    have h3:=contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ComplexModel d)) (n:=∞) z) hu.2
    have hh:=h3.comp u h2
    exact ((mdifferentiableAt_iff_differentiableAt).mp (hh.mdifferentiableAt (by simp))).differentiableWithinAt

private def matchedCoordinates {d : ℕ} {S Z : Type}
    [TopologicalSpace S] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel d) S] [ChartedSpace (ComplexModel d) Z]
    [IsComplexManifold d S] [IsComplexManifold d Z]
    (E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ S)
    (e : OpenPartialHomeomorph S (ComplexModel d))
    (he : e    ∈    maximalAtlas 𝓘(ℂ,ComplexModel d) ∞ S) (z : Z) (hz : E z    ∈    e.source) :
    LocalHolomorphicEquivAt (chartAt (ComplexModel d) z z) where
  source := (matchedPartial E e z).source
  target := (matchedPartial E e z).target
  isOpen_source := (matchedPartial E e z).open_source
  isOpen_target := (matchedPartial E e z).open_target
  center_mem_source := by
    refine ⟨mem_chart_target _ z,?_⟩
    change (chartAt (ComplexModel d) z).symm (chartAt (ComplexModel d) z z)    ∈    (E.toHomeomorph.toOpenPartialHomeomorph.trans e).source
    rw [(chartAt (ComplexModel d) z).left_inv (mem_chart_source _ z)]
    exact ⟨mem_univ z,hz⟩
  toFun := matchedPartial E e z
  invFun := (matchedPartial E e z).symm
  toFun_holomorphic := (matchedPartial_holomorphic E e he z).1
  invFun_holomorphic := (matchedPartial_holomorphic E e he z).2
  mapsTo_toFun := (matchedPartial E e z).mapsTo
  mapsTo_invFun := (matchedPartial E e z).symm.mapsTo
  left_inv := fun _ hu => (matchedPartial E e z).left_inv hu
  right_inv := fun _ hu => (matchedPartial E e z).right_inv hu

private theorem inclusion_eq_tangent (d t : ℕ) (u : ComplexModel d) :
    coordinateInclusion (d+t) d u=tangentInclusion d t u := by
  ext i
  by_cases hi : i.val<d
  · let j : Fin d:=⟨i.val,hi⟩
    have hij : j.castAdd t=i:=Fin.ext rfl
    rw [←hij,tangentInclusion_tangent,coordinateInclusion_apply]
    simp only [Fin.val_castAdd,dif_pos j.isLt]
  · let j : Fin t:=⟨i.val-d,by have hlt:=i.isLt;omega⟩
    have hij : j.natAdd d=i:=by apply Fin.ext;dsimp only [j,Fin.natAdd];omega
    rw [←hij,tangentInclusion_normal,coordinateInclusion_apply]
    simp only [Fin.val_natAdd]
    split_ifs with h
    · omega
    · rfl

private theorem trace_adapted_germ {d t : ℕ} {Y Z : Type}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]
    (f : Z → Y) (y : Y) (z : Z)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
    (h0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y)=0)
    (Ψ : LocalHolomorphicEquivAt (chartAt (ComplexModel d) z z))
    (hΨ0 : Ψ.toFun (chartAt (ComplexModel d) z z)=0)
    (hcoord : ∀ᶠ u in 𝓝 (0 : ComplexModel d),f (inverseCoordinates Ψ u)=inverseCoordinates Θ (tangentInclusion d t u))
    (F : Y → ℂ) (hF : HolomorphicAt (d+t) F y) (hFf : HolomorphicAt d (F ∘ f) z) :
    planeTrace d t (adaptedGerm y Θ h0 F hF)=adaptedGerm z Ψ hΨ0 (F ∘ f) hFf := by
  unfold planeTrace adaptedGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact hcoord.mono fun u hu => (congrArg F hu).symm

private theorem whole_trace_of_inverse {d t : ℕ} {Y Z : Type}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]
    (f : Z → Y) (hf : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ f)
    (y : Y) (z : Z) (hpoint : f z=y)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
    (h0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y)=0)
    (Ψ : LocalHolomorphicEquivAt (chartAt (ComplexModel d) z z))
    (hΨ0 : Ψ.toFun (chartAt (ComplexModel d) z z)=0)
    (hcoord : ∀ᶠ u in 𝓝 (0 : ComplexModel d),f (inverseCoordinates Ψ u)=inverseCoordinates Θ (tangentInclusion d t u))
    (A : GermIdeal (d+t) Y) (hA : A.IsCoherent) :
    Ideal.map (planeTrace d t).toRingHom (adaptedIdeal A y Θ h0)=
      adaptedIdeal (GermIdeal.pullback (m:=d) f A) z Ψ hΨ0 := by
  have hcomp (F : Y → ℂ) (hF : HolomorphicAt (d+t) F y) : HolomorphicAt d (F ∘ f) z := by
    have hF' : HolomorphicAt (d+t) F (f z):=hpoint.symm ▸ hF
    exact hF'.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt)
  apply le_antisymm
  · rw [adaptedIdeal,Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro g ⟨a,⟨F,hF,hmem,rfl⟩,rfl⟩
    change planeTrace d t (adaptedGerm y Θ h0 F hF)  ∈  adaptedIdeal (GermIdeal.pullback (m:=d) f A) z Ψ hΨ0
    rw [trace_adapted_germ f y z Θ h0 Ψ hΨ0 hcoord F hF (hcomp F hF)]
    apply Ideal.subset_span
    refine ⟨F ∘ f,hcomp F hF,?_,rfl⟩
    apply GermIdeal.mem_pullback_iff.mpr
    have hmem' : A.mem (f z) F:=hpoint.symm ▸ hmem
    exact isInSpanAt_self ⟨F,hmem',rfl⟩ (hcomp F hF)
  · apply Ideal.span_le.mpr
    rintro g ⟨G,hG,hmem,rfl⟩
    obtain ⟨_hGhol,r,s,c,hs,hc,hsum⟩:=GermIdeal.mem_pullback_iff.mp hmem
    choose a ha has using hs
    have haY (i) : A.mem y (a i):=hpoint ▸ ha i
    have haHol (i) : HolomorphicAt (d+t) (a i) y:=GermIdeal.IsCoherent.holomorphicAt_mem hA (haY i)
    have hsHol (i) : HolomorphicAt d (s i) z:=by
      rw [has i]
      exact hcomp (a i) (haHol i)
    have hRing (i) : adaptedGerm z Ψ hΨ0 (s i) (hsHol i)  ∈  
        Ideal.map (planeTrace d t).toRingHom (adaptedIdeal A y Θ h0) := by
      have hSource : adaptedGerm y Θ h0 (a i) (haHol i)  ∈  adaptedIdeal A y Θ h0:=
        Ideal.subset_span ⟨a i,haHol i,haY i,rfl⟩
      have hm:=Ideal.mem_map_of_mem (planeTrace d t).toRingHom hSource
      change planeTrace d t (adaptedGerm y Θ h0 (a i) (haHol i))  ∈  Ideal.map (planeTrace d t).toRingHom (adaptedIdeal A y Θ h0) at hm
      rw [trace_adapted_germ f y z Θ h0 Ψ hΨ0 hcoord (a i) (haHol i) (hcomp (a i) (haHol i))] at hm
      simpa only [has i] using hm
    have hspan : IsInSpanAt (n:=d) (·  ∈  range s) z G:=
      ⟨hG,r,s,c,fun i => ⟨i,rfl⟩,hc,hsum⟩
    have hspan':=(isInSpanAt_comp_adapted_iff z Ψ hΨ0 s G).mp hspan
    have hm:=(isInSpanAt_iff_holGerm_mem_span
      (fun i u => s i ((chartAt (ComplexModel d) z).symm (Ψ.invFun u)))
      (fun i => (holomorphic_adapted_iff z Ψ hΨ0 (s i)).mpr (hsHol i))
      ((holomorphic_adapted_iff z Ψ hΨ0 G).mpr hG)).mp hspan'
    change adaptedGerm z Ψ hΨ0 G hG  ∈  Ideal.span (range fun i => adaptedGerm z Ψ hΨ0 (s i) (hsHol i)) at hm
    exact (Ideal.span_le.mpr (by rintro _ ⟨i,rfl⟩;exact hRing i)) hm

section Native
variable {d t : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]
    {S : Set Y} (hS : ∀ y   ∈   S,RegularAtDim (n:=d+t) S y d)
variable {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

private def actualFlatData (p : S)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) p.val p.val))
    (hsrc : Θ.source ⊆ (chartAt (ComplexModel (d+t)) p.val).target)
    (hflat : ∀ y, y   ∈   (chartAt (ComplexModel (d+t)) p.val).source →
      chartAt (ComplexModel (d+t)) p.val y   ∈   Θ.source →
      (y   ∈   S ↔ Θ.toFun (chartAt (ComplexModel (d+t)) p.val y)   ∈   complexCoordinatePlane (d+t) d)) :
    FlatData (d+t) d Y S where
  amb:=complexChartAt (n:=d+t) p.val
  flat:=Θ.toOpenPartialHomeomorph
  differentiableOn_flat:=Θ.toFun_holomorphic
  differentiableOn_flat_symm:=Θ.invFun_holomorphic
  flat_source_subset:=hsrc
  mem_iff:=hflat
  base:=p.val
  base_mem:=p.property

/-- The given actual ambient flattening itself, rather than another chosen
regularity witness, constructs the matched old native coordinates. -/
theorem exists_matched_coordinates (p : S)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) p.val p.val))
    (hsrc : Θ.source ⊆ (chartAt (ComplexModel (d+t)) p.val).target)
    (h0 : Θ.toFun (chartAt (ComplexModel (d+t)) p.val p.val)=0)
    (hflat : ∀ y, y   ∈   (chartAt (ComplexModel (d+t)) p.val).source →
      chartAt (ComplexModel (d+t)) p.val y   ∈   Θ.source →
      (y   ∈   S ↔ Θ.toFun (chartAt (ComplexModel (d+t)) p.val y)   ∈   complexCoordinatePlane (d+t) d))
    : letI := chartedSpace (Nat.le_add_right d t) hS
      letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
      ∀ (E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ S),
    ∃ (Ψ : LocalHolomorphicEquivAt (chartAt (ComplexModel d) (E.symm p) (E.symm p)))
      (_hΨ0 : Ψ.toFun (chartAt (ComplexModel d) (E.symm p) (E.symm p))=0),
      ∀ᶠ u in 𝓝 (0 : ComplexModel d),
        (E (inverseCoordinates Ψ u)).val=inverseCoordinates Θ (tangentInclusion d t u) := by
  let := chartedSpace (Nat.le_add_right d t) hS
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
  intro E
  let F:=actualFlatData p Θ hsrc hflat
  let e:=F.chart (Nat.le_add_right d t)
  let z:=E.symm p
  have he : e   ∈   maximalAtlas 𝓘(ℂ,ComplexModel d) ∞ S :=
    IsManifold.subset_maximalAtlas (chart_mem_atlas (Nat.le_add_right d t) hS F)
  have hp : p   ∈   e.source:=⟨mem_chart_source _ p.val,Θ.center_mem_source⟩
  have he0 : e p=0 := by
    change coordinateProjection (d+t) d (Θ.toFun (chartAt (ComplexModel (d+t)) p.val p.val))=0
    rw [h0,map_zero]
  have hz : E z   ∈   e.source:=by simpa only [z,E.apply_symm_apply] using hp
  let Ψ:=matchedCoordinates E e he z hz
  have hΨ0 : Ψ.toFun (chartAt (ComplexModel d) z z)=0 := by
    change e (E ((chartAt (ComplexModel d) z).symm (chartAt (ComplexModel d) z z)))=0
    rw [(chartAt (ComplexModel d) z).left_inv (mem_chart_source _ z)]
    exact (congrArg e (E.apply_symm_apply p)).trans he0
  refine ⟨Ψ,hΨ0,?_⟩
  have htarget : (0 : ComplexModel d)   ∈   Ψ.target:=by
    rw [←hΨ0]
    exact Ψ.mapsTo_toFun Ψ.center_mem_source
  filter_upwards [Ψ.isOpen_target.mem_nhds htarget] with u hu
  have hchart : (chartAt (ComplexModel d) z).symm (Ψ.invFun u)=E.symm (e.symm u) :=
    (chartAt (ComplexModel d) z).left_inv hu.2
  change (E ((chartAt (ComplexModel d) z).symm (Ψ.invFun u))).val=_
  rw [hchart,E.apply_symm_apply]
  have huF : u   ∈   F.coordTarget:=hu.1.1
  change (F.invPoint u).val=_
  rw [F.invPoint_val huF]
  change (chartAt (ComplexModel (d+t)) p.val).symm (Θ.invFun (coordinateInclusion (d+t) d u))=_
  rw [inclusion_eq_tangent]
  rfl
/-- ONE internally constructed native chart works for EVERY actual coherent
ambient ideal, including all nonradical whole-ideal structure. -/
theorem exists_matched_coherent_trace (p : S)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) p.val p.val))
    (hsrc : Θ.source ⊆ (chartAt (ComplexModel (d+t)) p.val).target)
    (h0 : Θ.toFun (chartAt (ComplexModel (d+t)) p.val p.val)=0)
    (hflat : ∀ y, y ∈ (chartAt (ComplexModel (d+t)) p.val).source →
      chartAt (ComplexModel (d+t)) p.val y ∈ Θ.source →
      (y ∈ S ↔ Θ.toFun (chartAt (ComplexModel (d+t)) p.val y) ∈ complexCoordinatePlane (d+t) d)) :
    letI := chartedSpace (Nat.le_add_right d t) hS
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
    ∀ (E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ S),
    ∃ (Ψ : LocalHolomorphicEquivAt (chartAt (ComplexModel d) (E.symm p) (E.symm p)))
      (hΨ0 : Ψ.toFun (chartAt (ComplexModel d) (E.symm p) (E.symm p))=0),
      (∀ᶠ u in 𝓝 (0 : ComplexModel d),
        (E (inverseCoordinates Ψ u)).val=inverseCoordinates Θ (tangentInclusion d t u)) ∧
      ∀ (A : GermIdeal (d+t) Y), A.IsCoherent →
        Ideal.map (planeTrace d t).toRingHom (adaptedIdeal A p.val Θ h0)=
          adaptedIdeal (GermIdeal.pullback (m:=d) (fun z : Z => (E z).val) A) (E.symm p) Ψ hΨ0 := by
  let := chartedSpace (Nat.le_add_right d t) hS
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
  intro E
  obtain ⟨Ψ,hΨ0,hcoord⟩:=exists_matched_coordinates hS p Θ hsrc h0 hflat E
  have hf : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞
      (fun z : Z => (E z).val):=(contMDiff_val (Nat.le_add_right d t) hS).comp E.contMDiff
  have hpoint : (E (E.symm p)).val=p.val:=congrArg Subtype.val (E.apply_symm_apply p)
  refine ⟨Ψ,hΨ0,hcoord,fun A hA => ?_⟩
  exact whole_trace_of_inverse (fun z : Z => (E z).val) hf p.val (E.symm p) hpoint Θ h0 Ψ hΨ0 hcoord A hA

end Native
end
end Hironaka.HironakaDisjointMatchedControlledTrace
