/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPlaneContactBlowupRestriction
import Hironaka.Resolution.HironakaActualSubmanifoldGermExtension

/-!
# Actual blowups restricted to arbitrary closed regular native contacts

Whole genuine germ extension replaces a supplied global holomorphic retraction.
The literal closed inclusion gives actual properness of the universal lift;
two actual universal comparisons give the full native restricted blowup.
All strict closures here are centre-relative geoStrictTransform closures.
-/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualClosedContactBlowupRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothSubmersionOrderedChoiceImageTrace BlowupStrictSubmanifold
  SubmanifoldChartedSpace
variable {n k : ℕ} {A Y : Type} [TopologicalSpace A] [ChartedSpace (ComplexModel n) A]
  [IsComplexManifold n A] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {N : Set A} (hk : k≤n) (hNc : IsClosed N)
  (hN : ∀ x∈N,RegularAtDim (n := n) N x k) {D : Set N} {π : Y → A}

include hk hNc hN

omit hNc in
/-- Genuine native germ extension supplies the ENTIRE independently defined original centre ideal. -/
theorem centre_pullback (D : Set N) :
    letI := chartedSpace hk hN
    GermIdeal.pullback (m := k) (Subtype.val : N → A)
      (vanishingIdeal (n := n) ((Subtype.val : N → A) '' D))=vanishingIdeal (n := k) D :=
  HironakaActualSubmanifoldGermExtension.pullback_vanishing_image hk hN D

omit hk in
private theorem strict_regular (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π)
    (y : Y) (hy : y∈geoStrictTransform π ((Subtype.val : N → A) '' D) N) :
    RegularAtDim (n := n) (geoStrictTransform π ((Subtype.val : N → A) '' D) N) y k :=
  regularAtDim_geoStrictTransform hπ hNc hN (fun _ ⟨x,_hx,he⟩ => he ▸ x.property) hy

/-- The SAME actual strict contact has the internally constructed original flattening atlas. -/
@[instance_reducible] def strictChartedSpace
    (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π) :
    ChartedSpace (ComplexModel k) (geoStrictTransform π ((Subtype.val : N → A) '' D) N) :=
  chartedSpace hk (strict_regular hNc hN hπ)

theorem strict_isComplexManifold (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π) :
    letI := strictChartedSpace hk hNc hN hπ
    IsComplexManifold k (geoStrictTransform π ((Subtype.val : N → A) '' D) N) :=
  isComplexManifold_chartedSpace hk (strict_regular hNc hN hπ)

omit hk hN in
/-- The LITERAL restricted map to the true native contact, before any comparison isomorphism. -/
def restrictedProjection (D : Set N) (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π) :
    geoStrictTransform π ((Subtype.val : N → A) '' D) N → N :=
  fun y => ⟨π y.val,geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNc y.property⟩

omit hk hN in
omit [IsComplexManifold n A] [IsComplexManifold n Y] in
/-- The actual base square is an exact identity of the literal functions. -/
theorem restrictedProjection_factor (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π) :
    π∘(Subtype.val : geoStrictTransform π ((Subtype.val : N → A) '' D) N → Y)=
      (Subtype.val : N → A)∘restrictedProjection hNc D hπ := rfl

/-- Actual native corestriction proves holomorphy for the SAME intrinsic contact projection. -/
theorem restrictedProjection_contMDiff (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π) :
    letI := chartedSpace hk hN
    letI := strictChartedSpace hk hNc hN hπ
    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ (restrictedProjection hNc D hπ) := by
  let := chartedSpace hk hN
  let := strictChartedSpace hk hNc hN hπ
  have := strict_isComplexManifold hk hNc hN hπ
  have hval := contMDiff_val hk (strict_regular hNc hN hπ)
  exact SubmanifoldCodRestrict.contMDiff_codRestrict hk hN (hπ.contMDiff.comp hval)
    (fun y => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNc y.property)

omit hNc in
omit [IsComplexManifold n Y] in
/-- The actual whole matched centre ideal supplies the UNIQUE genuine universal ambient lift. -/
theorem exists_unique_lift {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
    [IsComplexManifold k Z] {ρ : Z → N}
    (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π) :
    letI := chartedSpace hk hN
    IsBlowupAlong k D ρ → ∃! κ : Z → Y,
      ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ κ ∧
      π∘κ=(Subtype.val : N → A)∘ρ := by
  let := chartedSpace hk hN
  have := isComplexManifold_chartedSpace hk hN
  intro hρ
  have hj := contMDiff_val hk hN
  have hi : (GermIdeal.pullback (m := k) ((Subtype.val : N → A)∘ρ)
      (vanishingIdeal (n := n) ((Subtype.val : N → A) '' D))).IsInvertible := by
    rw [whole_pullback_comp hj hρ.contMDiff (vanishingIdeal (n := n) ((Subtype.val : N → A) '' D))
      (fun _ _ h => h.1),centre_pullback hk hN D]
    exact hρ.2.2.2.1
  exact hπ.2.2.2.2 k Z ((Subtype.val : N → A)∘ρ) (hj.comp hρ.contMDiff) hi

/-- Actual CLOSED inclusion properness replaces a supplied global retraction and proves the ENTIRE strict range. -/
theorem lift_proper_and_range {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
    [IsComplexManifold k Z] {ρ : Z → N}
    (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π) (κ : Z → Y)
    (hκ : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ κ)
    (hcomm : π∘κ=(Subtype.val : N → A)∘ρ) :
    letI := chartedSpace hk hN
    IsBlowupAlong k D ρ → IsProperMap κ ∧
      range κ=geoStrictTransform π ((Subtype.val : N → A) '' D) N := by
  let := chartedSpace hk hN
  have := isComplexManifold_chartedSpace hk hN
  intro hρ
  have hcomm' (z : Z) : π (κ z)=(ρ z).val := congrFun hcomm z
  have hproper : IsProperMap κ := by
    apply isProperMap_of_comp_of_t2 hκ.continuous hπ.contMDiff.continuous
    rw [hcomm]
    exact hNc.isClosedEmbedding_subtypeVal.isProperMap.comp
      (HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hρ)
  refine ⟨hproper,?_⟩
  let S := geoStrictTransform π ((Subtype.val : N → A) '' D) N
  have hclosed : IsClosed (range κ) := by
    rw [← image_univ]
    exact hproper.isClosedMap _ isClosed_univ
  apply le_antisymm
  · have hdense : closure (ρ ⁻¹' D)ᶜ=univ := by
      rw [closure_compl,ExceptionalFibres.interior_preimage_eq_empty hρ,compl_empty]
    have hpre : (ρ ⁻¹' D)ᶜ ⊆ κ ⁻¹' S := by
      intro z hz
      apply subset_closure
      change π (κ z)∈N ∧ π (κ z)∉(Subtype.val : N → A) '' D
      rw [hcomm']
      refine ⟨(ρ z).property,?_⟩
      rintro ⟨x,hx,he⟩
      have hxe : x=ρ z := Subtype.ext he
      exact hz (show ρ z∈D from hxe ▸ hx)
    have hall : univ ⊆ κ ⁻¹' S := by
      rw [← hdense]
      exact closure_minimal hpre (isClosed_closure.preimage hκ.continuous)
    rintro _ ⟨z,rfl⟩
    exact hall (mem_univ z)
  · apply closure_minimal ?_ hclosed
    intro y hy
    obtain ⟨z,hz⟩ := HironakaLocalPrincipalization.surjective_of_isBlowupAlong hρ ⟨π y,hy.1⟩
    have he : π (κ z)=π y := by
      rw [hcomm']
      exact congrArg Subtype.val hz
    have hkc : π (κ z)∉(Subtype.val : N → A) '' D := by rw [he];exact hy.2
    have hi := (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ).1.2.1
    exact ⟨z,hi hkc hy.2 he⟩

/-- Actual exceptional invertibility ALONG this strict contact gives the WHOLE intrinsic centre invertibility. -/
theorem restrictedProjection_invertible (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π) :
    letI := chartedSpace hk hN
    letI := strictChartedSpace hk hNc hN hπ
    letI := strict_isComplexManifold hk hNc hN hπ
    (GermIdeal.pullback (m := k) (restrictedProjection hNc D hπ) (vanishingIdeal (n := k) D)).IsInvertible := by
  let := chartedSpace hk hN
  have := isComplexManifold_chartedSpace hk hN
  let := strictChartedSpace hk hNc hN hπ
  have := strict_isComplexManifold hk hNc hN hπ
  let S := geoStrictTransform π ((Subtype.val : N → A) '' D) N
  let C := (Subtype.val : N → A) '' D
  have hval := contMDiff_val hk (strict_regular hNc hN hπ)
  have halong : RestrictedIdealQuotient.IsInvertibleAlong n S
      (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) := by
    have h := MarkedIdeals.MarkedIdeal.isInvertibleAlong_geoStrictTransform hπ N 1
    change RestrictedIdealQuotient.IsInvertibleAlong n S
      (IdealWeightPowers.idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal 1) at h
    rw [BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ] at h
    exact h
  have hres := SubmanifoldIdealRestriction.isInvertible_restrictIdeal hval halong
  change (GermIdeal.pullback (m := k) (Subtype.val : S → Y)
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C))).IsInvertible at hres
  rw [← whole_pullback_comp hπ.contMDiff hval (vanishingIdeal (n := n) C) (fun _ _ h => h.1)] at hres
  rw [restrictedProjection_factor hNc hπ,
    whole_pullback_comp (contMDiff_val hk hN) (restrictedProjection_contMDiff hk hNc hN hπ)
      (vanishingIdeal (n := n) C) (fun _ _ h => h.1),centre_pullback hk hN D] at hres
  exact hres

/-- TWO actual universal properties construct genuine inverse native maps over the SAME original contact. -/
theorem exists_strictContact_diffeomorph {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] {ρ : Z → N}
    (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π) :
    letI := chartedSpace hk hN
    letI := strictChartedSpace hk hNc hN hπ
    letI := strict_isComplexManifold hk hNc hN hπ
    IsBlowupAlong k D ρ →
      ∃ E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
          geoStrictTransform π ((Subtype.val : N → A) '' D) N,
        restrictedProjection hNc D hπ∘E=ρ := by
  let := chartedSpace hk hN
  have := isComplexManifold_chartedSpace hk hN
  let := strictChartedSpace hk hNc hN hπ
  have := strict_isComplexManifold hk hNc hN hπ
  intro hρ
  let S := geoStrictTransform π ((Subtype.val : N → A) '' D) N
  let σ := restrictedProjection hNc D hπ
  have hσ := restrictedProjection_contMDiff hk hNc hN hπ
  have hinv := restrictedProjection_invertible hk hNc hN hπ
  obtain ⟨κ,⟨hκ,hcomm⟩,_hunique⟩ := exists_unique_lift hk hN hπ hρ
  obtain ⟨_hproper,hrange⟩ := lift_proper_and_range hk hNc hN hπ κ hκ hcomm hρ
  have hκS : ∀ z,κ z∈S := by
    intro z
    change κ z∈geoStrictTransform π ((Subtype.val : N → A) '' D) N
    rw [← hrange]
    exact ⟨z,rfl⟩
  let α : Z → S := fun z => ⟨κ z,hκS z⟩
  have hα : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ α :=
    SubmanifoldCodRestrict.contMDiff_codRestrict hk (strict_regular hNc hN hπ) hκ hκS
  have hσα : σ∘α=ρ := by
    funext z
    apply Subtype.ext
    exact congrFun hcomm z
  obtain ⟨β,⟨hβ,hρβ⟩,_hβunique⟩ := hρ.2.2.2.2 k S σ hσ hinv
  have hβα : β∘α=id := by
    apply BlowupUniqueness.eq_id_of_comp_eq hρ (hβ.comp hα)
    calc
      ρ∘(β∘α)=(ρ∘β)∘α := rfl
      _=σ∘α := congrArg (fun f => f∘α) hρβ
      _=ρ := hσα
  have hval := contMDiff_val hk (strict_regular hNc hN hπ)
  have hgInv : (GermIdeal.pullback (m := k) (π∘(Subtype.val : S → Y))
      (vanishingIdeal (n := n) ((Subtype.val : N → A) '' D))).IsInvertible := by
    rw [restrictedProjection_factor hNc hπ,
      whole_pullback_comp (contMDiff_val hk hN) hσ
        (vanishingIdeal (n := n) ((Subtype.val : N → A) '' D)) (fun _ _ h => h.1),centre_pullback hk hN D]
    exact hinv
  obtain ⟨k₀,_hk₀,huniq⟩ := hπ.2.2.2.2 k S (π∘(Subtype.val : S → Y))
    (hπ.contMDiff.comp hval) hgInv
  have hκβ : κ∘β=(Subtype.val : S → Y) := by
    have hπκβ : π∘(κ∘β)=π∘(Subtype.val : S → Y) := by
      calc
        π∘(κ∘β)=(π∘κ)∘β := rfl
        _=((Subtype.val : N → A)∘ρ)∘β := congrArg (fun f => f∘β) hcomm
        _=(Subtype.val : N → A)∘(ρ∘β) := rfl
        _=(Subtype.val : N → A)∘σ := congrArg (fun f => (Subtype.val : N → A)∘f) hρβ
        _=π∘(Subtype.val : S → Y) := (restrictedProjection_factor hNc hπ).symm
    exact (huniq (κ∘β) ⟨hκ.comp hβ,hπκβ⟩).trans
      (huniq (Subtype.val : S → Y) ⟨hval,rfl⟩).symm
  have hαβ : α∘β=id := by
    funext z
    apply Subtype.ext
    exact congrFun hκβ z
  let E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ S :=
    { toFun := α
      invFun := β
      left_inv := congrFun hβα
      right_inv := congrFun hαβ
      contMDiff_toFun := hα
      contMDiff_invFun := hβ }
  exact ⟨E,hσα⟩

/-- ORIGINAL closed regular contact and original smooth centre data produce the FULL restricted blowup. -/
theorem restrictedProjection_isBlowupAlong (D : Set N)
    (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π) :
    letI := chartedSpace hk hN
    letI := strictChartedSpace hk hNc hN hπ
    letI := strict_isComplexManifold hk hNc hN hπ
    IsClosedSubmanifold k D → interior D=∅ → IsBlowupAlong k D (restrictedProjection hNc D hπ) := by
  let := chartedSpace hk hN
  have := isComplexManifold_chartedSpace hk hN
  let := strictChartedSpace hk hNc hN hπ
  have := strict_isComplexManifold hk hNc hN hπ
  intro hD hDint
  let S := geoStrictTransform π ((Subtype.val : N → A) '' D) N
  let σ := restrictedProjection hNc D hπ
  obtain ⟨Z,tZ,cZ,mZ,ρ,hρ⟩ := BlowupExistence.exists_isBlowupAlong D hD hDint
  obtain ⟨E,hE⟩ := exists_strictContact_diffeomorph hk hNc hN hπ hρ
  have hρinv : ρ∘E.symm=σ := by
    funext z
    have he := congrFun hE (E.symm z)
    simpa only [Function.comp_apply,E.apply_symm_apply] using he.symm
  refine ⟨hD,hDint,restrictedProjection_contMDiff hk hNc hN hπ,
    restrictedProjection_invertible hk hNc hN hπ,?_⟩
  intro m T _tT _cT _mT g hg hginv
  obtain ⟨h,⟨hh,hρh⟩,hunique⟩ := hρ.2.2.2.2 m T g hg hginv
  refine ⟨E∘h,⟨E.contMDiff.comp hh,?_⟩,?_⟩
  · calc
      σ∘(E∘h)=(σ∘E)∘h := rfl
      _=ρ∘h := congrArg (fun f => f∘h) hE
      _=g := hρh
  · intro h' hh'
    have hcomp : ρ∘(E.symm∘h')=g := by
      calc
        ρ∘(E.symm∘h')=(ρ∘E.symm)∘h' := rfl
        _=σ∘h' := congrArg (fun f => f∘h') hρinv
        _=g := hh'.2
    have he := hunique (E.symm∘h') ⟨E.symm.contMDiff.comp hh'.1,hcomp⟩
    funext t
    have hc := congrArg E (congrFun he t)
    simpa only [Function.comp_apply,E.apply_symm_apply] using hc

omit hk hN in
omit [IsComplexManifold n A] [IsComplexManifold n Y] in
/-- EVERY singular subset retains its ENTIRE centre-relative strict closure through the SAME literal inclusion. -/
theorem strictTransform_image (hπ : IsBlowupAlong n ((Subtype.val : N → A) '' D) π) (W : Set N) :
    (Subtype.val : geoStrictTransform π ((Subtype.val : N → A) '' D) N → Y) ''
      geoStrictTransform (restrictedProjection hNc D hπ) D W=
        geoStrictTransform π ((Subtype.val : N → A) '' D) ((Subtype.val : N → A) '' W) := by
  let S := geoStrictTransform π ((Subtype.val : N → A) '' D) N
  let σ := restrictedProjection hNc D hπ
  let j : S → Y := Subtype.val
  have himage : j '' (σ ⁻¹' (W\D))=π ⁻¹' (((Subtype.val : N → A) '' W)\((Subtype.val : N → A) '' D)) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change π z.val∈(Subtype.val : N → A) '' W ∧ π z.val∉(Subtype.val : N → A) '' D
      refine ⟨⟨σ z,hz.1,rfl⟩,?_⟩
      rintro ⟨x,hxD,he⟩
      have hxe : x=σ z := Subtype.ext he
      exact hz.2 (hxe ▸ hxD)
    · rintro ⟨⟨x,hxW,he⟩,hyD⟩
      have hyS : y∈S := subset_closure ⟨he ▸ x.property,hyD⟩
      refine ⟨⟨y,hyS⟩,?_,rfl⟩
      have hσ : σ ⟨y,hyS⟩=x := Subtype.ext he.symm
      change σ ⟨y,hyS⟩∈W ∧ σ ⟨y,hyS⟩∉D
      rw [hσ]
      exact ⟨hxW,fun hxD => hyD ⟨x,hxD,he⟩⟩
  change j '' closure (σ ⁻¹' (W\D))=
    closure (π ⁻¹' (((Subtype.val : N → A) '' W)\((Subtype.val : N → A) '' D)))
  calc
    j '' closure (σ ⁻¹' (W\D))=closure (j '' (σ ⁻¹' (W\D))) :=
      ((isClosed_closure : IsClosed S).isClosedEmbedding_subtypeVal.closure_image_eq _).symm
    _=_ := congrArg closure himage

end
end Hironaka.HironakaActualClosedContactBlowupRestriction
