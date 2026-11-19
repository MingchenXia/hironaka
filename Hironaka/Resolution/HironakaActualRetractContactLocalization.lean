/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPlaneContactBlowupRestriction
import Hironaka.Resolution.HironakaActualAnalyticSubspaceRegularityConverse
import Hironaka.Resolution.HironakaActualLocalCommonGraphModel

/-!
# Whole original centre ideals and blowups under actual split holomorphic contacts

Actual holomorphic section/retraction geometry preserves the true manifold
open domains. Whole independently defined centre ideals are produced, with
no holomorphic extension or output ideal/restricted-blowup certificate.
-/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualRetractContactLocalization
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan HironakaSmoothSubmersionOrderedChoiceImageTrace
  BlowupStrictSubmanifold SubmanifoldChartedSpace
variable {d : ℕ} {X A : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [IsComplexManifold d X] [TopologicalSpace A] [ChartedSpace (ComplexModel (d+1)) A]
  [IsComplexManifold (d+1) A]

private theorem mem_vanishing_of_span {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (W : Set M) {x : M} {F : M → ℂ}
    (hF : IsInSpanAt (n := n) ((vanishingIdeal (n := n) W).mem x) x F) :
    (vanishingIdeal (n := n) W).mem x F := by
  obtain ⟨hhol,N,s,a,hs,_ha,he⟩ := hF
  refine ⟨hhol,?_⟩
  have hall : ∀ᶠ y in nhds x,∀ i : Fin N,y∈W→s i y=0 := eventually_all.mpr fun i => (hs i).2
  filter_upwards [he,hall] with y hy hys hyW
  rw [hy]
  exact Finset.sum_eq_zero fun i _ => by rw [hys i hyW,mul_zero]

/-- Genuine split holomorphic geometry proves equality of the ENTIRE independent original centre ideals. -/
theorem section_centre_pullback (s : X → A) (p : A → X)
    (hs : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ s)
    (hp : ContMDiff 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel d) ∞ p)
    (hps : p∘s=id) (D : Set X) :
    GermIdeal.pullback (m := d) s (vanishingIdeal (n := d+1) (s '' D))=vanishingIdeal (n := d) D := by
  apply GermIdeal.ext
  funext x F
  apply propext
  constructor
  · intro hF
    change IsInSpanAt (n := d) (fun b => ∃ a,
      (vanishingIdeal (n := d+1) (s '' D)).mem (s x) a ∧ b=a∘s) x F at hF
    apply mem_vanishing_of_span D
    apply IsInSpanAt.mono ?_ hF
    rintro _ ⟨a,ha,rfl⟩
    refine ⟨ha.1.comp_contMDiff (Eventually.of_forall fun _ => hs.contMDiffAt),?_⟩
    filter_upwards [hs.continuous.continuousAt.eventually ha.2] with y hy hyD
    exact hy ⟨y,hyD,rfl⟩
  · intro hF
    let a : A → ℂ := F∘p
    have hpx : p (s x)=x := congrFun hps x
    have ha : (vanishingIdeal (n := d+1) (s '' D)).mem (s x) a := by
      refine ⟨?_,?_⟩
      · have hh : HolomorphicAt d F (p (s x)) := hpx.symm ▸ hF.1
        exact hh.comp_contMDiff (Eventually.of_forall fun _ => hp.contMDiffAt)
      · have ht : Tendsto p (nhds (s x)) (nhds x) := by
          have ht := hp.continuous.tendsto (s x)
          rw [hpx] at ht
          exact ht
        filter_upwards [ht.eventually hF.2] with z hz hzC
        obtain ⟨y,hyD,rfl⟩ := hzC
        have hpy : p (s y)=y := congrFun hps y
        exact hz (hpy.symm ▸ hyD)
    have he : F=a∘s := by
      funext y
      change F y=F (p (s y))
      have hpy : p (s y)=y := congrFun hps y
      rw [hpy]
    change IsInSpanAt (n := d) (fun b => ∃ a,
      (vanishingIdeal (n := d+1) (s '' D)).mem (s x) a ∧ b=a∘s) x F
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨a,ha,he⟩ hF.1

omit [TopologicalSpace X] [TopologicalSpace A] in
/-- The actual centre image is the SAME whole subset inside the closed contact range. -/
theorem image_centre_eq (s : X → A) (p : A → X) (hps : p∘s=id) (D : Set X) :
    s '' D=range s ∩ p ⁻¹' D := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨⟨x,rfl⟩,?_⟩
    change p (s x)∈D
    have hpx : p (s x)=x := congrFun hps x
    rwa [hpx]
  · rintro ⟨⟨x,rfl⟩,hx⟩
    have hpx : p (s x)=x := congrFun hps x
    change p (s x)∈D at hx
    exact ⟨x,hpx ▸ hx,rfl⟩

omit [IsComplexManifold d X] in
/-- A true split holomorphic section has ACTUAL closed range; no closed-embedding certificate is assumed. -/
theorem range_section_closed (s : X → A) (p : A → X)
    (hs : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ s)
    (hp : ContMDiff 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel d) ∞ p)
    (hps : p∘s=id) : IsClosed (range s) := by
  have he : range s={a | s (p a)=a} := by
    ext a
    constructor
    · rintro ⟨x,rfl⟩
      change s (p (s x))=s x
      have hpx : p (s x)=x := congrFun hps x
      rw [hpx]
    · exact fun h => ⟨p a,h⟩
  rw [he]
  exact isClosed_eq (hs.continuous.comp hp.continuous) continuous_id

section Restriction
variable (s : X → A) (p : A → X)
  (hs : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ s)
  (hp : ContMDiff 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel d) ∞ p)
  (hps : p∘s=id)
  {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+1)) Y]
  [IsComplexManifold (d+1) Y] {D : Set X} {π : Y → A}

include hps in
omit [TopologicalSpace X] [TopologicalSpace A] in
private theorem section_projection {a : A} (ha : a∈range s) : s (p a)=a := by
  obtain ⟨x,rfl⟩ := ha
  have he : p (s x)=x := congrFun hps x
  rw [he]

include hs hp hps

omit [IsComplexManifold (d+1) Y] in
private theorem exists_unique_lift {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z] {ρ : Z → X}
    (hπ : IsBlowupAlong (d+1) (s '' D) π) (hρ : IsBlowupAlong d D ρ) :
    ∃! κ : Z → Y,ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ κ ∧
      π∘κ=s∘ρ := by
  have hi : (GermIdeal.pullback (m := d) (s∘ρ)
      (vanishingIdeal (n := d+1) (s '' D))).IsInvertible := by
    rw [whole_pullback_comp hs hρ.contMDiff (vanishingIdeal (n := d+1) (s '' D))
      (fun _ _ h => h.1),section_centre_pullback s p hs hp hps D]
    exact hρ.2.2.2.1
  exact hπ.2.2.2.2 d Z (s∘ρ) (hs.comp hρ.contMDiff) hi

omit hs in
private theorem lift_proper_and_range {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z] {ρ : Z → X}
    (hπ : IsBlowupAlong (d+1) (s '' D) π) (hρ : IsBlowupAlong d D ρ)
    (κ : Z → Y) (hκ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ κ)
    (hcomm : π∘κ=s∘ρ) :
    IsProperMap κ ∧ range κ=geoStrictTransform π (s '' D) (range s) := by
  have hcomm' (z : Z) : π (κ z)=s (ρ z) := congrFun hcomm z
  have hproper : IsProperMap κ := by
    apply isProperMap_of_comp_of_t2 hκ.continuous (hp.continuous.comp hπ.contMDiff.continuous)
    have he : (p∘π)∘κ=ρ := by
      funext z
      change p (π (κ z))=ρ z
      rw [hcomm']
      exact congrFun hps (ρ z)
    rw [he]
    exact HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hρ
  refine ⟨hproper,?_⟩
  let S := geoStrictTransform π (s '' D) (range s)
  have hclosed : IsClosed (range κ) := by
    rw [← image_univ]
    exact hproper.isClosedMap _ isClosed_univ
  apply le_antisymm
  · have hdense : closure (ρ ⁻¹' D)ᶜ=univ := by
      rw [closure_compl,ExceptionalFibres.interior_preimage_eq_empty hρ,compl_empty]
    have hpre : (ρ ⁻¹' D)ᶜ ⊆ κ ⁻¹' S := by
      intro z hz
      apply subset_closure
      change π (κ z)∈range s ∧ π (κ z)∉s '' D
      rw [hcomm']
      refine ⟨⟨ρ z,rfl⟩,?_⟩
      rintro ⟨x,hx,he⟩
      have hxe : x=ρ z := by
        have ht := congrArg p he
        have hx' : p (s x)=x := congrFun hps x
        have hz' : p (s (ρ z))=ρ z := congrFun hps (ρ z)
        simpa only [hx',hz'] using ht
      exact hz (show ρ z∈D from hxe ▸ hx)
    have hall : univ ⊆ κ ⁻¹' S := by
      rw [← hdense]
      exact closure_minimal hpre (isClosed_closure.preimage hκ.continuous)
    rintro _ ⟨z,rfl⟩
    exact hall (mem_univ z)
  · apply closure_minimal ?_ hclosed
    intro y hy
    obtain ⟨z,hz⟩ := HironakaLocalPrincipalization.surjective_of_isBlowupAlong hρ (p (π y))
    have he : π (κ z)=π y := by
      rw [hcomm',hz]
      exact section_projection s p hps hy.1
    have hkc : π (κ z)∉s '' D := by rw [he];exact hy.2
    have hi := (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ).1.2.1
    exact ⟨z,hi hkc hy.2 he⟩

variable (hN : ∀ a∈range s,RegularAtDim (n := d+1) (range s) a d)

include hN

omit [IsComplexManifold d X] in
private theorem strict_regular (hπ : IsBlowupAlong (d+1) (s '' D) π)
    (z : Y) (hz : z∈geoStrictTransform π (s '' D) (range s)) :
    RegularAtDim (n := d+1) (geoStrictTransform π (s '' D) (range s)) z d :=
  regularAtDim_geoStrictTransform hπ (range_section_closed s p hs hp hps) hN
    (fun _ ⟨x,_hx,he⟩ => ⟨x,he⟩) hz

/-- The true strict contact transform has its internally constructed intrinsic manifold atlas. -/
@[instance_reducible] def strictChartedSpace (hπ : IsBlowupAlong (d+1) (s '' D) π) :
    ChartedSpace (ComplexModel d) (geoStrictTransform π (s '' D) (range s)) :=
  chartedSpace (Nat.le_succ d) (strict_regular s p hs hp hps hN hπ)

omit [IsComplexManifold d X] in
theorem strict_isComplexManifold (hπ : IsBlowupAlong (d+1) (s '' D) π) :
    letI := strictChartedSpace s p hs hp hps hN hπ
    IsComplexManifold d (geoStrictTransform π (s '' D) (range s)) :=
  isComplexManifold_chartedSpace (Nat.le_succ d) (strict_regular s p hs hp hps hN hπ)

omit hs hp hps hN in
/-- The literal projection on the actual contact strict transform, prior to comparisons. -/
def restrictedProjection (s : X → A) (p : A → X) (π : Y → A) (D : Set X) :
    geoStrictTransform π (s '' D) (range s) → X := fun z => p (π z.val)

omit [IsComplexManifold d X] in
private theorem restrictedProjection_holo (hπ : IsBlowupAlong (d+1) (s '' D) π) :
    letI := strictChartedSpace s p hs hp hps hN hπ
    ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel d) ∞ (restrictedProjection s p π D) := by
  let := strictChartedSpace s p hs hp hps hN hπ
  exact hp.comp (hπ.contMDiff.comp (contMDiff_val (Nat.le_succ d) (strict_regular s p hs hp hps hN hπ)))

omit hN in
omit [IsComplexManifold d X] [IsComplexManifold (d+1) Y] in
private theorem restricted_factor (hπ : IsBlowupAlong (d+1) (s '' D) π) :
    π∘(Subtype.val : geoStrictTransform π (s '' D) (range s) → Y)=
      s∘restrictedProjection s p π D := by
  funext z
  exact (section_projection s p hps (geoStrictTransform_subset_preimage hπ.contMDiff.continuous
    (range_section_closed s p hs hp hps) z.property)).symm

private theorem restricted_invertible (hπ : IsBlowupAlong (d+1) (s '' D) π) :
    letI := strictChartedSpace s p hs hp hps hN hπ
    letI := strict_isComplexManifold s p hs hp hps hN hπ
    (GermIdeal.pullback (m := d) (restrictedProjection s p π D) (vanishingIdeal (n := d) D)).IsInvertible := by
  let := strictChartedSpace s p hs hp hps hN hπ
  have := strict_isComplexManifold s p hs hp hps hN hπ
  let S := geoStrictTransform π (s '' D) (range s)
  have hval := contMDiff_val (Nat.le_succ d) (strict_regular s p hs hp hps hN hπ)
  have halong : RestrictedIdealQuotient.IsInvertibleAlong (d+1) S
      (GermIdeal.pullback (m := d+1) π (vanishingIdeal (n := d+1) (s '' D))) := by
    have h := MarkedIdeals.MarkedIdeal.isInvertibleAlong_geoStrictTransform hπ (range s) 1
    change RestrictedIdealQuotient.IsInvertibleAlong (d+1) S
      (IdealWeightPowers.idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal 1) at h
    rw [BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ] at h
    exact h
  have hres := SubmanifoldIdealRestriction.isInvertible_restrictIdeal hval halong
  change (GermIdeal.pullback (m := d) (Subtype.val : S → Y)
    (GermIdeal.pullback (m := d+1) π (vanishingIdeal (n := d+1) (s '' D)))).IsInvertible at hres
  rw [← whole_pullback_comp hπ.contMDiff hval (vanishingIdeal (n := d+1) (s '' D))
    (fun _ _ h => h.1)] at hres
  rw [restricted_factor s p hs hp hps hπ,
    whole_pullback_comp hs (restrictedProjection_holo s p hs hp hps hN hπ)
      (vanishingIdeal (n := d+1) (s '' D)) (fun _ _ h => h.1),section_centre_pullback s p hs hp hps D] at hres
  exact hres

private theorem exists_diffeomorph {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z] {ρ : Z → X}
    (hπ : IsBlowupAlong (d+1) (s '' D) π) (hρ : IsBlowupAlong d D ρ) :
    letI := strictChartedSpace s p hs hp hps hN hπ
    letI := strict_isComplexManifold s p hs hp hps hN hπ
    ∃ E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
        geoStrictTransform π (s '' D) (range s),restrictedProjection s p π D∘E=ρ := by
  let := strictChartedSpace s p hs hp hps hN hπ
  have := strict_isComplexManifold s p hs hp hps hN hπ
  let S := geoStrictTransform π (s '' D) (range s)
  let σ := restrictedProjection s p π D
  have hσ := restrictedProjection_holo s p hs hp hps hN hπ
  have hinv := restricted_invertible s p hs hp hps hN hπ
  obtain ⟨κ,⟨hκ,hcomm⟩,_hunique⟩ := exists_unique_lift s p hs hp hps hπ hρ
  obtain ⟨_hproper,hrange⟩ := lift_proper_and_range s p hp hps hπ hρ κ hκ hcomm
  have hκS : ∀ z,κ z∈S := by
    intro z
    change κ z∈geoStrictTransform π (s '' D) (range s)
    rw [← hrange]
    exact ⟨z,rfl⟩
  let α : Z → S := fun z => ⟨κ z,hκS z⟩
  have hα : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel d) ∞ α :=
    SubmanifoldCodRestrict.contMDiff_codRestrict (Nat.le_succ d)
      (strict_regular s p hs hp hps hN hπ) hκ hκS
  have hσα : σ∘α=ρ := by
    funext z
    change p (π (κ z))=ρ z
    have he : π (κ z)=s (ρ z) := congrFun hcomm z
    rw [he]
    exact congrFun hps (ρ z)
  obtain ⟨β,⟨hβ,hρβ⟩,_hβunique⟩ := hρ.2.2.2.2 d S σ hσ hinv
  have hβα : β∘α=id := by
    apply BlowupUniqueness.eq_id_of_comp_eq hρ (hβ.comp hα)
    calc
      ρ∘(β∘α)=(ρ∘β)∘α := rfl
      _=σ∘α := congrArg (fun a => a∘α) hρβ
      _=ρ := hσα
  have hval := contMDiff_val (Nat.le_succ d) (strict_regular s p hs hp hps hN hπ)
  have hgInv : (GermIdeal.pullback (m := d) (π∘(Subtype.val : S → Y))
      (vanishingIdeal (n := d+1) (s '' D))).IsInvertible := by
    rw [restricted_factor s p hs hp hps hπ,
      whole_pullback_comp hs hσ (vanishingIdeal (n := d+1) (s '' D))
        (fun _ _ h => h.1),section_centre_pullback s p hs hp hps D]
    exact hinv
  obtain ⟨k₀,_hk₀,huniq⟩ := hπ.2.2.2.2 d S (π∘(Subtype.val : S → Y))
    (hπ.contMDiff.comp hval) hgInv
  have hκβ : κ∘β=(Subtype.val : S → Y) := by
    have hπκβ : π∘(κ∘β)=π∘(Subtype.val : S → Y) := by
      calc
        π∘(κ∘β)=(π∘κ)∘β := rfl
        _=(s∘ρ)∘β := congrArg (fun a => a∘β) hcomm
        _=s∘(ρ∘β) := rfl
        _=s∘σ := congrArg (fun a => s∘a) hρβ
        _=π∘(Subtype.val : S → Y) := (restricted_factor s p hs hp hps hπ).symm
    exact (huniq (κ∘β) ⟨hκ.comp hβ,hπκβ⟩).trans
      (huniq (Subtype.val : S → Y) ⟨hval,rfl⟩).symm
  have hαβ : α∘β=id := by
    funext z
    apply Subtype.ext
    exact congrFun hκβ z
  let E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ S :=
    { toFun := α
      invFun := β
      left_inv := congrFun hβα
      right_inv := congrFun hαβ
      contMDiff_toFun := hα
      contMDiff_invFun := hβ }
  exact ⟨E,hσα⟩

/-- Ordinary split contact geometry produces the FULL universal property of the SAME intrinsic restricted map. -/
theorem restrictedProjection_isBlowupAlong (D : Set X)
    (hD : IsClosedSubmanifold d D) (hDint : interior D=∅)
    (hπ : IsBlowupAlong (d+1) (s '' D) π) :
    letI := strictChartedSpace s p hs hp hps hN hπ
    letI := strict_isComplexManifold s p hs hp hps hN hπ
    IsBlowupAlong d D (restrictedProjection s p π D) := by
  let := strictChartedSpace s p hs hp hps hN hπ
  have := strict_isComplexManifold s p hs hp hps hN hπ
  let S := geoStrictTransform π (s '' D) (range s)
  let σ := restrictedProjection s p π D
  obtain ⟨Z,tZ,cZ,mZ,ρ,hρ⟩ := BlowupExistence.exists_isBlowupAlong D hD hDint
  obtain ⟨E,hE⟩ := exists_diffeomorph s p hs hp hps hN hπ hρ
  have hρinv : ρ∘E.symm=σ := by
    funext z
    have he := congrFun hE (E.symm z)
    simpa only [Function.comp_apply,E.apply_symm_apply] using he.symm
  refine ⟨hD,hDint,restrictedProjection_holo s p hs hp hps hN hπ,
    restricted_invertible s p hs hp hps hN hπ,?_⟩
  intro m T _tT _cT _mT g hg hginv
  obtain ⟨h,⟨hh,hρh⟩,hunique⟩ := hρ.2.2.2.2 m T g hg hginv
  refine ⟨E∘h,⟨E.contMDiff.comp hh,?_⟩,?_⟩
  · calc
      σ∘(E∘h)=(σ∘E)∘h := rfl
      _=ρ∘h := congrArg (fun a => a∘h) hE
      _=g := hρh
  · intro h' hh'
    have hcomp : ρ∘(E.symm∘h')=g := by
      calc
        ρ∘(E.symm∘h')=(ρ∘E.symm)∘h' := rfl
        _=σ∘h' := congrArg (fun a => a∘h') hρinv
        _=g := hh'.2
    have he := hunique (E.symm∘h') ⟨E.symm.contMDiff.comp hh'.1,hcomp⟩
    funext t
    have hc := congrArg E (congrFun he t)
    simpa only [Function.comp_apply,E.apply_symm_apply] using hc

end Restriction

section OpenGraph
open HironakaActualLocalCommonGraphModel HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceRegularityConverse
  CategoryTheory AlgebraicGeometry

/-- The true graph section from its original coordinate open to the wide graph domain. -/
def openGraphSection (U : Opens (ComplexModel d)) (f : ComplexModel d → ComplexModel 1) :
    U → firstWideDomain (m := 1) U :=
  fun x => ⟨tangentInclusion d 1 x.val+actualJointNormalInclusion d 1 (f x.val),by
    change tangentProjection d 1 (tangentInclusion d 1 x.val+actualJointNormalInclusion d 1 (f x.val))∈U
    simp [tangentProjection_tangentInclusion]⟩

/-- The literal first block projection retains the true source coordinate open. -/
def openGraphProjection (U : Opens (ComplexModel d)) : firstWideDomain (m := 1) U → U :=
  fun z => ⟨tangentProjection d 1 z.val,z.property⟩

private theorem openGraphSection_holo (U : Opens (ComplexModel d))
    (f : ComplexModel d → ComplexModel 1) (hf : ContDiffOn ℂ ∞ f U) :
    ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ (openGraphSection U f) := by
  have hf' : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel 1) ∞ (fun x : U => f x.val) := by
    intro x
    exact contMDiffAt_subtype_iff.mpr ((hf.contDiffAt (U.isOpen.mem_nhds x.property)).contMDiffAt)
  apply (ContMDiff.subtypeVal_comp_iff (firstWideDomain U) _).mp
  exact ((tangentInclusion d 1).contMDiff.comp contMDiff_subtype_val).add
    ((actualJointNormalInclusion d 1).contMDiff.comp hf')

private theorem openGraphProjection_holo (U : Opens (ComplexModel d)) :
    ContMDiff 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel d) ∞ (openGraphProjection U) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  exact (tangentProjection d 1).contMDiff.comp contMDiff_subtype_val

private theorem openGraph_projection_section (U : Opens (ComplexModel d))
    (f : ComplexModel d → ComplexModel 1) : openGraphProjection U∘openGraphSection U f=id := by
  funext x
  apply Subtype.ext
  simp [openGraphProjection,openGraphSection,tangentProjection_tangentInclusion]

private theorem openGraph_range (U : Opens (ComplexModel d)) (f : ComplexModel d → ComplexModel 1) :
    range (openGraphSection U f)=firstGraphSubset U f univ := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    constructor
    · exact mem_univ _
    · simp [openGraphSection,tangentProjection_tangentInclusion]
  · intro hz
    refine ⟨openGraphProjection U z,?_⟩
    apply Subtype.ext
    change tangentInclusion d 1 (tangentProjection d 1 z.val)+
      actualJointNormalInclusion d 1 (f (tangentProjection d 1 z.val))=z.val
    rw [← hz.2]
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

private theorem openGraph_regular (U : Opens (ComplexModel d))
    (f : ComplexModel d → ComplexModel 1) (hf : ContDiffOn ℂ ∞ f U) :
    ∀ z∈range (openGraphSection U f),RegularAtDim (n := d+1) (range (openGraphSection U f)) z d := by
  have hm : ∀ x∈(univ : Set U),openGraphSection U f x∈firstGraphSubset U f univ := by
    intro x _hx
    rw [← openGraph_range U f]
    exact ⟨x,rfl⟩
  let : IsIso (actualSubspaceMap (openGraphSection_holo U f hf) hm) := by
    change IsIso (firstGraphModelIso U f hf univ).hom
    infer_instance
  intro z hz
  have hreg := regularAtDim_of_holomorphic_model_open_immersion
    (openGraphSection_holo U f hf) hm (openGraphProjection U z)
  rw [← openGraph_range U f] at hreg
  have he := section_projection (openGraphSection U f) (openGraphProjection U)
    (openGraph_projection_section U f) hz
  exact he ▸ hreg

/-- ORIGINAL graph data on the TRUE open internally supply all contact geometry and the full actual lower blowup. -/
theorem openGraph_restrictedProjection_isBlowupAlong (U : Opens (ComplexModel d))
    (f : ComplexModel d → ComplexModel 1) (hf : ContDiffOn ℂ ∞ f U)
    (D : Set U) (hD : IsClosedSubmanifold d D) (hDint : interior D=∅)
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+1)) Y]
    [IsComplexManifold (d+1) Y] {π : Y → firstWideDomain (m := 1) U}
    (hπ : IsBlowupAlong (d+1) (openGraphSection U f '' D) π) :
    letI := strictChartedSpace (openGraphSection U f) (openGraphProjection U)
      (openGraphSection_holo U f hf) (openGraphProjection_holo U) (openGraph_projection_section U f)
      (openGraph_regular U f hf) hπ
    letI := strict_isComplexManifold (openGraphSection U f) (openGraphProjection U)
      (openGraphSection_holo U f hf) (openGraphProjection_holo U) (openGraph_projection_section U f)
      (openGraph_regular U f hf) hπ
    IsBlowupAlong d D (restrictedProjection (openGraphSection U f) (openGraphProjection U) π D) :=
  restrictedProjection_isBlowupAlong (openGraphSection U f) (openGraphProjection U)
    (openGraphSection_holo U f hf) (openGraphProjection_holo U) (openGraph_projection_section U f)
    (openGraph_regular U f hf) D hD hDint hπ

end OpenGraph

end
end Hironaka.HironakaActualRetractContactLocalization
