/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainFinitePolynomialModel
import Hironaka.Resolution.HironakaRelativeNormalAffineDNCDictionary

/-! # Every original nearby initial ideal from the same actual real polynomial family
Complete four-node mathematics precedes code. Membership comparisons are made
at actual points in genuine coherent domains. No global coherence extension,
arbitrary nearby germ map or desired kernel/flatness certificate is supplied.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainNearbyInitialKernel
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  OkaCoherence HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainSaturation
  HironakaSmoothCentreRealDomainDeformation HironakaSmoothCentreRealDomainInitialRelations
  HironakaSmoothCentreRealDomainGraphDictionary HironakaSmoothCentreRealDomainInitialEquality
  HironakaSmoothCentreRealDomainFinitePolynomialModel HironakaRelativeNormalCoherentSaturation
  HironakaRelativeNormalDeformationSaturation HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalAffineDNCDictionary
  HironakaRelativeNormalDeformationFiniteRelationsSpread HironakaRelativeNormalAnalyticCoefficients
  HironakaRelativeNormalGraphCentralPolynomialModel HironakaRelativeNormalNearbyPolynomialCoefficientGerms
  HironakaRelativeNormalHomogeneousAnalyticContraction HironakaHolomorphicJetChartInvariance
  RelativePrincipalizationSpan InvertibleIdealQuotient RestrictedIdealExtension DerivativeIdealAlongEtale HadamardBridge

/-- A real local finite presentation gives actual holomorphicity of every member at its point. -/
theorem coherentOn_holomorphicAt_mem {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (W : Set (ComplexModel n)) (hI : CoherentOn I W) {x : ComplexModel n} (hx : x ∈ W)
    {g : ComplexModel n → ℂ} (hg : I.mem x g) : HolomorphicAt n g x := by
  obtain ⟨U, _hU, hxU, _hUW, N, S, _hS, hgen⟩ := hI x hx
  exact ((hgen x hxU g).mp hg).1

/-- True local membership is closed under an actual equality of representatives. -/
theorem coherentOn_mem_congr {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (W : Set (ComplexModel n)) (hI : CoherentOn I W) {x : ComplexModel n} (hx : x ∈ W)
    {f g : ComplexModel n → ℂ} (hf : I.mem x f) (he : f =ᶠ[𝓝 x] g) : I.mem x g := by
  obtain ⟨U, _hU, hxU, _hUW, N, S, _hS, hgen⟩ := hI x hx
  exact (hgen x hxU g).mpr (DerivativeIdeal.isInSpanAt_congr ((hgen x hxU f).mp hf) he)

/-- True local membership absorbs every actual finite holomorphic span of its members. -/
theorem coherentOn_mem_of_isInSpanAt {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (W : Set (ComplexModel n)) (hI : CoherentOn I W) {x : ComplexModel n} (hx : x ∈ W)
    {g : ComplexModel n → ℂ} (hg : IsInSpanAt (n := n) (I.mem x) x g) : I.mem x g := by
  obtain ⟨U, _hU, hxU, _hUW, N, S, _hS, hgen⟩ := hI x hx
  apply (hgen x hxU g).mpr
  exact IsInSpanAt.trans (fun f hf => (hgen x hxU f).mp hf) hg

/-- Actual local inverse membership uses original coherence ONLY on the true source domain. -/
theorem mem_pullback_iff_of_real_local_inverse {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (W : Set (ComplexModel n)) (hI : CoherentOn I W)
    {φ ψ : ComplexModel n → ComplexModel n} {y : ComplexModel n}
    (hy : φ y ∈ W) (hψ : IsLocalInverseAt n φ ψ y) {f : ComplexModel n → ℂ} :
    (GermIdeal.pullback (m := n) φ I).mem y f ↔ I.mem (φ y) (f ∘ ψ) := by
  have hψy : ψ (φ y) = y := hψ.left_inv.self_of_nhds
  constructor
  · intro hf
    have hf' : IsInSpanAt (n := n) (fun s => ∃ b, I.mem (φ y) b ∧ s = b ∘ φ) (ψ (φ y)) f := by
      rw [hψy]
      exact hf
    have hc := isInSpanAt_comp_eventually_mdifferentiable hψ.mdiff_inv hf'
    apply coherentOn_mem_of_isInSpanAt I W hI hy
    refine IsInSpanAt.mono ?_ hc
    rintro t ⟨s, ⟨b, hb, rfl⟩, rfl⟩
    refine coherentOn_mem_congr I W hI hy hb ?_
    filter_upwards [hψ.right_inv] with q hq
    simp [hq]
  · intro hf
    have hhol : HolomorphicAt n ((f ∘ ψ) ∘ φ) y :=
      holomorphicAt_comp_map hψ.mdiff (coherentOn_holomorphicAt_mem I W hI hy hf)
    apply GermIdeal.mem_pullback_iff.mpr
    refine DerivativeIdeal.isInSpanAt_congr (isInSpanAt_self ⟨f ∘ ψ, hf, rfl⟩ hhol) ?_
    filter_upwards [hψ.left_inv] with q hq
    simp [hq]

/-- Pullback composition has the WHOLE pointwise dictionary on its genuine source domain. -/
theorem pullback_comp_mem_of_real {n m ℓ : ℕ}
    {f : ComplexModel m → ComplexModel n} {g : ComplexModel ℓ → ComplexModel m}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel ℓ) 𝓘(ℂ,ComplexModel m) ∞ g)
    (I : GermIdeal n (ComplexModel n)) (W : Set (ComplexModel n)) (hI : CoherentOn I W)
    (z : ComplexModel ℓ) (hz : f (g z) ∈ W) (v : ComplexModel ℓ → ℂ) :
    (GermIdeal.pullback (m := ℓ) (f ∘ g) I).mem z v ↔
      (GermIdeal.pullback (m := ℓ) g (GermIdeal.pullback (m := m) f I)).mem z v := by
  constructor
  · intro hv
    have hfat : ∀ᶠ y in 𝓝 (g z), MDifferentiableAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) f y :=
      Eventually.of_forall fun _ => (hf.contMDiffAt.mdifferentiableAt (by simp))
    refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c,hc,rfl⟩
    have hchol := coherentOn_holomorphicAt_mem I W hI hz hc
    have hcfhol : HolomorphicAt m (c ∘ f) (g z) := holomorphicAt_comp_map hfat hchol
    have hcf : (GermIdeal.pullback (m := m) f I).mem (g z) (c ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨c,hc,rfl⟩ hcfhol)
    exact ⟨c ∘ f,hcf,rfl⟩
  · intro hv
    refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c,hc,rfl⟩
    have hgat : ∀ᶠ y in 𝓝 z, MDifferentiableAt 𝓘(ℂ,ComplexModel ℓ) 𝓘(ℂ,ComplexModel m) g y :=
      Eventually.of_forall fun _ => (hg.contMDiffAt.mdifferentiableAt (by simp))
    refine IsInSpanAt.mono ?_ (isInSpanAt_comp_eventually_mdifferentiable hgat (GermIdeal.mem_pullback_iff.mp hc))
    rintro u' ⟨σ,⟨d,hd,rfl⟩,rfl⟩
    exact ⟨d,hd,rfl⟩

/-- The exact sum pullback membership dictionary uses ONLY real source-domain coherence. -/
theorem pullback_sum_mem_of_real {n m : ℕ} {f : ComplexModel m → ComplexModel n}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (I J : GermIdeal n (ComplexModel n)) (W : Set (ComplexModel n))
    (hI : CoherentOn I W) (hJ : CoherentOn J W)
    (y : ComplexModel m) (hy : f y ∈ W) (v : ComplexModel m → ℂ) :
    (GermIdeal.pullback (m := m) f (sumIdeal I J)).mem y v ↔
      (sumIdeal (GermIdeal.pullback (m := m) f I) (GermIdeal.pullback (m := m) f J)).mem y v := by
  have hfat : ∀ᶠ z in 𝓝 y, ContMDiffAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f z :=
    Eventually.of_forall fun _ => hf.contMDiffAt
  have h𝔞 : ∀ a, I.mem (f y) a → HolomorphicAt n a (f y) :=
    fun _ hi => coherentOn_holomorphicAt_mem I W hI hy hi
  have h𝔟 : ∀ a, J.mem (f y) a → HolomorphicAt n a (f y) :=
    fun _ hi => coherentOn_holomorphicAt_mem J W hJ hy hi
  constructor
  · intro hv
    change IsInSpanAt (n := m) (fun a => (GermIdeal.pullback (m := m) f I).mem y a ∨
      (GermIdeal.pullback (m := m) f J).mem y a) y v
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv)
    rintro _ ⟨a,ha,rfl⟩
    change IsInSpanAt (n := n) (fun a => I.mem (f y) a ∨ J.mem (f y) a) (f y) a at ha
    obtain ⟨_,K,r,c,hr,hc,hsum⟩ := ha
    have heq : (fun p => ∑ k, (c k ∘ f) p * (r k ∘ f) p) =ᶠ[𝓝 y] a ∘ f :=
      ((hf.continuous.tendsto y).eventually hsum).mono fun p hp => hp.symm
    refine DerivativeIdeal.isInSpanAt_congr (IsInSpanAt.sum Finset.univ fun k _ => ?_) heq
    refine IsInSpanAt.mul_left ((hc k).comp_contMDiff hfat) ?_
    rcases hr k with hrk | hrk
    · refine isInSpanAt_self (Or.inl ?_) ((h𝔞 _ hrk).comp_contMDiff hfat)
      exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨r k,hrk,rfl⟩ ((h𝔞 _ hrk).comp_contMDiff hfat))
    · refine isInSpanAt_self (Or.inr ?_) ((h𝔟 _ hrk).comp_contMDiff hfat)
      exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨r k,hrk,rfl⟩ ((h𝔟 _ hrk).comp_contMDiff hfat))
  · intro hv
    change IsInSpanAt (n := m) (fun a => (GermIdeal.pullback (m := m) f I).mem y a ∨
      (GermIdeal.pullback (m := m) f J).mem y a) y v at hv
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ hv)
    rintro _ (hs | hs)
    · refine (GermIdeal.mem_pullback_iff.mp hs).mono ?_
      rintro _ ⟨a,ha,he⟩
      refine ⟨a, ?_, he⟩
      change IsInSpanAt (n := n) (fun c => I.mem (f y) c ∨ J.mem (f y) c) (f y) a
      exact isInSpanAt_self (Or.inl ha) (h𝔞 a ha)
    · refine (GermIdeal.mem_pullback_iff.mp hs).mono ?_
      rintro _ ⟨a,ha,he⟩
      refine ⟨a, ?_, he⟩
      change IsInSpanAt (n := n) (fun c => I.mem (f y) c ∨ J.mem (f y) c) (f y) a
      exact isInSpanAt_self (Or.inr ha) (h𝔟 a ha)

/-- The EXISTING deformation is coherent only on the true original projection-preimage domain. -/
theorem coherentOn_originalDeformation_of_real (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (hI : CoherentOn I T) :
    CoherentOn (originalDeformationIdeal d t I) ((deformationProjection d t) ⁻¹' T) := by
  let V := (deformationProjection d t) ⁻¹' T
  have hV : IsOpen V := hT.preimage (deformationProjection d t).continuous
  have hpull := coherentOn_pullback_of_local I T hI V hV (deformationProjection d t)
    (fun _ _ => (deformationProjection d t).differentiableAt.mdifferentiableAt) (fun _ hz => hz)
  have hEq := coherentOn_of_isCoherent (deformationEquationIdeal d t)
    (deformationEquationIdeal_isCoherent d t) V hV
  exact coherentOn_sum _ _ V hpull hEq

/-- The actual centre translation gives WHOLE existing deformation membership at zero on the real source domain. -/
theorem original_deformation_pullback_shift_mem_real (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (hI : CoherentOn I T) (a : ComplexModel d)
    (ha : tangentInclusion d t a ∈ T) (v : ComplexModel (deformationDimension d t) → ℂ) :
    (originalDeformationIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a))).mem 0 v ↔
      (GermIdeal.pullback (m := deformationDimension d t) (actualDNCBaseShift d t a)
        (originalDeformationIdeal d t I)).mem 0 v := by
  let V := (deformationProjection d t) ⁻¹' T
  have hV : IsOpen V := hT.preimage (deformationProjection d t).continuous
  have hpull := coherentOn_pullback_of_local I T hI V hV (deformationProjection d t)
    (fun _ _ => (deformationProjection d t).differentiableAt.mdifferentiableAt) (fun _ hz => hz)
  have hEq := coherentOn_of_isCoherent (deformationEquationIdeal d t)
    (deformationEquationIdeal_isCoherent d t) V hV
  have hz : actualDNCBaseShift d t a 0 ∈ V := by
    change deformationProjection d t (actualDNCBaseShift d t a 0) ∈ T
    simpa only [actualDNCBaseShift_projection,map_zero,actualAffineTranslation_zero] using ha
  have hfirst : ∀ f,
      (GermIdeal.pullback (m := deformationDimension d t) (deformationProjection d t)
        (actualTranslatedOriginalSheaf I (tangentInclusion d t a))).mem 0 f ↔
      (GermIdeal.pullback (m := deformationDimension d t) (actualDNCBaseShift d t a)
        (GermIdeal.pullback (m := deformationDimension d t) (deformationProjection d t) I)).mem 0 f := by
    intro f
    have hleft := pullback_comp_mem_of_real
      (actualAffineTranslation_contMDiff (d+t) (tangentInclusion d t a))
      (deformationProjection d t).contMDiff I T hI 0
      (by simpa only [map_zero,actualAffineTranslation_zero] using ha) f
    have hright := pullback_comp_mem_of_real (deformationProjection d t).contMDiff
      (actualDNCBaseShift_holomorphic d t a) I T hI 0 hz f
    have he : (deformationProjection d t) ∘ actualDNCBaseShift d t a =
        actualAffineTranslation (d+t) (tangentInclusion d t a) ∘ (deformationProjection d t) :=
      funext (actualDNCBaseShift_projection d t a)
    rw [he] at hright
    exact hleft.symm.trans hright
  have hsum : (originalDeformationIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a))).mem 0 v ↔
      (sumIdeal (GermIdeal.pullback (m := deformationDimension d t) (actualDNCBaseShift d t a)
        (GermIdeal.pullback (m := deformationDimension d t) (deformationProjection d t) I))
          (deformationEquationIdeal d t)).mem 0 v := by
    change IsInSpanAt (n := deformationDimension d t) (fun f =>
      (GermIdeal.pullback (m := deformationDimension d t) (deformationProjection d t)
        (actualTranslatedOriginalSheaf I (tangentInclusion d t a))).mem 0 f ∨
        (deformationEquationIdeal d t).mem 0 f) 0 v ↔
      IsInSpanAt (n := deformationDimension d t) (fun f =>
      (GermIdeal.pullback (m := deformationDimension d t) (actualDNCBaseShift d t a)
        (GermIdeal.pullback (m := deformationDimension d t) (deformationProjection d t) I)).mem 0 f ∨
        (deformationEquationIdeal d t).mem 0 f) 0 v
    constructor
    · exact IsInSpanAt.mono fun f hf => hf.imp (hfirst f).mp id
    · exact IsInSpanAt.mono fun f hf => hf.imp (hfirst f).mpr id
  have hs := pullback_sum_mem_of_real (actualDNCBaseShift_holomorphic d t a)
    (GermIdeal.pullback (m := deformationDimension d t) (deformationProjection d t) I)
    (deformationEquationIdeal d t) V hpull hEq 0 hz v
  rw [actualDNCBaseShift_equationIdeal] at hs
  exact hsum.trans hs.symm

/-- The original deformation inverse-composite dictionary holds at the ACTUAL centre image point. -/
theorem original_deformation_origin_translation_of_real (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (hI : CoherentOn I T) (a : ComplexModel d)
    (ha : tangentInclusion d t a ∈ T) (f : ComplexModel (deformationDimension d t) → ℂ) :
    (originalDeformationIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a))).mem 0 f ↔
      (originalDeformationIdeal d t I).mem (deformationCentralInclusion d t (tangentInclusion d t a))
        (f ∘ actualAffineTranslation (deformationDimension d t)
          (-deformationCentralInclusion d t (tangentInclusion d t a))) := by
  rw [original_deformation_pullback_shift_mem_real d t I T hT hI a ha f]
  have hy : actualAffineTranslation (deformationDimension d t)
      (deformationCentralInclusion d t (tangentInclusion d t a)) 0 ∈ (deformationProjection d t) ⁻¹' T := by
    change actualDNCBaseShift d t a 0 ∈ (deformationProjection d t) ⁻¹' T
    change deformationProjection d t (actualDNCBaseShift d t a 0) ∈ T
    simpa only [actualDNCBaseShift_projection,map_zero,actualAffineTranslation_zero] using ha
  simpa only [actualDNCBaseShift,actualAffineTranslation_zero] using
    mem_pullback_iff_of_real_local_inverse (originalDeformationIdeal d t I)
      ((deformationProjection d t) ⁻¹' T) (coherentOn_originalDeformation_of_real d t I T hT hI) hy
      (actualAffineTranslation_localInverse (deformationDimension d t)
        (deformationCentralInclusion d t (tangentInclusion d t a)) 0) (f := f)

/-- EVERY literal parameter colon has its actual inverse-composite membership dictionary, using ONLY real coherence. -/
theorem original_colon_origin_translation_of_real (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (hI : CoherentOn I T) (a : ComplexModel d)
    (ha : tangentInclusion d t a ∈ T) (q : ℕ) (f : ComplexModel (deformationDimension d t) → ℂ) :
    (originalDeformationColonIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) q).mem 0 f ↔
      (originalDeformationColonIdeal d t I q).mem (deformationCentralInclusion d t (tangentInclusion d t a))
        (f ∘ actualAffineTranslation (deformationDimension d t)
          (-deformationCentralInclusion d t (tangentInclusion d t a))) := by
  induction q generalizing f with
  | zero => exact original_deformation_origin_translation_of_real d t I T hT hI a ha f
  | succ q ih =>
    change (HolAt f 0 ∧
      (originalDeformationColonIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) q).mem 0
        (fun z => f z * deformationParameter d t z)) ↔
      (HolAt (f ∘ actualAffineTranslation (deformationDimension d t)
        (-deformationCentralInclusion d t (tangentInclusion d t a)))
          (deformationCentralInclusion d t (tangentInclusion d t a)) ∧
      (originalDeformationColonIdeal d t I q).mem (deformationCentralInclusion d t (tangentInclusion d t a))
        (fun z => (f ∘ actualAffineTranslation (deformationDimension d t)
          (-deformationCentralInclusion d t (tangentInclusion d t a))) z * deformationParameter d t z))
    rw [ih]
    have hh := actualAffineTranslation_whole_holomorphic (deformationDimension d t)
      (deformationCentralInclusion d t (tangentInclusion d t a)) 0 f
    simp only [actualAffineTranslation_zero] at hh
    rw [hh]
    have he : (fun z => f z * deformationParameter d t z) ∘
        actualAffineTranslation (deformationDimension d t)
          (-deformationCentralInclusion d t (tangentInclusion d t a)) =
        fun z => (f ∘ actualAffineTranslation (deformationDimension d t)
          (-deformationCentralInclusion d t (tangentInclusion d t a))) z * deformationParameter d t z := by
      funext z
      simp only [Function.comp_apply]
      congr 1
      change deformationParameter d t
        (-deformationCentralInclusion d t (tangentInclusion d t a) + z) = deformationParameter d t z
      rw [map_add,map_neg,deformationCentralInclusion_parameter,neg_zero,zero_add]
    rw [he]

/-- The translated original family is coherent on its ACTUAL translated real domain. -/
theorem coherentOn_actualTranslated_of_real {n : ℕ}
    (I : GermIdeal n (ComplexModel n)) (T : Set (ComplexModel n))
    (hT : IsOpen T) (hI : CoherentOn I T) (a : ComplexModel n) :
    CoherentOn (actualTranslatedOriginalSheaf I a) ((actualAffineTranslation n a) ⁻¹' T) := by
  exact coherentOn_pullback_of_local I T hI _
    (hT.preimage (actualAffineTranslation_contMDiff n a).continuous)
    (actualAffineTranslation n a)
    (fun _ _ => (actualAffineTranslation_contMDiff n a).mdifferentiable (by simp) |>.mdifferentiableAt)
    (fun _ hz => hz)

/-- At the SAME actual selected index, whole central memberships translate using real colon coherence only. -/
theorem original_central_origin_membership_translation_of_real (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (hI : CoherentOn I T) (a : ComplexModel d)
    (ha : tangentInclusion d t a ∈ T) (N : ℕ)
    (U : Set (ComplexModel (deformationDimension d t)))
    (hK : CoherentOn (originalDeformationColonIdeal d t I N) U)
    (hb : deformationCentralInclusion d t (tangentInclusion d t a) ∈ U)
    (v : ComplexModel (d+t) → ℂ) :
    (originalDeformationCentralIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) N).mem 0 v ↔
      (actualTranslatedOriginalSheaf (originalDeformationCentralIdeal d t I N) (tangentInclusion d t a)).mem 0 v := by
  have hcolon : ∀ f,
      (originalDeformationColonIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) N).mem 0 f ↔
      (GermIdeal.pullback (m := deformationDimension d t) (actualDNCBaseShift d t a)
        (originalDeformationColonIdeal d t I N)).mem 0 f := by
    intro f
    have hy : actualAffineTranslation (deformationDimension d t)
        (deformationCentralInclusion d t (tangentInclusion d t a)) 0 ∈ U := by
      simpa only [actualAffineTranslation_zero] using hb
    have hinv := mem_pullback_iff_of_real_local_inverse (originalDeformationColonIdeal d t I N) U hK hy
      (actualAffineTranslation_localInverse (deformationDimension d t)
        (deformationCentralInclusion d t (tangentInclusion d t a)) 0) (f := f)
    simp only [actualAffineTranslation_zero] at hinv
    exact (original_colon_origin_translation_of_real d t I T hT hI a ha N f).trans hinv.symm
  have hfirst : (originalDeformationCentralIdeal d t
        (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) N).mem 0 v ↔
      (GermIdeal.pullback (m := d+t) (deformationCentralInclusion d t)
        (GermIdeal.pullback (m := deformationDimension d t) (actualDNCBaseShift d t a)
          (originalDeformationColonIdeal d t I N))).mem 0 v := by
    constructor
    · intro hv
      apply GermIdeal.mem_pullback_iff.mpr
      apply IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv)
      rintro _ ⟨f,hf,rfl⟩
      refine ⟨f,?_,rfl⟩
      simpa only [map_zero] using (hcolon f).mp (by simpa only [map_zero] using hf)
    · intro hv
      apply GermIdeal.mem_pullback_iff.mpr
      apply IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv)
      rintro _ ⟨f,hf,rfl⟩
      refine ⟨f,?_,rfl⟩
      simpa only [map_zero] using (hcolon f).mpr (by simpa only [map_zero] using hf)
  have hleft := pullback_comp_mem_of_real (actualDNCBaseShift_holomorphic d t a)
    (deformationCentralInclusion d t).contMDiff (originalDeformationColonIdeal d t I N) U hK 0
    (by simpa only [map_zero,actualDNCBaseShift,actualAffineTranslation_zero] using hb) v
  have hright := pullback_comp_mem_of_real (deformationCentralInclusion d t).contMDiff
    (actualAffineTranslation_contMDiff (d+t) (tangentInclusion d t a))
    (originalDeformationColonIdeal d t I N) U hK 0
    (by simpa only [actualAffineTranslation_zero] using hb) v
  have he : (deformationCentralInclusion d t) ∘ actualAffineTranslation (d+t) (tangentInclusion d t a) =
      actualDNCBaseShift d t a ∘ (deformationCentralInclusion d t) :=
    funext (actualDNCBaseShift_central d t a)
  rw [he] at hright
  exact hfirst.trans (hleft.symm.trans hright)

/-- ENTIRE origin ideals of the SAME-index central families agree after genuine real translation. -/
theorem original_central_whole_origin_translation_of_real (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (hI : CoherentOn I T) (a : ComplexModel d)
    (ha : tangentInclusion d t a ∈ T) (N : ℕ)
    (U : Set (ComplexModel (deformationDimension d t)))
    (hK : CoherentOn (originalDeformationColonIdeal d t I N) U)
    (hb : deformationCentralInclusion d t (tangentInclusion d t a) ∈ U) :
    originalCoherentOriginIdeal (originalDeformationCentralIdeal d t
      (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) N) =
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (originalDeformationCentralIdeal d t I N) (tangentInclusion d t a)) := by
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨f,hf,hIf,rfl⟩
    exact ⟨f,hf,(original_central_origin_membership_translation_of_real d t I T hT hI a ha N U hK hb f).mp hIf,rfl⟩
  · rintro ⟨f,hf,hIf,rfl⟩
    exact ⟨f,hf,(original_central_origin_membership_translation_of_real d t I T hT hI a ha N U hK hb f).mpr hIf,rfl⟩

/-- ALL actual same-index functional stability and the WHOLE colon union transport to the translated origin. -/
theorem original_translated_saturation_of_real (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (hI : CoherentOn I T) (a : ComplexModel d)
    (ha : tangentInclusion d t a ∈ T) (N : ℕ)
    (hchain : ∀ q : ℕ, ∀ f, (originalDeformationColonIdeal d t I (N+q)).mem
      (deformationCentralInclusion d t (tangentInclusion d t a)) f ↔
        (originalDeformationColonIdeal d t I N).mem
          (deformationCentralInclusion d t (tangentInclusion d t a)) f)
    (hsat : ∀ f, (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem
      (deformationCentralInclusion d t (tangentInclusion d t a)) f) ↔
        (originalDeformationColonIdeal d t I N).mem
          (deformationCentralInclusion d t (tangentInclusion d t a)) f) :
    (∀ q : ℕ, ∀ f,
      (originalDeformationColonIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) (N+q)).mem 0 f ↔
        (originalDeformationColonIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) N).mem 0 f) ∧
    (∀ f, (∃ q : ℕ,
      (originalDeformationColonIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) q).mem 0 f) ↔
        (originalDeformationColonIdeal d t (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) N).mem 0 f) := by
  constructor
  · intro q f
    rw [original_colon_origin_translation_of_real d t I T hT hI a ha (N+q) f,
      original_colon_origin_translation_of_real d t I T hT hI a ha N f]
    exact hchain q _
  · intro f
    constructor
    · rintro ⟨q,hq⟩
      apply (original_colon_origin_translation_of_real d t I T hT hI a ha N f).mpr
      apply (hsat _).mp
      exact ⟨q,(original_colon_origin_translation_of_real d t I T hT hI a ha q f).mp hq⟩
    · exact fun hf => ⟨N,hf⟩
private theorem nearby_initialSymbol_mem_selected_central_local (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t)))
    (hD : IdealFGAt (originalDeformationIdeal d t I).mem 0) (N : ℕ)
    (hN : ∀ f, (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem 0 f) ↔
      (originalDeformationColonIdeal d t I N).mem 0 f)
    (q : ℕ) (g : HolGerm (ComplexModel (d+t)))
    (hIg : g ∈ originalCoherentOriginIdeal I) (hg : g ∈ normalIdeal d t ^ q) :
    normalPolynomialEval d t (originalNormalInitialSymbol d t q g hg) ∈
      originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) := by
  obtain ⟨G, hG, hcentral⟩ := exists_divided_scaling_initial_symbol d t q g hg
  have hscaled := deformationScalingPullback_mem_originalIdeal_local d t I g hIg
  have hmul : G * deformationParameterGerm d t ^ q ∈
      originalCoherentOriginIdeal (originalDeformationIdeal d t I) := by
    rw [mul_comm, ← hG]
    exact hscaled
  have hcolon := (mem_actualOriginColonChain_iff
    (originalCoherentOriginIdeal (originalDeformationIdeal d t I)) (deformationParameterGerm d t) G q).mpr hmul
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk G
  have hfunctional := (actualColonChain_origin_dictionary_of_local (originalDeformationIdeal d t I) hD
    (Eventually.of_forall fun _ => (deformationParameter d t).differentiableAt) q hf).mpr hcolon
  have hchosen := (hN f).mp ⟨q, hfunctional⟩
  have horigin : HolGerm.mk f hf ∈ originalCoherentOriginIdeal (originalDeformationColonIdeal d t I N) :=
    Ideal.subset_span ⟨f, hf, hchosen, rfl⟩
  have hj := map_linear_originIdeal_le (deformationCentralInclusion d t)
    (originalDeformationColonIdeal d t I N) (Ideal.mem_map_of_mem _ horigin)
  change deformationCentralPullback d t (HolGerm.mk f hf) ∈
    originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) at hj
  rwa [hcentral] at hj

/-- Genuine finite generation and the ACTUAL whole functional saturation union give entire central-initial equality. -/
theorem whole_central_initial_equality_of_local_saturation (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t)))
    (hI : IdealFGAt I.mem 0) (hD : IdealFGAt (originalDeformationIdeal d t I).mem 0) (N : ℕ)
    (hN : ∀ f, (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem 0 f) ↔
      (originalDeformationColonIdeal d t I N).mem 0 f) :
    letI := tangentAlgebra d t
    originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) =
      Ideal.map (normalPolynomialEval d t).toRingHom
        (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)) := by
  let := tangentAlgebra d t
  have hforward : Ideal.map (normalPolynomialEval d t).toRingHom
      (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)) ≤
        originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [originalNormalInitialIdeal_eq_span_original_relations]
    apply Ideal.span_le.mpr
    rintro P ⟨a,rfl⟩
    exact nearby_initialSymbol_mem_selected_central_local d t I hD N hN a.1 a.2.val
      a.2.property.1 a.2.property.2
  have hreverse : originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) ≤
      Ideal.map (normalPolynomialEval d t).toRingHom
        (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)) := by
    rw [originalCentralOriginIdeal_eq_graphColon_image_of_local d t I hI hD N]
    apply Ideal.map_le_iff_le_comap.mpr
    intro h hh
    exact actual_graph_colon_central_mem_initial_image d t N I h hh
  exact hreverse.antisymm hforward

attribute [local instance] MvPolynomial.gradedAlgebra

section Original
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY original regularity/coherence supplies ALL genuine nearby original initial ideals by ONE finite polynomial family on ONE real base open. -/
theorem exists_original_regular_real_all_nearby_initial_polynomial_kernels
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    letI := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)),
        ∃ V : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' Φ.target ∧
        let F := actualFlattenedOriginalSheaf A x Φ
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ ((deformationCentralInclusion d t) ⁻¹' U) ∩ Φ.target ∧
        CoherentOn (originalDeformationCentralIdeal d t F N) V ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∀ α : Fin t →₀ ℕ, ∀ y ∈ V,
          DifferentiableAt ℂ (actualCoefficientRepresentative (P.coeff α)) (tangentProjection d t y)) ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∀ y ∈ V, HolAt (actualNormalPolynomialFunction d t P) y) ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∃ q : ℕ, P.IsHomogeneous q ∧
          ∀ y ∈ V, (actualPolynomialSpecialization P (tangentProjection d t y)).IsHomogeneous q) ∧
        (∀ y ∈ V, IdealFGAt (actualNormalPolynomialSpan d t F) y) ∧
        (∀ y ∈ V, ∀ g, actualNormalPolynomialSpan d t F y g ↔
          (originalDeformationCentralIdeal d t F N).mem y g) ∧
        let W := (tangentInclusion d t) ⁻¹' V
        IsOpen W ∧ 0 ∈ W ∧
        (∀ a ∈ W, tangentInclusion d t a ∈ Φ.target ∩ complexCoordinatePlane (d+t) d) ∧
        ∃ hc : ∀ a ∈ W, ∀ P : ↥(actualOriginalRelationFamily d t F), ∀ α,
          HolAt (actualCoefficientRepresentative (P.val.coeff α)) a,
        ∀ a (ha : a ∈ W),
          let H := Ideal.span (range fun P : ↥(actualOriginalRelationFamily d t F) =>
            actualNearbyCoefficientPolynomial d t P.val a (hc a ha P))
          let J := actualTranslatedOriginalSheaf F (tangentInclusion d t a)
          IdealFGAt J.mem 0 ∧ IdealFGAt (originalDeformationIdeal d t J).mem 0 ∧
          (∀ q : ℕ, ∀ f, (originalDeformationColonIdeal d t J (N+q)).mem 0 f ↔
            (originalDeformationColonIdeal d t J N).mem 0 f) ∧
          (∀ f, (∃ q : ℕ, (originalDeformationColonIdeal d t J q).mem 0 f) ↔
            (originalDeformationColonIdeal d t J N).mem 0 f) ∧
          H.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d))) ∧
          originalNormalInitialIdeal d t (originalCoherentOriginIdeal J) = H ∧
          originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N) =
            Ideal.map (normalPolynomialEval d t).toRingHom
              (originalNormalInitialIdeal d t (originalCoherentOriginIdeal J)) ∧
          originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N) =
            originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
              (originalDeformationCentralIdeal d t F N) (tangentInclusion d t a)) ∧
          originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N) =
            Ideal.map (normalPolynomialEval d t).toRingHom H ∧
          Ideal.comap (normalPolynomialEval d t).toRingHom
            (originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N)) = H := by
  classical
  let := tangentAlgebra d t
  obtain ⟨Φ,hsrc,h0,hflat,N,U,V,hU,h0U,hUV,hcol,hchain,hsat,hV,h0V,hVsub,
    hcent,hcoeff,hpoly,hdegree,hfg,hcentral,hW,h0W,hpoint,hc,hkernels⟩ :=
    exists_original_regular_real_translated_central_polynomial_kernels C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
  have hF := coherentOn_actualFlattenedOriginalSheaf A hA x Φ hsrc
  refine ⟨Φ,hsrc,h0,hflat,N,U,V,hU,h0U,hUV,hcol,hchain,hsat,hV,h0V,hVsub,
    hcent,hcoeff,hpoly,hdegree,hfg,hcentral,hW,h0W,hpoint,hc,?_⟩
  intro a ha
  dsimp only
  let J := actualTranslatedOriginalSheaf F (tangentInclusion d t a)
  let T := (actualAffineTranslation (d+t) (tangentInclusion d t a)) ⁻¹' Φ.target
  let H := Ideal.span (range fun P : ↥(actualOriginalRelationFamily d t F) =>
    actualNearbyCoefficientPolynomial d t P.val a (hc a ha P))
  have haT : tangentInclusion d t a ∈ Φ.target := (hpoint a ha).1
  have hT : IsOpen T := Φ.isOpen_target.preimage
    (actualAffineTranslation_contMDiff (d+t) (tangentInclusion d t a)).continuous
  have h0T : (0 : ComplexModel (d+t)) ∈ T := by
    change actualAffineTranslation (d+t) (tangentInclusion d t a) 0 ∈ Φ.target
    simpa only [actualAffineTranslation_zero] using haT
  have hJ := coherentOn_actualTranslated_of_real F Φ.target Φ.isOpen_target hF (tangentInclusion d t a)
  have hJFG : IdealFGAt J.mem 0 := idealFGAt_of_coherentOn J T hJ h0T
  have hD := coherentOn_originalDeformation_of_real d t J T hT hJ
  have h0D : (0 : ComplexModel (deformationDimension d t)) ∈ (deformationProjection d t) ⁻¹' T := by
    change deformationProjection d t 0 ∈ T
    simpa only [map_zero] using h0T
  have hDFG : IdealFGAt (originalDeformationIdeal d t J).mem 0 :=
    idealFGAt_of_coherentOn (originalDeformationIdeal d t J) _ hD h0D
  have hb : deformationCentralInclusion d t (tangentInclusion d t a) ∈ U := (hVsub ha).1
  have hst := original_translated_saturation_of_real d t F Φ.target Φ.isOpen_target hF a haT N
    (hchain _ hb) (hsat _ hb)
  have heInitial := whole_central_initial_equality_of_local_saturation d t J hJFG hDFG N hst.2
  have heSame := original_central_whole_origin_translation_of_real d t F Φ.target Φ.isOpen_target hF a haT N U hcol hb
  obtain ⟨hH,hmodel,hcontract⟩ := hkernels a ha
  have heModel : originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N) =
      Ideal.map (normalPolynomialEval d t).toRingHom H := heSame.trans hmodel
  have heKernel : originalNormalInitialIdeal d t (originalCoherentOriginIdeal J) = H := by
    have hi := whole_homogeneous_analytic_contraction d t
      (originalNormalInitialIdeal d t (originalCoherentOriginIdeal J))
      (originalNormalInitialIdeal_homogeneous d t (originalCoherentOriginIdeal J))
    rw [← heInitial,heModel] at hi
    exact hi.symm.trans (whole_homogeneous_analytic_contraction d t H hH)
  exact ⟨hJFG,hDFG,hst.1,hst.2,hH,heKernel,heInitial,heSame,heModel,
    by rw [heSame];exact hcontract⟩

end Original

end
end Hironaka.HironakaSmoothCentreRealDomainNearbyInitialKernel
