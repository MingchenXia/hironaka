/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainInitialRelations
import Hironaka.Resolution.HironakaRelativeNormalAnalyticGraphQuotient

/-! # Entire actual graph dictionaries from real original domains
Complete mathematics precedes code. The original-input producer internally supplies
all local presentations, the same actual N/U/B, and the true whole graph quotient,
all graph colons and exact central images. No global flattened-model coherence is
assumed or produced. The reverse initial-ideal and nearby graded kernels stay open.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainGraphDictionary
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  OkaCoherence HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainSaturation
  HironakaSmoothCentreRealDomainDeformation HironakaSmoothCentreRealDomainInitialRelations
  HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalDeformationSaturation
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalAnalyticGraphQuotient
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalMonomialBasis
  HironakaHolomorphicJetChartInvariance RelativePrincipalizationSpan InvertibleIdealQuotient

/-- Genuine local generation forces every recorded origin member to be holomorphic. -/
theorem holAt_mem_of_idealFGAt {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (hI : IdealFGAt I.mem 0) {f : ComplexModel n → ℂ} (hf : I.mem 0 f) : HolAt f 0 := by
  obtain ⟨U, _hU, h0U, μ, hμ, S, _hS, hgen⟩ := hI
  let := hμ
  exact ((hgen 0 h0U f).mp hf).1

theorem originalOriginIdeal_pullback_eq_of_holMem {m n : ℕ}
    (η : ComplexModel m →L[ℂ] ComplexModel n)
    (I : GermIdeal n (ComplexModel n)) (hI : ∀ f, I.mem 0 f → HolAt f 0) :
    originalCoherentOriginIdeal (GermIdeal.pullback (m := m) η I) =
      Ideal.map (compAlgHom η (Eventually.of_forall fun _ => η.differentiableAt) (map_zero _)).toRingHom
        (originalCoherentOriginIdeal I) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hIf,rfl⟩
    let S := fun s : ComplexModel m → ℂ => ∃ a, I.mem (η 0) a ∧ s = a ∘ η
    have hS : ∀ s, S s → HolAt s 0 := by
      rintro s ⟨a,ha,rfl⟩
      have ha0 : I.mem 0 a := by simpa only [map_zero] using ha
      exact holomorphic_comp η (Eventually.of_forall fun _ => η.differentiableAt) (map_zero _)
        (hI a ha0)
    apply whole_origin_span_mem _ S hS ?_ hf hIf
    rintro s ⟨a,ha,rfl⟩
    have ha0 : I.mem 0 a := by simpa only [map_zero] using ha
    have hah : HolAt a 0 := hI a ha0
    have he : HolGerm.mk (a ∘ η) (hS (a ∘ η) ⟨a,ha,rfl⟩) =
        compAlgHom η (Eventually.of_forall fun _ => η.differentiableAt) (map_zero _)
          (HolGerm.mk a hah) := by rw [compAlgHom_mk]
    rw [he]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a, hah, ha0, rfl⟩)
  · exact map_linear_originIdeal_le η I

/-- Exact entire sum dictionary from actual holomorphic members at zero. -/
theorem originalOriginIdeal_sum_eq_of_holMem {n : ℕ}
    (I J : GermIdeal n (ComplexModel n))
    (hI : ∀ f, I.mem 0 f → HolAt f 0) (hJ : ∀ f, J.mem 0 f → HolAt f 0) :
    originalCoherentOriginIdeal (RestrictedIdealExtension.sumIdeal I J) =
      originalCoherentOriginIdeal I ⊔ originalCoherentOriginIdeal J := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f, hf, hIf, rfl⟩
    let S := fun s : ComplexModel n → ℂ => I.mem 0 s ∨ J.mem 0 s
    have hS : ∀ s, S s → HolAt s 0 := by
      intro s hs
      rcases hs with hs | hs
      · exact hI s hs
      · exact hJ s hs
    apply whole_origin_span_mem _ S hS ?_ hf hIf
    intro s hs
    rcases hs with hs | hs
    · exact (show originalCoherentOriginIdeal I ≤ originalCoherentOriginIdeal I ⊔ originalCoherentOriginIdeal J from le_sup_left)
        (Ideal.subset_span ⟨s, hI s hs, hs, rfl⟩)
    · exact (show originalCoherentOriginIdeal J ≤ originalCoherentOriginIdeal I ⊔ originalCoherentOriginIdeal J from le_sup_right)
        (Ideal.subset_span ⟨s, hJ s hs, hs, rfl⟩)
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro g ⟨f, hf, hIf, rfl⟩
      apply Ideal.subset_span
      refine ⟨f, hf, ?_, rfl⟩
      change IsInSpanAt (n := n) (fun s => I.mem 0 s ∨ J.mem 0 s) 0 f
      exact isInSpanAt_self (Or.inl hIf) (hf.mono (fun _ h => h.mdifferentiableAt))
    · apply Ideal.span_le.mpr
      rintro g ⟨f, hf, hJf, rfl⟩
      apply Ideal.subset_span
      refine ⟨f, hf, ?_, rfl⟩
      change IsInSpanAt (n := n) (fun s => I.mem 0 s ∨ J.mem 0 s) 0 f
      exact isInSpanAt_self (Or.inr hJf) (hf.mono (fun _ h => h.mdifferentiableAt))

/-- A real local presentation gives the EXISTING graph ideal's exact whole decomposition. -/
theorem originalDeformationOriginIdeal_eq_of_local (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : IdealFGAt I.mem 0) :
    originalCoherentOriginIdeal (originalDeformationIdeal d t I) =
      Ideal.map (tangentPullback (d+t) (1+t)).toRingHom (originalCoherentOriginIdeal I) ⊔
        originalCoherentOriginIdeal (deformationEquationIdeal d t) := by
  unfold originalDeformationIdeal
  rw [originalOriginIdeal_sum_eq_of_holMem
    (GermIdeal.pullback (m := deformationDimension d t) (deformationProjection d t) I)
    (deformationEquationIdeal d t)
    (fun _ hf => hf.1.mono (fun _ h => h.differentiableAt))
    (fun _ hf => hf.1.mono (fun _ h => h.differentiableAt)),
    originalOriginIdeal_pullback_eq_of_holMem (deformationProjection d t) I
      (fun _ hf => holAt_mem_of_idealFGAt I hI hf)]
  rfl

theorem graphTrace_kernel_le_original_of_local (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : IdealFGAt I.mem 0) :
    RingHom.ker (graphTrace d t).toRingHom ≤ originalCoherentOriginIdeal (originalDeformationIdeal d t I) := by
  rw [graphTrace_kernel,originalDeformationOriginIdeal_eq_of_local d t I hI]
  exact le_sup_right

theorem graphTrace_map_originalOriginIdeal_of_local (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : IdealFGAt I.mem 0) :
    Ideal.map (graphTrace d t).toRingHom (originalCoherentOriginIdeal (originalDeformationIdeal d t I)) =
      actualGraphScaledIdeal d t I := by
  rw [originalDeformationOriginIdeal_eq_of_local d t I hI,Ideal.map_sup,Ideal.map_map]
  have he : Ideal.map (graphTrace d t).toRingHom
      (originalCoherentOriginIdeal (deformationEquationIdeal d t)) = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker _).mpr
    rw [graphTrace_kernel]
  rw [he,sup_bot_eq]
  rfl

theorem originalOriginIdeal_eq_graphTrace_comap_of_local (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : IdealFGAt I.mem 0) :
    originalCoherentOriginIdeal (originalDeformationIdeal d t I) =
      Ideal.comap (graphTrace d t).toRingHom (actualGraphScaledIdeal d t I) := by
  rw [← graphTrace_map_originalOriginIdeal_of_local d t I hI,
    Ideal.comap_map_of_surjective' (graphTrace d t).toRingHom (graphTrace_surjective d t)]
  exact (sup_eq_left.mpr (graphTrace_kernel_le_original_of_local d t I hI)).symm

theorem originalGraphQuotientMap_kernel_of_local (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : IdealFGAt I.mem 0) :
    RingHom.ker (originalGraphQuotientMap d t I) = originalCoherentOriginIdeal (originalDeformationIdeal d t I) := by
  rw [originalOriginIdeal_eq_graphTrace_comap_of_local d t I hI]
  ext g
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk (actualGraphScaledIdeal d t I) (graphTrace d t g) = 0 ↔
    graphTrace d t g ∈ actualGraphScaledIdeal d t I
  exact Ideal.Quotient.eq_zero_iff_mem



def originalGraphQuotientEquiv_of_local (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : IdealFGAt I.mem 0) :
    (HolGerm (ComplexModel (deformationDimension d t)) ⧸
      originalCoherentOriginIdeal (originalDeformationIdeal d t I)) ≃+*
    (HolGerm (ComplexModel (graphDimension d t)) ⧸ actualGraphScaledIdeal d t I) :=
  (Ideal.quotEquivOfEq (originalGraphQuotientMap_kernel_of_local d t I hI).symm).trans
    (RingHom.quotientKerEquivOfSurjective (originalGraphQuotientMap_surjective d t I))

theorem originalGraphQuotientEquiv_apply_mk_of_local (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : IdealFGAt I.mem 0)
    (g : HolGerm (ComplexModel (deformationDimension d t))) :
    originalGraphQuotientEquiv_of_local d t I hI (Ideal.Quotient.mk
      (originalCoherentOriginIdeal (originalDeformationIdeal d t I)) g) =
      Ideal.Quotient.mk (actualGraphScaledIdeal d t I) (graphTrace d t g) := by
  rw [originalGraphQuotientEquiv_of_local,RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

theorem originalOriginColon_eq_graphTrace_comap_of_local (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : IdealFGAt I.mem 0) (q : ℕ) :
    actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t I))
      (deformationParameterGerm d t) q = Ideal.comap (graphTrace d t).toRingHom (actualGraphColonIdeal d t I q) := by
  ext g
  rw [mem_actualOriginColonChain_iff,originalOriginIdeal_eq_graphTrace_comap_of_local d t I hI]
  change graphTrace d t (g*deformationParameterGerm d t^q) ∈ actualGraphScaledIdeal d t I ↔
    graphTrace d t g ∈ actualOriginColonChain (actualGraphScaledIdeal d t I) (graphParameterGerm d t) q
  rw [mem_actualOriginColonChain_iff,map_mul,map_pow,graphTrace_parameter]

theorem graphTrace_map_originalOriginColon_of_local (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : IdealFGAt I.mem 0) (q : ℕ) :
    Ideal.map (graphTrace d t).toRingHom
      (actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t I))
        (deformationParameterGerm d t) q) = actualGraphColonIdeal d t I q := by
  rw [originalOriginColon_eq_graphTrace_comap_of_local d t I hI,
    Ideal.map_comap_of_surjective (f := (graphTrace d t).toRingHom) (graphTrace_surjective d t)]

/-- Every literal colon origin ideal is the corresponding entire whole parameter colon. -/
theorem originalOriginIdeal_actualColon_of_local {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (hI : IdealFGAt I.mem 0) {h : ComplexModel n → ℂ} (hh : HolAt h 0) (q : ℕ) :
    originalCoherentOriginIdeal (actualColonGermIdeal I h q) =
      actualOriginColonChain (originalCoherentOriginIdeal I) (HolGerm.mk h hh) q := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f, hf, hIf, rfl⟩
    exact (actualColonChain_origin_dictionary_of_local I hI hh q hf).mp hIf
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
    exact Ideal.subset_span ⟨f, hf,
      (actualColonChain_origin_dictionary_of_local I hI hh q hf).mpr hg, rfl⟩

private theorem actualColonChain_holAt_of_local {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (hI : IdealFGAt I.mem 0) (h : ComplexModel n → ℂ) (q : ℕ)
    {f : ComplexModel n → ℂ} (hf : actualColonChain I.mem h q 0 f) : HolAt f 0 := by
  cases q with
  | zero => exact holAt_mem_of_idealFGAt I hI hf
  | succ q => exact hf.1

/-- The SAME actual central family at every order is exactly the whole graph-colon image. -/
theorem originalCentralOriginIdeal_eq_graphColon_image_of_local (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : IdealFGAt I.mem 0)
    (hD : IdealFGAt (originalDeformationIdeal d t I).mem 0) (q : ℕ) :
    originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I q) =
      Ideal.map (graphCentralPullback d t).toRingHom (actualGraphColonIdeal d t I q) := by
  have hpar : HolAt (deformationParameter d t) 0 :=
    Eventually.of_forall fun _ => (deformationParameter d t).differentiableAt
  have hcolon : originalCoherentOriginIdeal (originalDeformationColonIdeal d t I q) =
      actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t I))
        (deformationParameterGerm d t) q :=
    originalOriginIdeal_actualColon_of_local (originalDeformationIdeal d t I) hD hpar q
  have hpull := originalOriginIdeal_pullback_eq_of_holMem (deformationCentralInclusion d t)
    (originalDeformationColonIdeal d t I q)
    (fun _ hf => actualColonChain_holAt_of_local (originalDeformationIdeal d t I) hD _ q hf)
  change originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I q) =
    Ideal.map (deformationCentralPullback d t).toRingHom
      (originalCoherentOriginIdeal (originalDeformationColonIdeal d t I q)) at hpull
  rw [hpull, hcolon, ← graphCentralPullback_comp_trace, ← Ideal.map_map,
    graphTrace_map_originalOriginColon_of_local d t I hI q]

section Original
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Pure original data internally supply ALL true whole graph dictionaries at the SAME real witnesses. -/
theorem exists_original_regular_real_whole_graph_model
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    letI := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' Φ.target ∧
        let F := actualFlattenedOriginalSheaf A x Φ
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
          ((originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ q) ↔
            (originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ N))) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        let B := (deformationCentralInclusion d t) ⁻¹' U
        IsOpen B ∧ 0 ∈ B ∧ CoherentOn (originalDeformationCentralIdeal d t F N) B ∧
        Ideal.map (normalPolynomialEval d t).toRingHom
          (originalNormalInitialIdeal d t (originalCoherentOriginIdeal F)) ≤
            originalCoherentOriginIdeal (originalDeformationCentralIdeal d t F N) ∧
        (∀ q : ℕ, originalCoherentOriginIdeal (originalDeformationCentralIdeal d t F q) =
          Ideal.map (graphCentralPullback d t).toRingHom (actualGraphColonIdeal d t F q)) ∧
        (∀ q : ℕ, actualGraphColonIdeal d t F (N+q) = actualGraphColonIdeal d t F N) ∧
        (∀ g, (∃ q : ℕ, g ∈ actualGraphColonIdeal d t F q) ↔ g ∈ actualGraphColonIdeal d t F N) ∧
        ∃ e : (HolGerm (ComplexModel (deformationDimension d t)) ⧸
            originalCoherentOriginIdeal (originalDeformationIdeal d t F)) ≃+*
          (HolGerm (ComplexModel (graphDimension d t)) ⧸ actualGraphScaledIdeal d t F),
          ∀ g : HolGerm (ComplexModel (deformationDimension d t)),
            e (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ (graphTrace d t g) := by
  let := tangentAlgebra d t
  obtain ⟨Φ, hsrc, h0, hflat, N, U, hU, h0U, hUV, hcol, hchain, hpow, hsat, hB, h0B, hcent, hforward⟩ :=
    exists_original_regular_real_central_initial_ideal_inclusion C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
  let V := (deformationProjection d t) ⁻¹' Φ.target
  have hV : IsOpen V := Φ.isOpen_target.preimage (deformationProjection d t).continuous
  have h0T : (0 : ComplexModel (d+t)) ∈ Φ.target := actualFlattening_target_zero_mem x Φ h0
  have h0V : (0 : ComplexModel (deformationDimension d t)) ∈ V := by
    change deformationProjection d t 0 ∈ Φ.target
    simpa only [map_zero] using h0T
  have hF := coherentOn_actualFlattenedOriginalSheaf A hA x Φ hsrc
  have hIFG := idealFGAt_of_coherentOn F Φ.target hF h0T
  have hpull := coherentOn_pullback_of_local F Φ.target hF V hV (deformationProjection d t)
    (fun _ _ => (deformationProjection d t).differentiableAt.mdifferentiableAt) (fun _ hz => hz)
  have hEq := coherentOn_of_isCoherent (deformationEquationIdeal d t)
    (deformationEquationIdeal_isCoherent d t) V hV
  have hD := coherentOn_sum _ _ V hpull hEq
  have hDFG := idealFGAt_of_coherentOn (originalDeformationIdeal d t F) V hD h0V
  have hpar : HolAt (deformationParameter d t) 0 :=
    Eventually.of_forall fun _ => (deformationParameter d t).differentiableAt
  have hring : ∀ q : ℕ,
      actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t F))
        (deformationParameterGerm d t) (N+q) =
      actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t F))
        (deformationParameterGerm d t) N := by
    intro q
    ext g
    induction g using HolGerm.induction_on with
    | h f hf =>
      change HolGerm.mk f hf ∈ actualOriginColonChain
        (originalCoherentOriginIdeal (originalDeformationIdeal d t F))
        (HolGerm.mk (deformationParameter d t) hpar) (N+q) ↔
        HolGerm.mk f hf ∈ actualOriginColonChain
        (originalCoherentOriginIdeal (originalDeformationIdeal d t F))
        (HolGerm.mk (deformationParameter d t) hpar) N
      rw [← actualColonChain_origin_dictionary_of_local (originalDeformationIdeal d t F) hDFG hpar (N+q) hf,
        ← actualColonChain_origin_dictionary_of_local (originalDeformationIdeal d t F) hDFG hpar N hf]
      exact hchain 0 h0U q f
  have hgraph : ∀ q : ℕ, actualGraphColonIdeal d t F (N+q) = actualGraphColonIdeal d t F N := by
    intro q
    rw [← graphTrace_map_originalOriginColon_of_local d t F hIFG (N+q),
      ← graphTrace_map_originalOriginColon_of_local d t F hIFG N, hring q]
  have hgraphSat : ∀ g, (∃ q : ℕ, g ∈ actualGraphColonIdeal d t F q) ↔
      g ∈ actualGraphColonIdeal d t F N := by
    intro g
    constructor
    · rintro ⟨q, hg⟩
      let G := graphBasePullback d t g
      have hGq : G ∈ actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t F))
          (deformationParameterGerm d t) q := by
        rw [originalOriginColon_eq_graphTrace_comap_of_local d t F hIFG q]
        change graphTrace d t (graphBasePullback d t g) ∈ actualGraphColonIdeal d t F q
        rw [graphTrace_graphBasePullback]
        exact hg
      obtain ⟨f, hf, hG⟩ := HolGerm.exists_eq_mk G
      rw [hG] at hGq
      have hqfunc := (actualColonChain_origin_dictionary_of_local (originalDeformationIdeal d t F) hDFG hpar q hf).mpr hGq
      have hNfunc := (hsat 0 h0U f).mp ⟨q, hqfunc⟩
      have hGN := (actualColonChain_origin_dictionary_of_local (originalDeformationIdeal d t F) hDFG hpar N hf).mp hNfunc
      rw [← hG] at hGN
      change G ∈ actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t F))
        (deformationParameterGerm d t) N at hGN
      rw [originalOriginColon_eq_graphTrace_comap_of_local d t F hIFG N] at hGN
      change graphTrace d t (graphBasePullback d t g) ∈ actualGraphColonIdeal d t F N at hGN
      rwa [graphTrace_graphBasePullback] at hGN
    · exact fun hg => ⟨N, hg⟩
  exact ⟨Φ, hsrc, h0, hflat, N, U, hU, h0U, hUV, hcol, hchain, hpow, hsat, hB, h0B, hcent,
    hforward, fun q => originalCentralOriginIdeal_eq_graphColon_image_of_local d t F hIFG hDFG q,
    hgraph, hgraphSat, originalGraphQuotientEquiv_of_local d t F hIFG,
    fun g => originalGraphQuotientEquiv_apply_mk_of_local d t F hIFG g⟩

end Original
end
end Hironaka.HironakaSmoothCentreRealDomainGraphDictionary
