import Hironaka.Resolution.HironakaActualStrictPullbackSaturation
import Hironaka.Resolution.HironakaActualFixedFlatteningHSComparison

/-! Genuine local finite generation suffices; no global analytic extension of the actual chart model.
Blueprint: hironaka-actual-local-strict-saturation-extension.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualLocalStrictSaturation
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
 RelativePrincipalizationSpan HironakaRelativeNormalAnalyticGraphQuotient
  OkaCoherence HironakaRelativeNormalCoherentSaturation
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan HironakaActualPointGeometricBennett
  HironakaActualPointExceptionalVanishing HironakaActualStrictPullbackSaturation
 HironakaActualAnalyticBlowupTaylor HironakaActualNormalBlowupExceptionalLocus
 HironakaActualStrictExceptionalRegularity HironakaActualStrictRadicalPullback Hironaka.BlowupSequences
 HironakaActualCoefficientPresentationCentrePower
 HironakaActualFixedFlatteningHSComparison HironakaSmoothCentreCoherentDomain
 HironakaSmoothCentreNearbyStalks HironakaRelativeNormalCoherentTranslatedJets
variable {n : ℕ}

theorem mk_mem_origin_iff_of_local_fg {n : ℕ}
    (I : GermIdeal n (ComplexModel n)) (hI : IdealFGAt I.mem (0 : ComplexModel n))
    {f : ComplexModel n → ℂ} (hf : HolAt f 0) :
    HolGerm.mk f hf ∈ originalCoherentOriginIdeal I ↔ I.mem 0 f := by
  classical
  obtain ⟨U,hU,h0U,μ,hμ,s,hs,hsI⟩ := hI
  let := hμ
  have hs0 : ∀ i, HolAt (s i) 0 := fun i => holAt_of_differentiableOn hU (hs i) h0U
  let K := Ideal.span (range fun i => HolGerm.mk (s i) (hs0 i))
  have hdict : ∀ (g : ComplexModel n → ℂ) (hg : HolAt g 0),
      I.mem 0 g ↔ HolGerm.mk g hg ∈ K := fun g hg =>
    (hsI 0 h0U g).trans (inSpanAt_zero_iff_mem_origin_span s hs0 hg)
  have he : originalCoherentOriginIdeal I = K := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro g ⟨a,ha,hIa,rfl⟩
      exact (hdict a ha).mp hIa
    · apply Ideal.span_le.mpr
      rintro g ⟨i,rfl⟩
      apply Ideal.subset_span
      exact ⟨s i,hs0 i,(hsI 0 h0U _).mpr (inSpanAt_self hs0 i),rfl⟩
  rw [he]
  exact (hdict f hf).symm


theorem exists_power_of_local_fg_off_divisor
    (I : GermIdeal n (ComplexModel n)) (hI : IdealFGAt I.mem (0 : ComplexModel n))
    (G : ComplexModel n → ℂ) (hG : HolAt G 0) (e : Fin n)
    (hOff : ∀ᶠ y in 𝓝 (0 : ComplexModel n),y e≠0→I.mem y G) :
    ∃ N : ℕ,(coordinateGerm e)^N*HolGerm.mk G hG∈originalCoherentOriginIdeal I := by
  have hfg := hI
  obtain ⟨U,hU,h0U,μ,hμ,H,hH,hgen⟩ := IdealFGAt.colon (okaProperty_euclidean n) hfg hG
  let := hμ
  let E := Fintype.equivFin μ
  let F := fun j : Fin (Fintype.card μ) => H (E.symm j)
  have hH0 (i : μ) : HolAt (H i) 0 := holAt_of_differentiableOn hU (hH i) h0U
  have hF (i) : HolAt (F i) 0 := hH0 (E.symm i)
  let L := (originalCoherentOriginIdeal I).colon {HolGerm.mk G hG}
  have hmem (i : μ) : HolGerm.mk (H i) (hH0 i)∈L := by
    rw [Submodule.mem_colon_singleton,smul_eq_mul,← HolGerm.mk_mul _ _ (hH0 i) hG]
    apply (mk_mem_origin_iff_of_local_fg I hI _).mpr
    exact ((hgen 0 h0U (H i)).mpr (inSpanAt_self hH0 i)).2
  have hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel n),(∀ i,F i z=0)→z e=0 := by
    filter_upwards [hOff,hU.mem_nhds h0U] with z hz hzU hzF
    by_contra hze
    have hcolon : colonIdeal I.mem G z (fun _ => (1 : ℂ)) := by
      refine ⟨holAt_const 1 z,?_⟩
      simpa only [one_mul] using hz hze
    obtain ⟨_hone,a,_ha,he⟩ := (hgen z hzU (fun _ => (1 : ℂ))).mp hcolon
    have hez := he.self_of_nhds
    have hHz (i : μ) : H i z=0 := by
      simpa only [F,Equiv.symm_apply_apply] using hzF (E i)
    simp only [hHz,mul_zero,Finset.sum_const_zero] at hez
    exact one_ne_zero hez
  have he : HolAt (fun z : ComplexModel n => z e) 0 :=
    Eventually.of_forall fun _ => (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hc : coordinateGerm e∈L.radical := by
    apply RueckertNullstellensatz.vanishingIdeal_le_radical L F (fun i => ⟨hF i,hmem (E.symm i)⟩)
    exact AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr hzero
  obtain ⟨N,hN⟩ := Ideal.mem_radical_iff.mp hc
  exact ⟨N,Submodule.mem_colon_singleton.mp hN⟩


private theorem local_data (I : GermIdeal n (ComplexModel n)) (hI : IdealFGAt I.mem (0 : ComplexModel n)) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ 0∈U ∧ ∃ N : ℕ,∃ S : Fin N → ComplexModel n → ℂ,
      (∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (S i) U) ∧
      ∀ y∈U,∀g,I.mem y g ↔ IsInSpanAt (n := n) (·∈range S) y g := by
  obtain ⟨U,hU,h0,μ,hμ,s,hs,hgen⟩ := hI
  let := hμ
  let E := Fintype.equivFin μ
  let S := fun i => s (E.symm i)
  refine ⟨U,hU,h0,Fintype.card μ,S,fun i => mdifferentiableOn_iff_differentiableOn.mpr (hs _),?_⟩
  intro y hy g
  rw [hgen y hy g,←CoherentIdealColon.inSpanAt_comp_equiv E.symm s y g,
    CoherentIdealColon.isInSpanAt_range_iff]
  constructor
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h => h.mdifferentiableAt),a,fun i => (ha i).mono (fun _ h => h.mdifferentiableAt),he⟩
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h => h.differentiableAt),a,fun i => (ha i).mono (fun _ h => h.differentiableAt),he⟩

theorem local_fg_pullback (η : ComplexModel n → ComplexModel n)
    (hη : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ η) (hη0 : η 0=0)
    (I : GermIdeal n (ComplexModel n)) (hI : IdealFGAt I.mem (0 : ComplexModel n)) :
    IdealFGAt (GermIdeal.pullback (m := n) η I).mem (0 : ComplexModel n) := by
  obtain ⟨U,hU,h0,N,S,hS,hgen⟩ := local_data I hI
  have hfat : ∀ {z : ComplexModel n},∀ᶠ z' in 𝓝 z,
      ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ η z' :=
    fun {_} => Eventually.of_forall fun _ => hη.contMDiffAt
  have hshol : ∀ i:Fin N,∀x∈U,HolomorphicAt n (S i) x := fun i x hx =>
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hS i) hx
  have hcomp : ∀ i:Fin N,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (S i ∘ η) (η ⁻¹' U) := by
    intro i z hz
    exact ((hshol i (η z) hz).comp_contMDiff hfat).mdifferentiableAt.mdifferentiableWithinAt
  refine ⟨η ⁻¹' U,hU.preimage hη.continuous,by simpa only[mem_preimage,hη0] using h0,
    Fin N,inferInstance,fun i => S i ∘ η,fun i => mdifferentiableOn_iff_differentiableOn.mp (hcomp i),?_⟩
  intro z hz g
  have hdict : (GermIdeal.pullback (m := n) η I).mem z g ↔
      IsInSpanAt (n := n) (·∈range fun i => S i ∘ η) z g := by
    constructor
    · intro hg
      refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
      rintro t ⟨a,ha,rfl⟩
      refine IsInSpanAt.mono ?_ (GermIdealPullbackCalculus.isInSpanAt_comp hη ((hgen (η z) hz a).mp ha))
      rintro s' ⟨σ,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · intro hg
      refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hg)
      rintro s' ⟨i,rfl⟩
      exact ⟨S i,(hgen (η z) hz (S i)).mpr (InvertibleIdealQuotient.isInSpanAt_self
        ⟨i,rfl⟩ (hshol i (η z) hz)),rfl⟩
  rw [hdict,CoherentIdealColon.isInSpanAt_range_iff]
  constructor
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h => h.differentiableAt),a,fun i => (ha i).mono (fun _ h => h.differentiableAt),he⟩
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h => h.mdifferentiableAt),a,fun i => (ha i).mono (fun _ h => h.mdifferentiableAt),he⟩
theorem local_origin_pullback_eq (η : ComplexModel n → ComplexModel n)
    (hη : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ η) (hη0 : η 0=0)
    (I : GermIdeal n (ComplexModel n)) (hI : IdealFGAt I.mem (0 : ComplexModel n)) :
    originalCoherentOriginIdeal (GermIdeal.pullback (m := n) η I)=
      Ideal.map (actualHolomorphicOriginPullback η hη hη0).toRingHom (originalCoherentOriginIdeal I) := by
  have hp : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ η z :=
    Eventually.of_forall fun z => (hη.contMDiffAt (x := z)).mdifferentiableAt (by simp) |>.differentiableAt
  have hJ := local_fg_pullback η hη hη0 I hI
  obtain ⟨U,hU,h0,μ,hμ,S,hS,hgen⟩ := hI
  let := hμ
  have hhol (a : ComplexModel n → ℂ) (ha : I.mem 0 a) : HolAt a 0 := ((hgen 0 h0 a).mp ha).1
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hIf,rfl⟩
    let S := fun s : ComplexModel n → ℂ => ∃ a,I.mem (η 0) a ∧ s=a∘η
    have hS : ∀ s,S s→HolAt s 0 := by
      rintro _ ⟨a,ha,rfl⟩
      have ha0 : I.mem 0 a := by simpa only [hη0] using ha
      exact holomorphic_comp η hp hη0 (hhol a ha0)
    apply whole_origin_span_mem _ S hS ?_ hf hIf
    rintro s ⟨a,ha,rfl⟩
    have ha0 : I.mem 0 a := by simpa only [hη0] using ha
    have hah : HolAt a 0 := hhol a ha0
    change HolGerm.mk (a∘η) _∈Ideal.map (compAlgHom η hp hη0).toRingHom (originalCoherentOriginIdeal I)
    rw [← compAlgHom_mk η hp hη0 a hah]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a,hah,ha0,rfl⟩)
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hIf,rfl⟩
    change compAlgHom η hp hη0 (HolGerm.mk f hf)∈originalCoherentOriginIdeal (GermIdeal.pullback (m := n) η I)
    rw [compAlgHom_mk]
    have hc := holomorphic_comp η hp hη0 hf
    apply (mk_mem_origin_iff_of_local_fg _ hJ hc).mpr
    refine ⟨hc.mono (fun _ h => h.mdifferentiableAt),1,fun _ => f∘η,fun _ _ => 1,?_,?_,?_⟩
    · exact fun _ => ⟨f,by simpa only [hη0] using hIf,rfl⟩
    · exact fun _ => Eventually.of_forall fun _ => mdifferentiableAt_const
    · exact Eventually.of_forall fun _ => by simp


private theorem local_contMDiff_blowup (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualAnalyticBlowupMap A e b) := by
  have hp (i : Fin n) : ContDiff ℂ ∞ (fun z : ComplexModel n => z i) :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).contDiff
  have hc (i : Fin n) : ContDiff ℂ ∞ (actualAnalyticBlowupCoordinate A e b i) := by
    unfold actualAnalyticBlowupCoordinate
    split_ifs
    · exact hp e
    · exact (hp e).mul ((contDiff_const (c := b i)).add (hp i))
    · exact hp i
  exact ((EuclideanSpace.equiv (Fin n) ℂ).symm.contDiff.comp (contDiff_pi.mpr hc)).contMDiff


theorem mem_strict_ideal_iff_power_of_local_fg
    (d t : ℕ) (ht : 2≤t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t))) (hW : IdealFGAt (vanishingIdeal (n := d+t) W).mem (0 : ComplexModel (d+t)))
    (g : HolGerm (ComplexModel (d+t))) :
    g∈originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) ↔
      ∃ N : ℕ,(coordinateGerm (j.natAdd d))^N*g∈
        Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom
          (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) := by
  let A := actualTangentCentreVariables d t
  let e := j.natAdd d
  let π := actualAnalyticBlowupMap A e b
  let I := vanishingIdeal (n := d+t) W
  let J := GermIdeal.pullback (m := d+t) π I
  have hI : IdealFGAt I.mem (0 : ComplexModel (d+t)) := hW
  have hπ := local_contMDiff_blowup A e b
  have hπ0 : π 0=0 := actualAnalyticBlowupMap_zero A e b
  have hJ : IdealFGAt J.mem (0 : ComplexModel (d+t)) := local_fg_pullback π hπ hπ0 I hI
  have hmap : originalCoherentOriginIdeal J=
      Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom (originalCoherentOriginIdeal I) := by
    exact local_origin_pullback_eq π hπ hπ0 I hI
  have hπnear : ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)),DifferentiableAt ℂ π z :=
    Eventually.of_forall fun _ => (differentiable_actualAnalyticBlowupMap A e b).differentiableAt
  have htπ : Tendsto π (𝓝 (0 : ComplexModel (d+t))) (𝓝 (0 : ComplexModel (d+t))) := by
    have h : Tendsto π (𝓝 (0 : ComplexModel (d+t))) (𝓝 (π 0)) := hπ.continuous.tendsto 0
    rwa [hπ0] at h
  constructor
  · intro hg
    obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
    have hzero := (mk_mem_original_vanishing_origin_ideal_iff _ G hG).mp hg
    obtain ⟨U,hUprop,hU,h0U⟩ := eventually_nhds_iff.mp (hG.and hzero)
    have hOff : ∀ᶠ y in 𝓝 (0 : ComplexModel (d+t)),y e≠0→J.mem y G := by
      filter_upwards [hU.mem_nhds h0U] with y hy hye
      apply (pullback_vanishingIdeal_mem_iff_off_coordinate A e b W y hye G).mpr
      have hGU : DifferentiableOn ℂ G U := fun z hz => (hUprop z hz).1.differentiableWithinAt
      refine ⟨(holAt_of_differentiableOn hU hGU hy).mono (fun _ h => h.mdifferentiableAt),?_⟩
      filter_upwards [hU.mem_nhds hy,
        (EuclideanSpace.proj e : ComplexModel (d+t) →L[ℂ] ℂ).continuous.continuousAt.eventually_ne hye]
        with z hz hze hzW
      apply (hUprop z hz).2
      rw [strictTransform,exceptionalLocus_actual_normal_blowup_eq d t ht j b]
      exact subset_closure ⟨hzW,hze⟩
    obtain ⟨N,hN⟩ := exists_power_of_local_fg_off_divisor J hJ G hG e hOff
    exact ⟨N,by rwa [hmap] at hN⟩
  · rintro ⟨N,hN⟩
    apply (coordinate_pow_mul_mem_geometric_strict_ideal_iff d t ht j b W N g).mp
    have hle : Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom (originalCoherentOriginIdeal I)≤
        originalCoherentOriginIdeal (vanishingIdeal (n := d+t) (strictTransform (d+t) π W)) := by
      apply Ideal.map_le_iff_le_comap.mpr
      apply Ideal.span_le.mpr
      rintro _ ⟨F,hF,hFW,rfl⟩
      change actualAnalyticBlowupPullback A e b (HolGerm.mk F hF)∈
        originalCoherentOriginIdeal (vanishingIdeal (n := d+t) (strictTransform (d+t) π W))
      rw [actualAnalyticBlowupPullback,compAlgHom_mk]
      apply (mk_mem_original_vanishing_origin_ideal_iff _ (F∘π) _).mpr
      apply eventually_zero_on_closure_of_eventually_continuous (F∘π)
        (π ⁻¹' W\exceptionalLocus (d+t) π)
        ((holomorphic_comp π hπnear hπ0 hF).mono fun _ h => h.continuousAt)
      filter_upwards [htπ.eventually hFW.2] with z hz hzS
      exact hz hzS.1
    exact hle hN


section Original
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem fixedFlattening_vanishing_local_fg (W : Set M)
    (hW : (vanishingIdeal (n := n) W).IsCoherent) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    IdealFGAt (vanishingIdeal (n := n) (actualFixedFlatteningSet x Φ W)).mem
      (0 : ComplexModel n) := by
  have hcoh := coherentOn_actualFlattenedOriginalSheaf
    (vanishingIdeal (n := n) W) hW x Φ hsrc
  obtain ⟨U,hU,h0U,hUT,N,S,hS,hgen⟩ := hcoh 0 (actualFlattening_target_zero_mem x Φ h0)
  refine ⟨U,hU,h0U,Fin N,inferInstance,S,
    fun i => mdifferentiableOn_iff_differentiableOn.mp (hS i),?_⟩
  intro y hy g
  rw [←flattened_vanishing_mem_iff x Φ hsrc W y (hUT hy),hgen y hy g,
    CoherentIdealColon.isInSpanAt_range_iff]
  constructor
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h => h.differentiableAt),a,
      fun i => (ha i).mono (fun _ h => h.differentiableAt),he⟩
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h => h.mdifferentiableAt),a,
      fun i => (ha i).mono (fun _ h => h.mdifferentiableAt),he⟩
end Original

section OriginalNormal
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

theorem mem_fixedFlattening_strict_iff_power (ht : 2≤t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set M) (hW : (vanishingIdeal (n := d+t) W).IsCoherent) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0)
    (g : HolGerm (ComplexModel (d+t))) :
    g∈originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
        (actualFixedFlatteningSet x Φ W))) ↔
      ∃ N : ℕ,(coordinateGerm (j.natAdd d))^N*g∈
        Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (actualFlattenedOriginalSheaf (vanishingIdeal (n := d+t) W) x Φ) 0)) := by
  rw [originalFlattenedVanishingOriginIdeal_eq_model x Φ hsrc h0]
  exact mem_strict_ideal_iff_power_of_local_fg d t ht j b (actualFixedFlatteningSet x Φ W)
    (fixedFlattening_vanishing_local_fg W hW x Φ hsrc h0) g
end OriginalNormal

end
end Hironaka.HironakaActualLocalStrictSaturation
