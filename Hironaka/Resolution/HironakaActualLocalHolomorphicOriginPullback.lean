import Hironaka.Resolution.HironakaActualLocalStrictSaturation

/-! True local holomorphic maps preserve local finite generation and the
ENTIRE original origin ideal under the literal germ-sheaf pullback. No
holomorphic extension outside a genuine neighborhood is assumed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualLocalHolomorphicOriginPullback
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
 HironakaHolomorphicJetChartInvariance HironakaActualLocalStrictSaturation
 HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalDeformationInitialRelations
 HironakaRelativeNormalCoherentTranslatedJets GermIdealPullbackCalculus
 HironakaActualStrictPullbackSaturation OkaIdealOperations RelativePrincipalizationSpan
 HironakaRelativeNormalAnalyticGraphQuotient OkaCoherence
variable {n : ℕ}

private theorem holomorphicAt_comp_local
    (η : ComplexModel n → ComplexModel n) (z : ComplexModel n)
    (hη : ∀ᶠy in 𝓝 z,DifferentiableAt ℂ η y)
    (f : ComplexModel n → ℂ) (hf : HolomorphicAt n f (η z)) :
    HolomorphicAt n (f ∘ η) z := by
  filter_upwards [hη,hη.self_of_nhds.continuousAt.tendsto.eventually hf] with y hy hfy
  exact hfy.comp y hy.mdifferentiableAt

private theorem span_comp_local
    (η : ComplexModel n → ComplexModel n) (z : ComplexModel n)
    (hη : ∀ᶠy in 𝓝 z,DifferentiableAt ℂ η y)
    {S : (ComplexModel n → ℂ) → Prop} {c : ComplexModel n → ℂ}
    (hc : IsInSpanAt (n:=n) S (η z) c) :
    IsInSpanAt (n:=n) (fun s=>∃a,S a ∧ s=a ∘ η) z (c ∘ η) := by
  obtain ⟨hchol,N,s,a,hs,ha,hsum⟩:=hc
  refine ⟨holomorphicAt_comp_local η z hη c hchol,N,fun i=>s i ∘ η,fun i=>a i ∘ η,
    fun i=>⟨s i,hs i,rfl⟩,fun i=>holomorphicAt_comp_local η z hη (a i) (ha i),?_⟩
  exact hη.self_of_nhds.continuousAt.tendsto.eventually hsum

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


/-- The actual pullback of a source locally finitely generated at zero is
locally finitely generated there for a map holomorphic ONLY near zero. -/
theorem local_fg_pullback_of_holomorphic_germ (η : ComplexModel n → ComplexModel n)
    (hη : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ η z) (hη0 : η 0=0)
    (I : GermIdeal n (ComplexModel n)) (hI : IdealFGAt I.mem (0 : ComplexModel n)) :
    IdealFGAt (GermIdeal.pullback (m:=n) η I).mem (0 : ComplexModel n) := by
  obtain ⟨U,hU,h0,N,S,hS,hgen⟩:=local_data I hI
  obtain ⟨O,hOD,hOo,h0O⟩:=mem_nhds_iff.mp hη
  have hηO : DifferentiableOn ℂ η O:=fun z hz=>(hOD hz).differentiableWithinAt
  let V:=O∩η ⁻¹' U
  have hV : IsOpen V:=hηO.continuousOn.isOpen_inter_preimage hOo hU
  have h0V : (0 : ComplexModel n)∈V:=⟨h0O,by simpa only [mem_preimage,hη0] using h0⟩
  have hηnear (z : ComplexModel n) (hz : z∈V) : ∀ᶠy in 𝓝 z,DifferentiableAt ℂ η y := by
    have hO : ∀ᶠy in 𝓝 z,y∈O:=hOo.mem_nhds hz.1
    exact hO.mono fun y hy=>hOD hy
  have hshol (i : Fin N) (z : ComplexModel n) (hz : z∈U) : HolomorphicAt n (S i) z:=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hS i) hz
  have hcomp : ∀i : Fin N,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (S i ∘ η) V := by
    intro i z hz
    exact (holomorphicAt_comp_local η z (hηnear z hz) (S i) (hshol i (η z) hz.2)).self_of_nhds.mdifferentiableWithinAt
  refine ⟨V,hV,h0V,Fin N,inferInstance,fun i=>S i ∘ η,
    fun i=>mdifferentiableOn_iff_differentiableOn.mp (hcomp i),?_⟩
  intro z hz g
  have hdict : (GermIdeal.pullback (m:=n) η I).mem z g ↔
      IsInSpanAt (n:=n) (·∈range fun i=>S i ∘ η) z g := by
    constructor
    · intro hg
      refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
      rintro t ⟨a,ha,rfl⟩
      refine IsInSpanAt.mono ?_ (span_comp_local η z (hηnear z hz) ((hgen (η z) hz.2 a).mp ha))
      rintro s' ⟨σ,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · intro hg
      refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hg)
      rintro s' ⟨i,rfl⟩
      exact ⟨S i,(hgen (η z) hz.2 (S i)).mpr
        (InvertibleIdealQuotient.isInSpanAt_self ⟨i,rfl⟩ (hshol i (η z) hz.2)),rfl⟩
  rw [hdict,CoherentIdealColon.isInSpanAt_range_iff]
  constructor
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h=>h.differentiableAt),a,fun i=>(ha i).mono (fun _ h=>h.differentiableAt),he⟩
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h=>h.mdifferentiableAt),a,fun i=>(ha i).mono (fun _ h=>h.mdifferentiableAt),he⟩

theorem origin_pullback_eq_of_holomorphic_germ (η : ComplexModel n → ComplexModel n)
    (hη : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ η z) (hη0 : η 0=0)
    (I : GermIdeal n (ComplexModel n)) (hI : IdealFGAt I.mem (0 : ComplexModel n)) :
    originalCoherentOriginIdeal (GermIdeal.pullback (m := n) η I)=
      Ideal.map (compAlgHom η hη hη0).toRingHom (originalCoherentOriginIdeal I) := by
  have hp : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ η z :=
    hη
  have hJ := local_fg_pullback_of_holomorphic_germ η hη hη0 I hI
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


end
end Hironaka.HironakaActualLocalHolomorphicOriginPullback
