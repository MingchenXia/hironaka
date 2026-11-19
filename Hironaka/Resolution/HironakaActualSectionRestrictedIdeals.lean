import Hironaka.Resolution.HironakaActualSectionBoundaryDimension
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSectionRestrictedIdeals
noncomputable section
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient
open HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
 HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
variable {n m : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}
 {V : TopologicalSpace.Opens (ComplexModel m)}

theorem restrictedSpan_comp {f : U→V}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    {A : Set V} {B : Set U} (hAB : B⊆f ⁻¹' A)
    {S : (V→ℂ)→Prop} {x : U} {g : V→ℂ}
    (hg : IsInSpanOnAt (n := m) A S (f x) g) :
    IsInSpanOnAt (n := n) B (fun t => ∃s, S s ∧ t=s ∘ f) x (g ∘ f) := by
  obtain ⟨K,s,c,hs,hc,he⟩:=hg
  refine ⟨K,fun i => s i ∘ f,fun i => c i ∘ f,fun i => ⟨s i,hs i,rfl⟩,
    fun i => (hc i).comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt),?_⟩
  filter_upwards [hf.continuous.continuousAt.eventually he] with y hy hyB
  exact hy (hAB hyB)

private theorem projection_section (x : U) : projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x

private theorem section_projection {A : Set U} (z : productOpen U) (hz : z∈liftedCarrier A) :
    zeroSection U (projection U z)=z := by
  apply Subtype.ext
  change tangentInclusion n 1 (tangentProjection n 1 z.val)=z.val
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hz.2,map_zero,add_zero] using
    (join_projections (n := n) (m := 1) z.val)

theorem restrictedSpan_section_iff (A : Set U) (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀z g,J.mem z g → HolomorphicAt (n+1) g z) (x : U)
    (g : productOpen U→ℂ) :
    IsInSpanOnAt (n := n+1) (liftedCarrier A) (J.mem (zeroSection U x)) (zeroSection U x) g ↔
    IsInSpanOnAt (n := n) A ((GermIdeal.pullback (m := n) (zeroSection U) J).mem x) x (g ∘ zeroSection U) := by
  have hLift : A⊆zeroSection U ⁻¹' liftedCarrier A := by
    intro y hy
    exact ⟨by simpa only [projection_section] using hy,by change actualJointNormalProjection n 1 (tangentInclusion n 1 y)=0; simp⟩
  constructor
  · intro h
    apply IsInSpanOnAt.mono ?_ (restrictedSpan_comp (zeroSection_contMDiff U) hLift h)
    rintro _ ⟨a,ha,rfl⟩
    exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨a,ha,rfl⟩
      ((hJ _ _ ha).comp_contMDiff (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt)))
  · intro h
    have hh : IsInSpanOnAt (n := n) A
        (fun t => ∃a, J.mem (zeroSection U x) a ∧ t=a ∘ zeroSection U) x (g ∘ zeroSection U) :=
      IsInSpanOnAt.trans (fun _ ha => IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp ha)) h
    obtain ⟨K,s,c,hs,hc,he⟩:=hh
    choose a ha has using hs
    refine ⟨K,a,fun i => c i ∘ projection U,ha,
      fun i => ?_,?_⟩
    · have hp : projection U (zeroSection U x)=x:=projection_section x
      have hc' : HolomorphicAt n (c i) (projection U (zeroSection U x)) := by simpa only [hp] using hc i
      exact hc'.comp_contMDiff
        (Eventually.of_forall fun _ => (projection_contMDiff U).contMDiffAt)
    · have ht : Tendsto (projection U) (𝓝 (zeroSection U x)) (𝓝 x) := by
        simpa only [projection_section] using (projection_contMDiff U).continuous.tendsto (zeroSection U x)
      filter_upwards [ht.eventually he] with z hz hzA
      have hv:=hz hzA.1
      simpa only [Function.comp_apply,has,section_projection z hzA] using hv
open RestrictedIdealExtension GermIdealOrder IdealWeightPowers

theorem pullback_section_restrictOn (A : Set U) (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀z g,J.mem z g → HolomorphicAt (n+1) g z) :
    GermIdeal.pullback (m := n) (zeroSection U) (restrictOn (n+1) (liftedCarrier A) J)=
      restrictOn n A (GermIdeal.pullback (m := n) (zeroSection U) J) := by
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro hg
    apply restrictOn_of_isInSpanAt
    apply IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨ha.1.comp_contMDiff (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt),
      (restrictedSpan_section_iff A J hJ x a).mp ha.2⟩
  · intro hg
    have he : (g ∘ projection U) ∘ zeroSection U=g := by
      funext y
      simp only [Function.comp_apply,projection_section]
    have hh : HolomorphicAt (n+1) (g ∘ projection U) (zeroSection U x) := by
      have hx : HolomorphicAt n g (projection U (zeroSection U x)) := by
        simpa only [projection_section] using hg.1
      exact hx.comp_contMDiff (Eventually.of_forall fun _ => (projection_contMDiff U).contMDiffAt)
    have hs : (restrictOn (n+1) (liftedCarrier A) J).mem (zeroSection U x) (g ∘ projection U) :=
      ⟨hh,(restrictedSpan_section_iff A J hJ x (g ∘ projection U)).mpr (by rw [he];exact hg.2)⟩
    apply GermIdeal.mem_pullback_iff.mpr
    apply isInSpanAt_self ?_ hg.1
    exact ⟨g ∘ projection U,hs,he.symm⟩

open RestrictedIdealQuotient

theorem colonAlong_section_mem_iff (A : Set U) (I L : GermIdeal (n+1) (productOpen U))
    (hI : ∀z g,I.mem z g → HolomorphicAt (n+1) g z)
    (hL : ∀z g,L.mem z g → HolomorphicAt (n+1) g z)
    (x : U) (h : productOpen U→ℂ) (hh : HolomorphicAt (n+1) h (zeroSection U x)) :
    (colonAlong (n+1) (liftedCarrier A) I L).mem (zeroSection U x) h ↔
    (colonAlong n A (GermIdeal.pullback (m := n) (zeroSection U) I)
      (GermIdeal.pullback (m := n) (zeroSection U) L)).mem x (h ∘ zeroSection U) := by
  have hhB : HolomorphicAt n (h ∘ zeroSection U) x :=
    hh.comp_contMDiff (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt)
  constructor
  · intro hm
    refine ⟨hhB,?_⟩
    intro b hb
    obtain ⟨hbhol,K,s,c,hs,hc,he⟩:=GermIdeal.mem_pullback_iff.mp hb
    choose a ha has using hs
    apply restrictOn_of_isInSpanAt
    refine ⟨hbhol.mul hhB,K,fun i => (fun z => a i z*h z) ∘ zeroSection U,c,?_,hc,?_⟩
    · intro i
      have hi:=(hm.2 (a i) (ha i)).2
      exact ⟨((hL _ _ (ha i)).mul hh).comp_contMDiff
        (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt),
        (restrictedSpan_section_iff A I hI x (fun z => a i z*h z)).mp hi⟩
    · filter_upwards [he] with y hy
      change b y*h (zeroSection U y)=_
      rw [hy,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [has,Function.comp_apply]
      ring
  · intro hm
    refine ⟨hh,?_⟩
    intro a ha
    have hb : (GermIdeal.pullback (m := n) (zeroSection U) L).mem x (a ∘ zeroSection U) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨a,ha,rfl⟩
        ((hL _ _ ha).comp_contMDiff (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt)))
    have ht:=(hm.2 (a ∘ zeroSection U) hb).2
    exact ⟨(hL _ _ ha).mul hh,
      (restrictedSpan_section_iff A I hI x (fun z => a z*h z)).mpr ht⟩

private theorem colonAlong_of_span {A : Set U} {I L : GermIdeal n U} {x : U} {g : U→ℂ}
    (hg : IsInSpanAt (n := n) ((colonAlong n A I L).mem x) x g) :
    (colonAlong n A I L).mem x g := by
  obtain ⟨hhol,K,s,c,hs,hc,he⟩:=hg
  refine ⟨hhol,?_⟩
  intro a ha
  apply restrictOn_of_isInSpanAt
  have has : ∀i, (restrictOn n A I).mem x (fun y => a y*s i y) := fun i => (hs i).2 a ha
  have haHol : HolomorphicAt n (fun y => a y*g y) x := by
    have hex : IsInSpanAt (n := n) ((restrictOn n A I).mem x) x (fun y => a y*g y) := by
      refine ⟨?_,K,fun i y => a y*s i y,c,has,hc,?_⟩
      · have hcspan : IsInSpanAt (n := n) ((restrictOn n A I).mem x) x
            (fun y => ∑i, c i y*(a y*s i y)) :=
          IsInSpanAt.sum Finset.univ fun i _ => IsInSpanAt.mul_left (hc i)
            (isInSpanAt_self (has i) (has i).1)
        apply HolomorphicAt.congr hcspan.holomorphicAt
        filter_upwards [he] with y hy
        rw [hy,Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      · filter_upwards [he] with y hy
        rw [hy,Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    exact hex.holomorphicAt
  refine ⟨haHol,K,fun i y => a y*s i y,c,has,hc,?_⟩
  filter_upwards [he] with y hy
  rw [hy,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem pullback_section_colonAlong (A : Set U) (I L : GermIdeal (n+1) (productOpen U))
    (hI : ∀z g,I.mem z g → HolomorphicAt (n+1) g z)
    (hL : ∀z g,L.mem z g → HolomorphicAt (n+1) g z) :
    GermIdeal.pullback (m := n) (zeroSection U) (colonAlong (n+1) (liftedCarrier A) I L)=
      colonAlong n A (GermIdeal.pullback (m := n) (zeroSection U) I)
        (GermIdeal.pullback (m := n) (zeroSection U) L) := by
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro hg
    apply colonAlong_of_span
    apply IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    exact (colonAlong_section_mem_iff A I L hI hL x a ha.1).mp ha
  · intro hg
    have he : (g ∘ projection U) ∘ zeroSection U=g := by
      funext y
      simp only [Function.comp_apply,projection_section]
    have hh : HolomorphicAt (n+1) (g ∘ projection U) (zeroSection U x) := by
      have hx : HolomorphicAt n g (projection U (zeroSection U x)) := by
        simpa only [projection_section] using hg.1
      exact hx.comp_contMDiff (Eventually.of_forall fun _ => (projection_contMDiff U).contMDiffAt)
    have hs : (colonAlong (n+1) (liftedCarrier A) I L).mem (zeroSection U x) (g ∘ projection U) :=
      (colonAlong_section_mem_iff A I L hI hL x (g ∘ projection U) hh).mpr (by rw [he];exact hg)
    apply GermIdeal.mem_pullback_iff.mpr
    apply isInSpanAt_self ?_ hg.1
    exact ⟨g ∘ projection U,hs,he.symm⟩

theorem pullback_section_boundary_vanishing (H : Set U) :
    GermIdeal.pullback (m := n) (zeroSection U) (vanishingIdeal (n := n+1) (projection U ⁻¹' H))=
      vanishingIdeal (n := n) H := by
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro hg
    apply DerivativeIdealAlong.vanishingIdeal_mem_of_isInSpanAt
    apply IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    refine ⟨ha.1.comp_contMDiff (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt),?_⟩
    filter_upwards [(zeroSection_contMDiff U).continuous.continuousAt.eventually ha.2] with y hy hyH
    exact hy (by simpa only [Set.mem_preimage,projection_section] using hyH)
  · intro hg
    have he : (g ∘ projection U) ∘ zeroSection U=g := by
      funext y
      simp only [Function.comp_apply,projection_section]
    have hh : HolomorphicAt (n+1) (g ∘ projection U) (zeroSection U x) := by
      have hx : HolomorphicAt n g (projection U (zeroSection U x)) := by
        simpa only [projection_section] using hg.1
      exact hx.comp_contMDiff (Eventually.of_forall fun _ => (projection_contMDiff U).contMDiffAt)
    have hp : Tendsto (projection U) (𝓝 (zeroSection U x)) (𝓝 x) := by
      simpa only [projection_section] using (projection_contMDiff U).continuous.tendsto (zeroSection U x)
    have hs : (vanishingIdeal (n := n+1) (projection U ⁻¹' H)).mem (zeroSection U x) (g ∘ projection U) :=
      ⟨hh,hp.eventually hg.2⟩
    exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g ∘ projection U,hs,he.symm⟩ hg.1)

theorem pullback_section_boundary_power (H : Set U) (e : ℕ) :
    GermIdeal.pullback (m := n) (zeroSection U)
        (idealPow (vanishingIdeal (n := n+1) (projection U ⁻¹' H)) e)=
      idealPow (vanishingIdeal (n := n) H) e := by
  rw [HironakaActualNonregularCoefficientNaturality.pullback_idealPow (zeroSection_contMDiff U)
    (I := vanishingIdeal (n := n+1) (projection U ⁻¹' H))
    (fun hg => hg.1),pullback_section_boundary_vanishing]

open MonomialPartAlong HironakaActualSectionBoundaryDimension DivisorExponentAlong

theorem monomialPartAlong_section_mem_iff (A : Set U) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀z g,J.mem z g → HolomorphicAt (n+1) g z)
    (x : U) (g : productOpen U→ℂ) (hg : HolomorphicAt (n+1) g (zeroSection U x)) :
    (monomialPartAlong (n+1) (liftedCarrier A) J (E.map (projection U ⁻¹' ·))).mem (zeroSection U x) g ↔
    (monomialPartAlong n A (GermIdeal.pullback (m := n) (zeroSection U) J) E).mem x (g ∘ zeroSection U) := by
  have hA : zeroSection U x∈liftedCarrier A ↔ x∈A := by
    change (projection U (zeroSection U x)∈A ∧ _=0) ↔ x∈A
    simp only [projection_section]
    simp [zeroSection]
  have hd (H : Set U) : divExpAlong (n+1) (liftedCarrier A) J (projection U ⁻¹' H) (zeroSection U x)=
      divExpAlong n A (GermIdeal.pullback (m := n) (zeroSection U) J) H x :=
    divExpAlong_section_eq A H J hJ x
  constructor
  · intro hm
    refine ⟨hg.comp_contMDiff (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt),?_⟩
    intro i hxA hxi
    let i' : Fin (E.map (projection U ⁻¹' ·)).length := ⟨i.val,by simp only [List.length_map]; exact i.isLt⟩
    have hi : (E.map (projection U ⁻¹' ·)).get i'=projection U ⁻¹' E.get i := by simp [i']
    have hs:=hm.2 i' (hA.mpr hxA) (by simp only [hi,Set.mem_preimage,projection_section]; exact hxi)
    rw [hi,hd] at hs
    have hh:=(restrictedSpan_section_iff A
      (idealPow (vanishingIdeal (n := n+1) (projection U ⁻¹' E.get i))
        (divExpAlong n A (GermIdeal.pullback (m := n) (zeroSection U) J) (E.get i) x))
      (fun _ _ h => GermIdealOrder.holomorphicAt_of_mem_idealPow h) x g).mp hs
    rw [pullback_section_boundary_power] at hh
    exact hh
  · intro hm
    refine ⟨hg,?_⟩
    intro i hxA hxi
    let i' : Fin E.length := ⟨i.val,by simpa using i.isLt⟩
    have hi : (E.map (projection U ⁻¹' ·)).get i=projection U ⁻¹' E.get i' := by simp [i']
    rw [hi,hd]
    apply (restrictedSpan_section_iff A
      (idealPow (vanishingIdeal (n := n+1) (projection U ⁻¹' E.get i'))
        (divExpAlong n A (GermIdeal.pullback (m := n) (zeroSection U) J) (E.get i') x))
      (fun _ _ h => GermIdealOrder.holomorphicAt_of_mem_idealPow h) x g).mpr
    rw [pullback_section_boundary_power]
    exact hm.2 i' (hA.mp hxA) (by simpa only [hi,Set.mem_preimage,projection_section] using hxi)

private theorem monomialPartAlong_of_span {A : Set U} {I : GermIdeal n U} {E : List (Set U)}
    {x : U} {g : U→ℂ}
    (hg : IsInSpanAt (n := n) ((monomialPartAlong n A I E).mem x) x g) :
    (monomialPartAlong n A I E).mem x g := by
  refine ⟨hg.holomorphicAt,?_⟩
  intro i hxA hxi
  exact IsInSpanOnAt.trans (fun _ hs => hs.2 i hxA hxi) (IsInSpanAt.restrict hg)

theorem pullback_section_monomialPartAlong (A : Set U) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀z g,J.mem z g → HolomorphicAt (n+1) g z) :
    GermIdeal.pullback (m := n) (zeroSection U)
      (monomialPartAlong (n+1) (liftedCarrier A) J (E.map (projection U ⁻¹' ·)))=
    monomialPartAlong n A (GermIdeal.pullback (m := n) (zeroSection U) J) E := by
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro hg
    apply monomialPartAlong_of_span
    apply IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    exact (monomialPartAlong_section_mem_iff A E J hJ x a ha.1).mp ha
  · intro hg
    have he : (g ∘ projection U) ∘ zeroSection U=g := by
      funext y
      simp only [Function.comp_apply,projection_section]
    have hh : HolomorphicAt (n+1) (g ∘ projection U) (zeroSection U x) := by
      have hx : HolomorphicAt n g (projection U (zeroSection U x)) := by
        simpa only [projection_section] using hg.1
      exact hx.comp_contMDiff (Eventually.of_forall fun _ => (projection_contMDiff U).contMDiffAt)
    have hs : (monomialPartAlong (n+1) (liftedCarrier A) J (E.map (projection U ⁻¹' ·))).mem
        (zeroSection U x) (g ∘ projection U) :=
      (monomialPartAlong_section_mem_iff A E J hJ x (g ∘ projection U) hh).mpr (by rw [he];exact hg)
    exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g ∘ projection U,hs,he.symm⟩ hg.1)

theorem pullback_section_nonmonomialPartAlong (A : Set U) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀z g,J.mem z g → HolomorphicAt (n+1) g z) :
    GermIdeal.pullback (m := n) (zeroSection U)
      (nonmonomialPartAlong (n+1) (liftedCarrier A) J (E.map (projection U ⁻¹' ·)))=
    nonmonomialPartAlong n A (GermIdeal.pullback (m := n) (zeroSection U) J) E := by
  unfold nonmonomialPartAlong
  rw [pullback_section_colonAlong A J
      (monomialPartAlong (n+1) (liftedCarrier A) J (E.map (projection U ⁻¹' ·)))
      hJ (fun _ _ hg => hg.1),
    pullback_section_monomialPartAlong A E J hJ]

end
end Hironaka.HironakaActualSectionRestrictedIdeals
