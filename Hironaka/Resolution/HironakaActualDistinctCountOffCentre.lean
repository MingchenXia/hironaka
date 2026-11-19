import Hironaka.Resolution.HironakaG4DistinctResidualCountTransform

/-! Actual off-centre ideal membership reflects through the genuine inverse
section. The SAME original chronological germ setoid and proper positions,
not merely the raw number of rows, are preserved. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualDistinctCountOffCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualChronologicalStrictStep
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalFirstMemberRelativeStrict
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  InvertibleIdealQuotient IdealWeightPowers GermIdealTotalTransform
  MarkedIdealRestrictOpen HadamardBridge NormalCrossings
variable {n m : ℕ} {X Y Z : CMfd.{u} n}

private theorem next_mem_off_centre (N C : Set X) (I : GermIdeal n X)
    {π : Y → X} (hπ : IsBlowupAlong n C π) {z : Y} (hzC : π z∉C) (g : Y → ℂ) :
    (nextRelativeStrict N I C π).mem z g ↔
      (restrictOn n (geoStrictTransform π C N) (GermIdeal.pullback (m:=n) π I)).mem z g := by
  have hD : IsClosed (π ⁻¹' C):=hπ.1.1.preimage hπ.contMDiff.continuous
  have hOne : (vanishingIdeal (n:=n) (π ⁻¹' C)).mem z (1 : Y → ℂ):=by
    refine ⟨holomorphicAt_const 1,?_⟩
    filter_upwards [hD.isOpen_compl.mem_nhds hzC] with y hy hyD
    exact (hy hyD).elim
  constructor
  · rintro ⟨k,_hg,hcolon⟩
    have h:=hcolon (1 : Y → ℂ) (one_mem_idealPow hOne k)
    change (restrictOn n (geoStrictTransform π C N) (GermIdeal.pullback (m:=n) π I)).mem z
      (fun y=>(1 : Y → ℂ) y*g y) at h
    simpa only [Pi.one_apply,one_mul] using h
  · intro hg
    refine ⟨0,hg.1,fun a ha=>?_⟩
    have hhol : HolomorphicAt n a z:=ha
    exact restrictOn_mul_left hhol hg

private theorem comp_mem_next_iff (N C : Set X) (hN : IsClosed N)
    (I : GermIdeal n X) (hI : I.IsCoherent)
    {π : Y → X} (hπ : IsBlowupAlong n C π) {z : Y} (hzC : π z∉C)
    (hNorm : ∀f,(restrictOn n N I).mem (π z) f → I.mem (π z) f)
    (f : X → ℂ) (hf : HolomorphicAt n f (π z)) :
    (nextRelativeStrict N I C π).mem z (f ∘ π) ↔ I.mem (π z) f := by
  rw [next_mem_off_centre N C I hπ hzC]
  constructor
  · intro hg
    obtain ⟨s,hs,hsπ,hsec⟩:=BlowupIsomorphismOff.exists_section_compl hπ
    let O : Opens X:=⟨Cᶜ,hπ.1.1.isOpen_compl⟩
    let x : O:=⟨π z,hzC⟩
    have hsz : s x=z:=hsec z hzC
    have hπs (w : O) : π (s w)=w.val:=congrFun hsπ w
    have hMaps : (Subtype.val : O → X) ⁻¹' N ⊆ s ⁻¹' geoStrictTransform π C N := by
      intro w hw
      have he:=TransformOffCentre.eventually_mem_geoStrictTransform_iff hN hπ.1.1 hπ.contMDiff.continuous
        (show π (s w)∉C from by rw [hπs];exact w.property)
      exact he.self_of_nhds.mpr (by rw [hπs];exact hw)
    have hFlat : IsInSpanOnAt (n:=n) (geoStrictTransform π C N)
        (fun t=>∃a,I.mem (π z) a ∧ t=a ∘ π) z (f ∘ π) :=
      IsInSpanOnAt.trans (fun _ ha=>IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp ha)) hg.2
    have hFlat' : IsInSpanOnAt (n:=n) (geoStrictTransform π C N)
        (fun t=>∃a,I.mem (π z) a ∧ t=a ∘ π) (s x) (f ∘ π):=hsz.symm ▸ hFlat
    have hBack:=CoefficientIdealAlongRestrictionFull.isInSpanOnAt_comp hs.continuous
      (fun w=>(hs w).mdifferentiableAt (by simp)) hMaps hFlat'
    have hId (a : X → ℂ) : (a ∘ π) ∘ s=a ∘ (Subtype.val : O → X):=by
      funext w
      exact congrArg a (hπs w)
    rw [hId] at hBack
    have hSpan : IsInSpanOnAt (n:=n) ((Subtype.val : O → X) ⁻¹' N)
        ((GermIdeal.pullback (m:=n) (Subtype.val : O → X) I).mem x) x
        (f ∘ (Subtype.val : O → X)) := by
      refine IsInSpanOnAt.mono ?_ hBack
      rintro _ ⟨t,⟨a,ha,rfl⟩,rfl⟩
      rw [hId]
      exact comp_val_mem_pullback_val O hI ha
    have hOpen : (restrictOn n ((Subtype.val : O → X) ⁻¹' N)
        (GermIdeal.pullback (m:=n) (Subtype.val : O → X) I)).mem x
        (f ∘ (Subtype.val : O → X)):=
      ⟨(holomorphicAt_comp_val_iff O).mpr hf,hSpan⟩
    have hExt : (restrictOn n N I).mem (π z) (extendOpens O (f ∘ (Subtype.val : O → X))):=
      (restrictOn_pullback_val_iff O hI).mp hOpen
    apply hNorm
    refine restrictOn_congr hExt hf ?_
    filter_upwards [O.isOpen.mem_nhds x.property] with w hw _hwN
    rw [extendOpens_val O _ ⟨w,hw⟩]
    rfl
  · intro hfI
    have hhol : HolomorphicAt n (f ∘ π) z:=
      hf.comp_contMDiff (Eventually.of_forall fun _=>hπ.contMDiff.contMDiffAt)
    have hp : (GermIdeal.pullback (m:=n) π I).mem z (f ∘ π):=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨f,hfI,rfl⟩ hhol)
    exact ⟨hhol,IsInSpanAt.restrict (isInSpanAt_self hp hhol)⟩

private theorem strict_mem_congr (N C : Set X) (π : Y → X) (z : Y)
    {I J : GermIdeal n X} (h : ∀a,I.mem (π z) a ↔ J.mem (π z) a) (g : Y → ℂ) :
    (nextRelativeStrict N I C π).mem z g ↔ (nextRelativeStrict N J C π).mem z g := by
  have hPull (a) : (GermIdeal.pullback (m:=n) π I).mem z a ↔
      (GermIdeal.pullback (m:=n) π J).mem z a := by
    rw [GermIdeal.mem_pullback_iff,GermIdeal.mem_pullback_iff]
    constructor
    · exact IsInSpanAt.mono fun _ ⟨b,hb,he⟩=>⟨b,(h b).mp hb,he⟩
    · exact IsInSpanAt.mono fun _ ⟨b,hb,he⟩=>⟨b,(h b).mpr hb,he⟩
  constructor
  · rintro ⟨k,hg,hc⟩
    exact ⟨k,hg,fun a ha=>⟨(hc a ha).1,IsInSpanOnAt.mono (fun b hb=>(hPull b).mp hb) (hc a ha).2⟩⟩
  · rintro ⟨k,hg,hc⟩
    exact ⟨k,hg,fun a ha=>⟨(hc a ha).1,IsInSpanOnAt.mono (fun b hb=>(hPull b).mpr hb) (hc a ha).2⟩⟩

theorem actual_distinct_count_nextRelativeStrict_off_centre
    (N C : Set X) (hN : IsClosed N) (F : Fin m → GermIdeal n X)
    (hF : ∀i,(F i).IsCoherent)
    {π : Y → X} (hπ : IsBlowupAlong n C π) {z : Y} (hzC : π z∉C)
    (hNorm : ∀i f,(restrictOn n N (F i)).mem (π z) f → (F i).mem (π z) f) :
    actualDistinctProperCount (fun i=>nextRelativeStrict N (F i) C π) z=
      actualDistinctProperCount F (π z) := by
  classical
  let G:=fun i=>nextRelativeStrict N (F i) C π
  have hR : actualIdealGermSetoid F (π z)=actualIdealGermSetoid G z := by
    apply Setoid.ext
    intro i j
    constructor
    · intro h g
      exact strict_mem_congr N C π z h g
    · intro h g
      constructor
      · intro hg
        have hhol:=GermIdeal.IsCoherent.holomorphicAt_mem (hF i) hg
        exact (comp_mem_next_iff N C hN (F j) (hF j) hπ hzC (hNorm j) g hhol).mp
          ((h (g ∘ π)).mp ((comp_mem_next_iff N C hN (F i) (hF i) hπ hzC (hNorm i) g hhol).mpr hg))
      · intro hg
        have hhol:=GermIdeal.IsCoherent.holomorphicAt_mem (hF j) hg
        exact (comp_mem_next_iff N C hN (F i) (hF i) hπ hzC (hNorm i) g hhol).mp
          ((h (g ∘ π)).mpr ((comp_mem_next_iff N C hN (F j) (hF j) hπ hzC (hNorm j) g hhol).mpr hg))
  have hP : actualProperPositions F (π z)=actualProperPositions G z := by
    ext i
    simp only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and]
    have h:=comp_mem_next_iff N C hN (F i) (hF i) hπ hzC (hNorm i) (1 : X → ℂ) (holomorphicAt_const 1)
    have heq : (1 : X → ℂ) ∘ π=(1 : Y → ℂ):=by funext y;rfl
    rw [heq] at h
    exact not_congr h.symm
  change ((actualProperPositions G z).image (Quotient.mk (actualIdealGermSetoid G z))).card=
    ((actualProperPositions F (π z)).image (Quotient.mk (actualIdealGermSetoid F (π z)))).card
  rw [←hR,←hP]

theorem original_chronological_distinct_count_off_centre (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π)
    {z : Z} (hz : z∈(geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).N)
    (hzC : π z∉C) :
    actualDistinctProperCount (fun i : Fin E.length=>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (.step T C π hπ)).ideal) z=
    actualDistinctProperCount (fun i : Fin E.length=>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) (π z) := by
  let N:=(geoTransformAlong (geometricTemplate W []) T).N
  let F:=fun i : Fin E.length=>(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hN : IsClosedSubmanifold n N:=
    (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      (𝔪:=geometricTemplate W []) hW isCoherent_unitIdeal T hT).1
  have hx : π z∈N:=geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hz
  have hCo (i : Fin E.length) : (F i).IsCoherent:=by
    obtain ⟨_hNi,_hEi,_hd,hwi,_hnzi,_hpri⟩:=
      original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
    exact hwi.isCoherent
  have hNorm (i : Fin E.length) (g : Y → ℂ)
      (hg : (restrictOn n N (F i)).mem (π z) g) : (F i).mem (π z) g := by
    obtain ⟨hNi,_hEi,_hd,_hwi,_hnzi,hpri⟩:=
      original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
    have hxi : π z∈(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N:=hNi.symm ▸ hx
    obtain ⟨f,_hf,hgen⟩:=hpri (π z) hxi
    have hg' : (restrictOn n (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (F i)).mem (π z) g := by rw [hNi];exact hg
    exact (hgen g).mpr ⟨hg'.1,IsInSpanOnAt.trans (fun a ha=>(hgen a).mp ha |>.2) hg'.2⟩
  have hFamily : (fun i : Fin E.length=>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (.step T C π hπ)).ideal)=
      (fun i=>nextRelativeStrict N (F i) C π) := by
    funext i
    change nextRelativeStrict (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N (F i) C π=_
    rw [(original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT).1]
  rw [hFamily]
  exact actual_distinct_count_nextRelativeStrict_off_centre N C hN.1 F hCo hπ hzC hNorm

end
end Hironaka.HironakaActualDistinctCountOffCentre
