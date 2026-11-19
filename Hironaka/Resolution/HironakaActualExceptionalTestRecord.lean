import Hironaka.Resolution.HironakaActualExceptionalCarrierGeometry
import Hironaka.Resolution.HironakaActualWholeStalkHolomorphicPullback

/-! The genuine BM08 exceptional marked record uses ORDINARY whole pullback
and the unchanged original mark. Nonzero along its actual strict carrier is
derived internally, without source testhood or centre containment.
Blueprint FIRST: hironaka-actual-exceptional-test-record.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualExceptionalTestRecord
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold MarkedIdeals ResolutionInvariantSpec
  DivisorExponentAlong RelativePrincipalizationSpan GermIdealPullbackCalculus
  InvertibleIdealQuotient HironakaActualExceptionalCarrierGeometry
  HironakaActualWholeStalkHolomorphicPullback HironakaHolomorphicJetRankLoci

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem ordinary_nonzero_off {C N : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) {I : GermIdeal n X} (hI : I.IsCoherent)
    {y : Y} (hyC : π y ∉ C) (hne : IsNonzeroAlongAt N I (π y)) :
    IsNonzeroAlongAt (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π I) y := by
  obtain ⟨g,hg,hfreq⟩ := hne
  have hgh : HolomorphicAt n (g ∘ π) y :=
    (GermIdeal.IsCoherent.holomorphicAt_mem hI hg).comp_contMDiff
      (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt)
  refine ⟨g ∘ π,GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg,rfl⟩ hgh),?_⟩
  obtain ⟨s,hs,hsπ,hsy⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hO : IsOpen Cᶜ := hπ.1.1.isOpen_compl
  have ht : Tendsto s (𝓝 ⟨π y,hyC⟩) (𝓝 y) := by
    have h := hs.continuous.continuousAt (x := ⟨π y,hyC⟩)
    rwa [ContinuousAt,hsy y hyC] at h
  have hf : ∃ᶠ p : ↥(Cᶜ : Set X) in 𝓝 ⟨π y,hyC⟩,p.val ∈ N ∧ g p.val ≠ 0 := by
    rw [nhds_subtype_eq_comap,Filter.frequently_comap]
    exact (hfreq.and_eventually (hO.mem_nhds hyC)).mono fun x ⟨hx,hxC⟩ => ⟨⟨x,hxC⟩,rfl,hx⟩
  refine ht.frequently (hf.mono fun p hp => ⟨?_,?_⟩)
  · have he : π (s p)=p.val := congrFun hsπ p
    exact subset_closure (show π (s p) ∈ N \ C by rw [he];exact ⟨hp.1,p.property⟩)
  · have he : π (s p)=p.val := congrFun hsπ p
    simpa only [Function.comp_apply,he] using hp.2

/-- Genuine coherent ORDINARY pullback is nonzero along the actual strict
carrier, for an arbitrary smooth blowup and no source admissibility premise. -/
theorem ordinary_pullback_nonzero_on_strict {C N : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hN : IsClosed N) {I : GermIdeal n X} (hI : I.IsCoherent)
    (hne : ∀ x ∈ N,IsNonzeroAlongAt N I x) :
    ∀ y ∈ geoStrictTransform π C N,
      IsNonzeroAlongAt (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π I) y := by
  have hcoh := isCoherent_pullback hπ.contMDiff hI
  have hoff : ∀ y ∈ geoStrictTransform π C N,π y ∉ C →
      IsNonzeroAlongAt (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π I) y := by
    intro y hy hyC
    exact ordinary_nonzero_off hπ hI hyC
      (hne (π y) (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN hy))
  intro y hy
  by_cases hyC : π y ∈ C
  · by_contra hzero
    have hev := CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt hcoh hzero
    have hf : ∃ᶠ z in 𝓝 y,z ∈ π ⁻¹' (N \ C) := mem_closure_iff_frequently.mp hy
    obtain ⟨z,hz,hzev⟩ := (hf.and_eventually hev).exists
    obtain ⟨g,hg,hgf⟩ := hoff z (subset_closure hz) hz.2
    obtain ⟨w,⟨hwN,hgw⟩,hw⟩ := (hgf.and_eventually (hzev g hg)).exists
    exact hgw (hw hwN)
  · exact hoff y hy hyC

/-- The SAME original mark and full boundary, with ORDINARY whole pullback. -/
def exceptionalTest (M : MarkedIdeal n X) (i j : Fin M.E.length) (π : Y → X) : MarkedIdeal n Y :=
  let C := M.E.get i ∩ M.E.get j
  ⟨geoStrictTransform π C M.N,M.E.map (geoStrictTransform π C) ++ [π ⁻¹' C],
    GermIdeal.pullback (m := n) π M.ideal,M.d⟩

/-- Every native domain field is derived from the ordinary original source
and actual boundary blowup, without source admissibility or target packets. -/
theorem exceptional_test_isInvDomain (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    (i j : Fin M.E.length) (hij : i ≠ j) {π : Y → X}
    (hπ : IsBlowupAlong n (M.E.get i ∩ M.E.get j) π) :
    IsInvDomain k (exceptionalTest M i j π) := by
  obtain ⟨_heq,hN,hDim,hE,hTr,_hreg,_hlen,_hslots,_hlast⟩ :=
    exceptional_carrier_geometry M hM i j hij hπ
  refine ⟨⟨hN,isCoherent_pullback hπ.contMDiff hM.isWellFormed.isCoherent,hE,hTr⟩,
    hDim,hM.one_le_d,?_⟩
  exact ordinary_pullback_nonzero_on_strict hπ hM.isWellFormed.isClosedSubmanifold_N.1
    hM.isWellFormed.isCoherent hM.isNonzeroAlongAt

/-- Every original field and ordered old/empty/exceptional position is kept. -/
theorem exceptional_test_dictionary (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    (i j : Fin M.E.length) (hij : i ≠ j) {π : Y → X}
    (hπ : IsBlowupAlong n (M.E.get i ∩ M.E.get j) π) :
    let C := M.E.get i ∩ M.E.get j
    let Q := exceptionalTest M i j π
    Q.N=π ⁻¹' M.N ∧ Q.ideal=GermIdeal.pullback (m := n) π M.ideal ∧ Q.d=M.d ∧
      Q.E=M.E.map (geoStrictTransform π C) ++ [π ⁻¹' C] ∧ Q.E.length=M.E.length+1 ∧
      (∀ h : Fin M.E.length,Q.E[h.val]'(by simp [Q,exceptionalTest])=
        geoStrictTransform π C (M.E.get h)) ∧
      Q.E.getLast (by simp [Q,exceptionalTest])=π ⁻¹' C := by
  refine ⟨(exceptional_carrier_geometry M hM i j hij hπ).1,rfl,rfl,rfl,
    by simp [exceptionalTest],?_,?_⟩
  · intro h
    change (M.E.map (geoStrictTransform π (M.E.get i ∩ M.E.get j)) ++
      [π ⁻¹' (M.E.get i ∩ M.E.get j)])[h.val]=_
    rw [List.getElem_append_left (by simpa only [List.length_map] using h.isLt),List.getElem_map]
    rfl
  · exact List.getLast_append_singleton _

/-- The actual original germ map retains the WHOLE ideal image, EVERY
original holomorphic numerator and the actual scalar action on ALL germs. -/
theorem exceptional_germ_dictionary (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    (i j : Fin M.E.length) {π : Y → X}
    (hπ : IsBlowupAlong n (M.E.get i ∩ M.E.get j) π) (y : Y) :
    let τ := actualHolomorphicGermPullback hπ.contMDiff y
    Ideal.map τ.toRingHom (wholeChartStalkIdeal M.ideal (π y) (π y) (mem_chart_source _ (π y)))=
      wholeChartStalkIdeal (exceptionalTest M i j π).ideal y y (mem_chart_source _ y) ∧
      (∀ (g : X → ℂ) (hg : HolomorphicAt n g (π y)),
        τ (chartTranslatedGerm (π y) (π y) (mem_chart_source _ (π y)) g hg)=
          chartTranslatedGerm y y (mem_chart_source _ y) (g ∘ π)
            (hg.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt))) ∧
      ∀ (c : ℂ) (a : HolGerm (ComplexModel n)),τ (c • a)=c • τ a := by
  refine ⟨map_wholeChartStalkIdeal_actual_pullback hπ.contMDiff M.ideal hM.isWellFormed.isCoherent y,?_,?_⟩
  · intro g hg
    exact actualHolomorphicGermPullback_original_function hπ.contMDiff y g hg
  · intro c a
    exact (actualHolomorphicGermPullback hπ.contMDiff y).toLinearMap.map_smul c a

end
end Hironaka.HironakaActualExceptionalTestRecord
