import Hironaka.Resolution.HironakaG1RatioGraphCentreGeometry
import Hironaka.Analytic.SubmanifoldCodRestrict

/-! The actual normalized source of the open-image ratio graph section. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1RatioGraphNativeSource
noncomputable section
open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG1NormalGraphFlags HironakaG1RatioSectionBlowup HironakaBaseChange
  HironakaActualNativeSectionFiniteHistory SubmanifoldChartedSpace SubmanifoldCodRestrict
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaG1RatioGraphCentreGeometry NormalCrossings MarkedIdealBiholomorphism

variable {n t : ℕ} {U : Opens (ComplexModel n)} {X : CMfd.{0} (n+t)}
    {e : X → blockOpen U t} {O : Opens (blockOpen U t)}
    (b : X ≃ₘ⟮𝓘(ℂ,ComplexModel (n+t)),𝓘(ℂ,ComplexModel (n+t))⟯ O)
    (hb : ∀ z, e z = (b z).val)
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)

private abbrev he : IsOpenHoloEmbedding (n+t) e := ⟨O,b,hb⟩

/-- The open of the actual normalized base whose graph points lie in the
reader cylinder image. -/
def sectionBaseOpen : Opens U :=
  ⟨blockSection f ⁻¹' O, O.isOpen.preimage (blockSection_contMDiff hf).continuous⟩

private theorem section_of_graph (z : blockOpen U t) (hz : z ∈ blockGraph f univ) :
    blockSection f (blockProjection z) = z := by
  apply Subtype.ext
  change HironakaActualIntrinsicStableAmbientIso.join (blockProjection z).val (f (blockProjection z)) = z.val
  rw [← hz.2]
  exact join_projections z.val

private theorem graph_of_section (x : U) : blockSection f x ∈ blockGraph f univ := by
  refine ⟨mem_univ _,?_⟩
  rw [blockProjection_blockSection]
  exact second_join _ _

/-- The intrinsic atlas of the literal ratio section gives the original
normalized source-open coordinates. The inverse map is the exact base
projection and the forward map is the cylinder's actual graph lift. -/
def sectionBaseEquiv :
    sectionBaseOpen (O := O) hf ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      nativeManifold (Nat.le_add_right n t) (sectionSupport e f)
        (sectionSupport_regular (he b hb) hf) := by
  let A := sectionBaseOpen (O := O) hf
  let W := sectionSupport e f
  let hW := sectionSupport_regular (he b hb) hf
  let j (x : A) : O := ⟨blockSection f x.val,x.property⟩
  let s : A → X := b.symm ∘ j
  have hs (x : A) : e (s x) = blockSection f x.val := by
    rw [hb]
    change (b (b.symm (j x))).val = _
    rw [b.apply_symm_apply]
  have hWmem (x : A) : s x ∈ W := by
    change e (s x) ∈ blockGraph f univ
    rw [hs]
    exact graph_of_section _
  let p (z : nativeManifold (Nat.le_add_right n t) W hW) : A :=
    ⟨blockProjection (e z.val), by
      change blockSection f (blockProjection (e z.val)) ∈ O
      rw [section_of_graph _ z.property, hb]
      exact (b z.val).property⟩
  have hj : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+t)) ∞ j :=
    (ContMDiff.subtypeVal_comp_iff O j).mp ((blockSection_contMDiff hf).comp contMDiff_subtype_val)
  have hsHol : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+t)) ∞ s := b.symm.contMDiff.comp hj
  have hp : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ p :=
    (ContMDiff.subtypeVal_comp_iff A p).mp ((blockProjection_contMDiff U t).comp
      ((he b hb).contMDiff.comp (SubmanifoldChartedSpace.contMDiff_val _ hW)))
  refine ⟨⟨fun x => ⟨s x,hWmem x⟩,p,?_,?_⟩,
    contMDiff_codRestrict (Nat.le_add_right n t) hW hsHol hWmem,hp⟩
  · intro x
    apply Subtype.ext
    change blockProjection (e (s x)) = x.val
    rw [hs,blockProjection_blockSection]
  · intro z
    apply Subtype.ext
    apply (he b hb).injective
    change e (s (p z)) = e z.val
    rw [hs]
    exact section_of_graph _ z.property

/-- The source centre in the actual open is carried by that same graph.
Its image is the literal centre in the common padded open. -/
theorem sectionBaseEquiv_centre_image (D : Set U) :
    let c := sectionBaseEquiv b hb hf
    let W := sectionSupport e f
    let D' := c.symm ⁻¹' ((Subtype.val : sectionBaseOpen (O := O) hf → U) ⁻¹' D)
    (Subtype.val : W → X) '' D' = e ⁻¹' blockGraph f D := by
  intro c W D'
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨hz,z.property.2⟩
  · intro hz
    exact ⟨⟨x,mem_univ _,hz.2⟩,hz.1,rfl⟩


open Hironaka.HolomorphicIdealSheaves HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaG1IteratedNormalBlockIdeal
  HironakaG1RatioBlockUnpadding HironakaG11PresLineState ResolutionInvariantSpec
  HironakaActualOpenEmbeddingCanonicalExtension CoefficientIdealRestriction MarkedIdealOpenBiholomorphism
  HironakaG1SingularGraphCodimension HironakaEmbeddedAnalytic BlowupStrictSubmanifold MarkedIdealOperationsAlong.MarkedIdeal

private theorem sectionBaseEquiv_point (x : sectionBaseOpen (O := O) hf) :
    e (sectionBaseEquiv b hb hf x).val = blockSection f x.val := by
  rw [hb]
  change (b (b.symm (⟨blockSection f x.val,x.property⟩ : O))).val = _
  rw [b.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Under the actual graph diffeomorphism, the whole native marked record
is the whole source record restricted to the exact normalized open. -/
theorem sectionBaseEquiv_record (Q : MarkedIdeal n U) (hQ : Q.ideal.IsCoherent) (hd : 0 < Q.d) :
    let A := sectionBaseOpen (O := O) hf
    let W := sectionSupport e f
    let hW := sectionSupport_regular (he b hb) hf
    let P := markedPullback (m := n+t) e (blockAmbientMarked f Q)
    MarkedIdeal.pullback (sectionBaseEquiv b hb hf) (nativePullback (Nat.le_add_right n t) W hW P) =
      markedPullback (m := n) (Subtype.val : A → U) Q := by
  intro A W hW P
  let c := sectionBaseEquiv b hb hf
  let WN := nativeManifold (Nat.le_add_right n t) W hW
  let AX := CMfd.of (n := n) A
  let BX := CMfd.of (n := n+t) (blockOpen U t)
  let UX := CMfd.of (n := n) U
  let i : WN → X := Subtype.val
  have hi := SubmanifoldChartedSpace.contMDiff_val (Nat.le_add_right n t) hW
  have hCo : (blockAmbientMarked f Q).ideal.IsCoherent := blockMarked_coherent hf hQ []
  have hPe : P.ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback (he b hb).contMDiff hCo
  change markedPullback (m := n) c (markedPullback (m := n) i P) = _
  rw [← whole_markedPullback_comp (X := X) (Y := WN) (Z := AX) hi c.contMDiff P hPe]
  change markedPullback (m := n) (i ∘ c) (markedPullback (m := n+t) e (blockAmbientMarked f Q)) = _
  let j (x : A) : O := ⟨blockSection f x.val,x.property⟩
  have hj : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+t)) ∞ j :=
    (ContMDiff.subtypeVal_comp_iff O j).mp ((blockSection_contMDiff hf).comp contMDiff_subtype_val)
  have hc : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+t)) ∞ (i ∘ c) :=
    b.symm.contMDiff.comp hj
  rw [← whole_markedPullback_comp (X := BX) (Y := X) (Z := AX) (he b hb).contMDiff hc _ hCo]
  have hEq : e ∘ (i ∘ c) = blockSection f ∘ (Subtype.val : A → U) :=
    funext (sectionBaseEquiv_point b hb hf)
  rw [hEq, whole_markedPullback_comp (X := BX) (Y := UX) (Z := AX) (blockSection_contMDiff hf)
    contMDiff_subtype_val _ hCo, markedPullback_blockAmbientMarked_section hf Q hQ hd]

private theorem native_admissible_interior_empty (Q : MarkedIdeal n U)
    {K D : Set U} {H : ℕ → ℕ}
    (hState : NativeHSState (X := CMfd.of (n := n) U) Q K H)
    (hD : Q.IsAdmissibleCentre D) : interior D = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hs := mem_singularSet_iff.mp (native_cut_singular hState (hD.2.1 (interior_subset hx)))
  have hNear : ∀ᶠ y in nhds x, y ∈ K ↔ y ∈ (univ : Set U) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact ⟨fun _ => mem_univ _,fun _ => (mem_singularSet_iff.mp
      (native_cut_singular hState (hD.2.1 (interior_subset hy)))).1⟩
  exact hs.2 n (CodimOneSupport.regularAtDim_of_eventually_mem_iff (hNear.mono fun _ h => h.symm)
    (AnalyticIrreducibleComponents.regularAtDim_univ x))

/-- An admissible centre of the actual normalized source produces a genuine
ambient blowup and the induced genuine native blowup. The centre, the whole
initial section record, and the transformed records are all identified
through the same literal graph and its strict transform. -/
theorem exists_ratioSection_source_blowup (hpos : 0 < n+t)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q) {K D : Set U} {H : ℕ → ℕ}
    (hState : NativeHSState (X := CMfd.of (n := n) U) Q K H)
    (hD : Q.IsAdmissibleCentre D) :
    let A := sectionBaseOpen (O := O) hf
    let W := sectionSupport e f
    let hW := sectionSupport_regular (he b hb) hf
    let c := sectionBaseEquiv b hb hf
    let D' := c.symm ⁻¹' ((Subtype.val : A → U) ⁻¹' D)
    let P := markedPullback (m := n+t) e (blockAmbientMarked f Q)
    let C := (Subtype.val : W → X) '' D'
    C = e ⁻¹' blockGraph f D ∧
    MarkedIdeal.pullback c (nativePullback (Nat.le_add_right n t) W hW P) =
      markedPullback (m := n) (Subtype.val : A → U) Q ∧
    ∃ (Y : CMfd.{0} (n+t)) (π : Y → X) (hπ : IsBlowupAlong (n+t) C π),
      let V := geoStrictTransform π C W
      let hV := strictRegular (sectionSupport_closed (he b hb) hf) hW D' π hπ
      let σ := nativeProjection (Nat.le_add_right n t) (sectionSupport_closed (he b hb) hf) hW D' π hπ
      let S' := (withN P (P.N ∩ W)).geoTransform C π
      IsBlowupAlong n D' σ ∧
      (∀ z : V, π z.val = (σ z).val) ∧
      RestrictEquiv (withN (P.geoTransform C π) S'.N) S' ∧
      nativePullback (Nat.le_add_right n t) V hV S' =
        (nativePullback (Nat.le_add_right n t) W hW P).geoTransform D' σ := by
  intro A W hW c D' P C
  have hEq : C = e ⁻¹' blockGraph f D := sectionBaseEquiv_centre_image b hb hf D
  refine ⟨hEq,sectionBaseEquiv_record b hb hf Q hQ.isWellFormed.isCoherent hQ.one_le_d,?_⟩
  obtain ⟨hTr,hTrN,hAC⟩ := ratioSection_centreGeometry (he b hb) hf Q hQ hState hD
  have hAmb := (blockAmbientMarked_nativeHSState f hf Q H hState hQ).1
  have hPD : IsInvDomain (n+t) P :=
    isInvDomain_pullback_of_isOpenHoloEmbedding
      (X := CMfd.of (n := n+t) (blockOpen U t)) (Y := X) e (he b hb) hAmb
  have hVal := isOpenHoloEmbedding_val (n := n) A
  have hNative : IsClosedSubmanifold n D' := by
    apply (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff c.symm).mpr
    refine ⟨hD.1.1.preimage continuous_subtype_val,fun x hx => ?_⟩
    obtain ⟨k,hk⟩ := hD.1.2 x.val hx
    exact ⟨k,hVal.regularAtDim_preimage hk⟩
  have hProper : interior D' = ∅ := by
    rw [show D' = ((Subtype.val : A → U) ∘ c.symm.toHomeomorph) ⁻¹' D from rfl,
      ← (hVal.isOpenMap.comp c.symm.toHomeomorph.isOpenMap).preimage_interior_eq_interior_preimage
        (continuous_subtype_val.comp c.symm.continuous), native_admissible_interior_empty Q hState hD, preimage_empty]
  have hC : P.IsAdmissibleCentre C := hEq.symm ▸ hAC
  exact exists_blockGraph_section_blowup hpos (he b hb) hf Q hQ.isWellFormed
    hPD.isWellFormed hTr hTrN D' hNative hProper hC

end
end Hironaka.HironakaG1RatioGraphNativeSource
