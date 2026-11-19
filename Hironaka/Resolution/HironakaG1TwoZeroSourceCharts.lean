import Hironaka.Resolution.HironakaG1TwoZeroBornCounts

/-! # Literal unit-equivalent source charts for the two-zero example -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1TwoZeroSourceCharts
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers GermIdealOrder RelativePrincipalizationSpan InvertibleIdealQuotient BlowupFlatCoordinates
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedNormalPadding
  HironakaG1PositiveNormalNonspecialExample HironakaG1TwoZeroBornCounts
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec StepOneValue
  InvDomainRebase InvDomainMemberRestriction HironakaG1RecursiveMemberValueTransport NonmonomialOrderLocal
  HironakaG8MixedOrderInvariance HironakaSharpOriginalProductTraceOrder
  HironakaG1ProperCarrierNormalLocalClass HironakaActualOpenZeroSectionDifferentials
  HironakaSmoothSubmersionOrderedChoiceImageTrace MarkedIdealBiholomorphism.MarkedIdeal
  GermIdealPullbackCalculus BlowupTowerTransforms StepOneRegime MemberInterLocusAlong
  HironakaG1ProperCarrierNormalContact HironakaActualSectionBoundaryGeometry HironakaG8HomStable
  HironakaActualNativeSectionInitialBar HironakaRelativeNormalIdeal StepOneLowerDomain StepOneValueMasked
  HironakaG1LaterPositiveNormalExample
  MarkedIdealRestrictOpen HironakaCoherentTransformExtension

private theorem finite_two_generator_unit {n : ℕ} {M : CMfd.{0} n}
    (g h u : M → ℂ) (hg : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g)
    (hh : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h)
    (hu : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) u)
    (hUnit : ∀ z, u z ≠ 0) :
    finiteFunctionIdeal (n := n) (fun j : Bool => if j then g else fun z => h z * u z) =
      finiteFunctionIdeal (n := n) (fun j : Bool => if j then g else h) := by
  apply GermIdeal.ext
  funext x f
  apply propext
  let G : Bool → M → ℂ := fun j => if j then g else fun z => h z * u z
  let H : Bool → M → ℂ := fun j => if j then g else h
  change IsInSpanAt (n := n) (· ∈ range G) x f ↔ IsInSpanAt (n := n) (· ∈ range H) x f
  have hHolg : HolomorphicAt n g x := Eventually.of_forall fun z => hg z
  have hHolh : HolomorphicAt n h x := Eventually.of_forall fun z => hh z
  have hHolu : HolomorphicAt n u x := Eventually.of_forall fun z => hu z
  constructor
  · intro hf
    refine IsInSpanAt.trans ?_ hf
    rintro a ⟨j, rfl⟩
    cases j
    · have hh' : IsInSpanAt (n := n) (· ∈ range H) x h :=
        isInSpanAt_self ⟨false, rfl⟩ hHolh
      apply InvertibleIdealQuotient.IsInSpanAt.congr'
        (RelativePrincipalizationSpan.IsInSpanAt.mul_left hHolu hh')
      exact Eventually.of_forall fun z => mul_comm _ _
    · exact isInSpanAt_self ⟨true, rfl⟩ hHolg
  · intro hf
    refine IsInSpanAt.trans ?_ hf
    rintro a ⟨j, rfl⟩
    cases j
    · have hh' : IsInSpanAt (n := n) (· ∈ range G) x (fun z => h z * u z) :=
        isInSpanAt_self ⟨false, rfl⟩ (hHolh.mul hHolu)
      apply InvertibleIdealQuotient.IsInSpanAt.congr'
        (RelativePrincipalizationSpan.IsInSpanAt.mul_left (BlowupFlatCoordinates.HolomorphicAt.inv hHolu (hUnit x)) hh')
      exact Eventually.of_forall fun z => by
        change (u z)⁻¹ * (h z * u z) = h z
        rw [mul_comm (h z), ← mul_assoc, inv_mul_cancel₀ (hUnit z), one_mul]
    · exact isInSpanAt_self ⟨true, rfl⟩ hHolg

def bornSourceOpen : Opens (ComplexModel 2) :=
  ⟨{z | z (1 : Fin 2) ≠ 1}, isOpen_ne_fun (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).continuous continuous_const⟩

def offSourceOpen : Opens (ComplexModel 2) :=
  ⟨{z | z (1 : Fin 2) ≠ 0}, isOpen_ne_fun (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).continuous continuous_const⟩

def linearOffGenerator (j : Bool) (z : ComplexModel 2) : ℂ :=
  if j then z 0 else z 1 - 1

private theorem hdiff (j : Fin 2) :
    MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ) (fun z : ComplexModel 2 => z j) :=
  (EuclideanSpace.proj (𝕜 := ℂ) j).mdifferentiable

private theorem shifted :
    MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ) (fun z : ComplexModel 2 => z 1 - 1) :=
  ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).differentiable.sub_const (1 : ℂ)).mdifferentiable

private theorem hGenerator (j : Bool) :
    MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ) (generator j) := by
  cases j
  · change MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ) (fun z : ComplexModel 2 => z 1 ^ 2 * (z 1 - 1))
    exact ((hdiff 1).pow 2).mul shifted
  · exact hdiff 0

private theorem hOld (j : Bool) :
    MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ) (coordinatePairGenerator j) := by
  cases j
  · exact (hdiff 1).pow 2
  · exact hdiff 0

private theorem hLinear (j : Bool) :
    MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ) (linearOffGenerator j) := by
  cases j
  · exact shifted
  · exact hdiff 0

set_option maxHeartbeats 900000 in
/-- On the genuine open containing the blowup centre the new whole
source ideal is literally the old double-zero ideal. -/
theorem born_source_window_ideal_eq :
    GermIdeal.pullback (m := 2) (Subtype.val : bornSourceOpen → ComplexModel 2) sourceIdeal =
      GermIdeal.pullback (m := 2) (Subtype.val : bornSourceOpen → ComplexModel 2) coordinatePairIdeal := by
  change GermIdeal.pullback (m := 2) (Subtype.val : bornSourceOpen → ComplexModel 2)
    (finiteFunctionIdeal (n := 2) generator) = GermIdeal.pullback (m := 2)
      (Subtype.val : bornSourceOpen → ComplexModel 2) (finiteFunctionIdeal (n := 2) coordinatePairGenerator)
  rw [finiteFunctionIdeal_pullback generator hGenerator _ contMDiff_subtype_val,
    finiteFunctionIdeal_pullback coordinatePairGenerator hOld _ contMDiff_subtype_val]
  let M := CMfd.of (n := 2) bornSourceOpen
  let v : M → ComplexModel 2 := Subtype.val
  have hv : ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ v := contMDiff_subtype_val
  have hmv := hv.mdifferentiable (by simp)
  have h := finite_two_generator_unit (M := M) ((fun z : ComplexModel 2 => z 0) ∘ v)
    ((fun z : ComplexModel 2 => z 1 ^ 2) ∘ v) ((fun z : ComplexModel 2 => z 1 - 1) ∘ v)
    ((hdiff 0).comp hmv) (((hdiff 1).pow 2).comp hmv) (shifted.comp hmv)
    (fun z => sub_ne_zero.mpr z.property)
  have hL : (fun j => generator j ∘ v) =
      (fun j : Bool => if j then (fun z : M => z.val 0) else fun z => z.val 1 ^ 2 * (z.val 1 - 1)) :=
    funext (fun j => by cases j <;> rfl)
  have hR : (fun j => coordinatePairGenerator j ∘ v) =
      (fun j : Bool => if j then (fun z : M => z.val 0) else fun z => z.val 1 ^ 2) :=
    funext (fun j => by cases j <;> rfl)
  rw [hL, hR]
  exact h

set_option maxHeartbeats 900000 in
/-- On the actual open containing the off-centre source point, the
quadratic factor is a unit and the new ideal is a simple transverse
coordinate pair. -/
theorem off_source_window_ideal_eq :
    GermIdeal.pullback (m := 2) (Subtype.val : offSourceOpen → ComplexModel 2) sourceIdeal =
      GermIdeal.pullback (m := 2) (Subtype.val : offSourceOpen → ComplexModel 2)
        (finiteFunctionIdeal (n := 2) linearOffGenerator) := by
  rw [finiteFunctionIdeal_pullback generator hGenerator _ contMDiff_subtype_val,
    finiteFunctionIdeal_pullback linearOffGenerator hLinear _ contMDiff_subtype_val]
  let M := CMfd.of (n := 2) offSourceOpen
  let v : M → ComplexModel 2 := Subtype.val
  have hv : ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ v := contMDiff_subtype_val
  have hmv := hv.mdifferentiable (by simp)
  have h := finite_two_generator_unit (M := M) ((fun z : ComplexModel 2 => z 0) ∘ v)
    ((fun z : ComplexModel 2 => z 1 - 1) ∘ v) ((fun z : ComplexModel 2 => z 1 ^ 2) ∘ v)
    ((hdiff 0).comp hmv) (shifted.comp hmv) (((hdiff 1).pow 2).comp hmv)
    (fun z => pow_ne_zero 2 z.property)
  have hL : (fun j => generator j ∘ v) =
      (fun j : Bool => if j then (fun z : M => z.val 0) else fun z => (z.val 1 - 1) * z.val 1 ^ 2) := by
    funext j z
    cases j
    · exact mul_comm _ _
    · rfl
  have hR : (fun j => linearOffGenerator j ∘ v) =
      (fun j : Bool => if j then (fun z : M => z.val 0) else fun z => z.val 1 - 1) :=
    funext (fun j => by cases j <;> rfl)
  rw [hL,hR]
  exact h

set_option maxHeartbeats 850000 in
/-- Positive initial selection removes every incident original boundary
slot. At a selected cosupport point the genuine recursive raw order is
therefore positive for every positive mark. -/
theorem positive_initial_selected_raw_order_of_cosupport
    {n k : ℕ} {X : CMfd.{0} n} (J : MarkedIdeal n X) (p : X) (V : Opens X)
    (hp : p ∈ V) :
    let K := positiveMemberOn J (.refl : BlowupTower X X) p V
    let z : V := ⟨p,hp⟩
    IsInvDomain k K → z ∈ K.cosupp → 0 < nmOrd (M := CMfd.of (n := n) V) K z := by
  classical
  intro K z hK hz
  have hE : K.E = (J.E.filter (fun D => decide (p ∉ D))).map
      ((Subtype.val : V → X) ⁻¹' ·) := by
    change ((memberRestrict (barMarked J) (membersThrough (barMarked J).E
      (origMembers J (.refl : BlowupTower X X)) p)).E).map _ = _
    rw [memberRestrict_membersThrough_E]
    have hOrig : origMembers J (.refl : BlowupTower X X) = J.E := List.take_length
    rw [hOrig]
    congr 1
    change J.E.filter _ = _
    apply List.filter_congr
    intro D hD
    simp [hD]
  have hOff : ∀ i : Fin K.E.length, z ∉ K.E.get i := by
    intro i hi
    let S := K.E.get i
    have hMem : S ∈ K.E := List.get_mem K.E i
    rw [hE] at hMem
    obtain ⟨D, hD, he⟩ := List.mem_map.mp hMem
    have hNot := of_decide_eq_true (List.mem_filter.mp hD).2
    have hpull : z ∈ (Subtype.val : V → X) ⁻¹' D := he.symm ▸ (show z ∈ S from hi)
    exact hNot hpull
  rw [nmOrd_eq_ordinaryTraceOrder_of_notMem K hOff]
  exact lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one hK.one_le_d)
    ((ordinaryTraceOrder_cosupport_iff hK.isWellFormed.isClosedSubmanifold_N
      hK.isWellFormed.isCoherent hK.isNonzeroAlongAt hz.1 K.d).mp hz)

/-- The ambient window obtained by pulling back a literal model open
under the two-coordinate section projection. -/
def sectionWindow (W : Opens (ComplexModel 2)) : Opens HironakaG1TwoZeroBornCounts.X :=
  ⟨(fun x => (projection U x).val) ⁻¹' W,
    W.isOpen.preimage (continuous_subtype_val.comp (projection_contMDiff U).continuous)⟩

abbrev sourceWithIdeal (I : GermIdeal 2 (ComplexModel 2)) : MarkedIdeal 2 U :=
  {source with ideal := GermIdeal.pullback (m := 2) (Subtype.val : U → ComplexModel 2) I}

set_option maxHeartbeats 1100000 in
/-- Whole model-ideal equality on an open transports to literal section
records, including their carrier, mark, and ordered boundary. -/
theorem section_window_record_eq (W : Opens (ComplexModel 2))
    (I J : GermIdeal 2 (ComplexModel 2)) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hEq : GermIdeal.pullback (m := 2) (Subtype.val : W → ComplexModel 2) I =
      GermIdeal.pullback (m := 2) (Subtype.val : W → ComplexModel 2) J) :
    pullback (Subtype.val : sectionWindow W → HironakaG1TwoZeroBornCounts.X)
        (sectionMarked (sourceWithIdeal I)) =
      pullback (Subtype.val : sectionWindow W → HironakaG1TwoZeroBornCounts.X)
        (sectionMarked (sourceWithIdeal J)) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (𝔪 := pullback (Subtype.val : sectionWindow W → HironakaG1TwoZeroBornCounts.X)
      (sectionMarked (sourceWithIdeal I)))
    (𝔫 := pullback (Subtype.val : sectionWindow W → HironakaG1TwoZeroBornCounts.X)
      (sectionMarked (sourceWithIdeal J))) rfl rfl ?_ rfl
  let V := sectionWindow W
  let X := HironakaG1TwoZeroBornCounts.X
  let p : X → U := projection U
  let f : V → W := fun x => ⟨(p x.val).val, x.property⟩
  have hA : ContMDiff 𝓘(ℂ,ComplexModel 2) 𝓘(ℂ,ComplexModel 2) ∞
      (Subtype.val : U → ComplexModel 2) := contMDiff_subtype_val
  have hp : ContMDiff 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ComplexModel 2) ∞ p := projection_contMDiff U
  have hv : ContMDiff 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ComplexModel 3) ∞
      (Subtype.val : V → X) := contMDiff_subtype_val
  have hf : ContMDiff 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ComplexModel 2) ∞ f :=
    (ContMDiff.subtypeVal_comp_iff W f).mp ((hA.comp hp).comp hv)
  have hW : ContMDiff 𝓘(ℂ,ComplexModel 2) 𝓘(ℂ,ComplexModel 2) ∞
      (Subtype.val : W → ComplexModel 2) := contMDiff_subtype_val
  have fold (K : GermIdeal 2 (ComplexModel 2)) (hK : K.IsCoherent) :
      GermIdeal.pullback (m := 3) (Subtype.val : V → X)
        (GermIdeal.pullback (m := 3) p
          (GermIdeal.pullback (m := 2) (Subtype.val : U → ComplexModel 2) K)) =
      GermIdeal.pullback (m := 3) f
        (GermIdeal.pullback (m := 2) (Subtype.val : W → ComplexModel 2) K) := by
    rw [← coherent_pullback_comp hA hp K hK,
      ← coherent_pullback_comp (hA.comp hp) hv K hK, ← coherent_pullback_comp hW hf K hK]
    rfl
  exact (fold I hI).trans ((congrArg (GermIdeal.pullback (m := 3) f) hEq).trans (fold J hJ).symm)

private theorem projection_zero (a : U) : projection U (zeroSection U a) = a := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion 2 1 a

set_option maxHeartbeats 1100000 in
/-- At the new off-centre source zero the literal section branch is
nonspecial. A tangent line in the selected original member leaves the
two-point cosupport arbitrarily close to the anchor. -/
theorem off_source_section_nonspecial :
    ¬ IsSpecial sectionRecord emptyTower p₁ := by
  intro h
  have hLevel := section_initial_levels.2
  rcases h with hZero | ⟨_, hMem⟩
  · exact (by decide : (1 : ℕ) ≠ 0) (hLevel.symm.trans hZero.1)
  have hSec : IsInvDomain 2 sectionRecord :=
    section_projected_domain 2 source.N source.E source.ideal source.d source_domain
  have hCos : (barMarked (X := HironakaG1TwoZeroBornCounts.X) sectionRecord).cosupp = {p₀,p₁} :=
    (((bar_local_any_boundary (X := HironakaG1TwoZeroBornCounts.X) sectionRecord hSec).wEquiv.2
      emptyTower).2 trivial).symm.trans section_source_cosupport
  let e := EuclideanSpace.single (1 : Fin 2) (1 : ℂ)
  let a (t : ℂ) : U := ⟨(1+t) • e, mem_univ _⟩
  let f (t : ℂ) := zeroSection U (a t)
  have ha : Continuous a :=
    (continuous_const.add continuous_id).smul continuous_const |>.subtype_mk (fun _ => mem_univ _)
  have hf : Continuous f := (zeroSection_contMDiff U).continuous.comp ha
  have hAt : f 0 = p₁ := by
    change zeroSection U (a 0) = zeroSection U a₁
    congr 1
    apply Subtype.ext
    simp [a, a₁, e]
  have hT : Tendsto f (𝓝 0) (𝓝 p₁) := hAt ▸ hf.tendsto 0
  have hne : ∃ᶠ t : ℂ in 𝓝 0, t ≠ 0 := by
    have hF : ∃ᶠ t : ℂ in 𝓝[≠] 0, True :=
      Filter.Eventually.frequently (Filter.Eventually.of_forall fun _ => trivial)
    exact ((frequently_nhdsWithin_iff).mp hF).mono (fun _ ht => ht.2)
  have hNear : ∀ᶠ t : ℂ in 𝓝 0, 1 + t ≠ 0 :=
    ((continuous_const.add continuous_id : Continuous (fun t : ℂ => 1+t)).tendsto 0).eventually
      (isOpen_ne.mem_nhds (by simp))
  obtain ⟨t, ht, htn, hloc⟩ := (hne.and_eventually
    (hNear.and (hT.eventually (mem_memberInterLocus_iff.mp hMem).2))).exists
  have htCoord : (projection U (f t)).val (1 : Fin 2) = 1+t := by
    change (projection U (zeroSection U (a t))).val 1 = 1+t
    rw [projection_zero]
    simp [a, e]
  have hN : f t ∈ (barMarked (X := HironakaG1TwoZeroBornCounts.X) sectionRecord).N := by
    change zeroSection U (a t) ∈ projection U ⁻¹' univ ∧ _
    constructor
    · exact mem_univ _
    · exact HironakaActualCentreJointJets.actualJointNormalProjection_tangent 2 1 (a t).val
  have hBoundary : ∀ D ∈ origMembers sectionRecord emptyTower, p₁ ∈ D → f t ∈ D := by
    intro D hD hAtD
    change D ∈ [(projection U ⁻¹' {z : U | z.val 0 = 0}),
      (projection U ⁻¹' {z : U | z.val 1 = 0})] at hD
    rcases List.mem_cons.mp hD with rfl | hD
    · change (projection U (zeroSection U (a t))).val 0 = 0
      rw [projection_zero]
      simp [a,e]
    · obtain rfl := List.mem_singleton.mp hD
      change (projection U (zeroSection U a₁)).val 1 = 0 at hAtD
      rw [projection_zero] at hAtD
      simp [a₁] at hAtD
  have hIn : f t ∈ (barMarked (X := HironakaG1TwoZeroBornCounts.X) sectionRecord).cosupp :=
    hloc hN hBoundary
  rw [hCos] at hIn
  rcases hIn with h0 | h1
  · change f t = p₀ at h0
    rw [h0] at htCoord
    change (projection U (zeroSection U a₀)).val 1 = 1+t at htCoord
    rw [projection_zero] at htCoord
    exact htn (by simpa [a₀] using htCoord.symm)
  · rw [mem_singleton_iff.mp h1] at htCoord
    change (projection U (zeroSection U a₁)).val 1 = 1+t at htCoord
    rw [projection_zero] at htCoord
    apply ht
    simpa [a₁] using htCoord.symm

abbrev originalBornSource : MarkedIdeal 2 U := sourceWithIdeal coordinatePairIdeal
abbrev bornSectionWindow := sectionWindow bornSourceOpen

theorem born_anchor_mem_section_window :
    q ∈ openPreimage B bornSectionWindow := by
  change π q ∈ bornSectionWindow
  rw [show π q = p₀ from joint_first_point_blowup_positive_normal_contact.2.2.2.1]
  change (projection U (zeroSection U a₀)).val (1 : Fin 2) ≠ 1
  rw [projection_zero]
  simp [a₀]

theorem off_anchor_mem_section_window :
    offCentreAnchor ∈ openPreimage B (sectionWindow offSourceOpen) := by
  change π offCentreAnchor ∈ sectionWindow offSourceOpen
  rw [offCentreAnchor_proj]
  change (projection U (zeroSection U a₁)).val (1 : Fin 2) ≠ 0
  rw [projection_zero]
  simp [a₁]

set_option maxHeartbeats 1550000 in
/-- The literal first transformed section record at the born chart is
the same as in the original double-zero example, on the genuine open
preimage of the source window. -/
theorem born_section_stage_chart_eq :
    pullback (Subtype.val : openPreimage B bornSectionWindow → HironakaG1LaterPositiveNormalExample.Y)
      (geoTransformAlong sectionRecord B) =
    pullback (Subtype.val : openPreimage B bornSectionWindow → HironakaG1LaterPositiveNormalExample.Y)
      (geoTransformAlong (sectionMarked originalBornSource) B) := by
  let X := HironakaG1TwoZeroBornCounts.X
  let W := bornSectionWindow
  let A := sectionRecord
  let C := sectionMarked originalBornSource
  have hA : IsInvDomain 2 A :=
    section_projected_domain 2 source.N source.E source.ideal source.d source_domain
  have hQ : IsInvDomain 2 originalBornSource := HironakaG1LaterAdvancedHeadNativeExample.Q_domain
  have hC : IsInvDomain 2 C := section_projected_domain 2 originalBornSource.N originalBornSource.E
    originalBornSource.ideal originalBornSource.d hQ
  have hPadTest := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (CanonicalCentres.invFamily (by decide : 0 < 3) 2) padded
    (properNormalMarked_isInvDomain source source_domain)
    (properNormalMarked_maximalOrder source source_domain.isWellFormed.isCoherent)
    (by decide : 0 < 3) B two_zero_first_blowup_common_canonical.1).2.1
  have hAT : IsGeoTestTower A B :=
    ((properNormalMarked_locWPEquiv_section source source_domain).wEquiv.2 B).1.mp hPadTest
  have hCT : IsGeoTestTower C B :=
    ((properNormalMarked_locWPEquiv_section originalBornSource hQ).wEquiv.2 B).1.mp
      HironakaG1LaterAdvancedHeadExample.joint_added_boundary_test.2
  have hStart : pullback (Subtype.val : W → X) A = pullback (Subtype.val : W → X) C :=
    section_window_record_eq bornSourceOpen sourceIdeal coordinatePairIdeal
      (isCoherent_finiteFunctionIdeal generator hGenerator)
      (isCoherent_finiteFunctionIdeal coordinatePairGenerator hOld) born_source_window_ideal_eq
  have hAEnd := geoTransformAlong_restrict W hA.isWellFormed.isClosedSubmanifold_N
    hA.isWellFormed.isCoherent B hAT
  have hCEnd := geoTransformAlong_restrict W hC.isWellFormed.isClosedSubmanifold_N
    hC.isWellFormed.isCoherent B hCT
  exact hAEnd.symm.trans ((congrArg (fun J => geoTransformAlong J (restrict W B)) hStart).trans hCEnd)

end
end Hironaka.HironakaG1TwoZeroSourceCharts
