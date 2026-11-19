import Hironaka.Resolution.HironakaG1LaterAdvancedHeadLeafExample
import Hironaka.Resolution.HironakaG1LaterPositiveSelectedExample

/-! The numerical leaf on the last literal selected curve. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterAdvancedHeadNumericalExample

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneLowerDomain MemberInterLocusAlong HomogenizedIdealAlong
  InvDomainMemberRestriction InvDomainCompanion InvDomainTowerAlong MarkedIdealRestrictOpen
  MarkedIdealBiholomorphism
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1PositiveNormalJointExample HironakaG1PositiveNormalNonspecialExample
  HironakaG1LaterPositiveNormalExample HironakaG1LaterPositiveSelectedExample
  HironakaG1LaterAdvancedHeadExample HironakaG1LaterAdvancedHeadCanonicalExample
  HironakaG1LaterPositiveSuccessorRead HironakaG1InitialPositiveGeneralRead
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialTransformAlong
  GeneralValue CompanionRebase CompanionReductionAlong CoefficientIdeal
  InvertibleIdealQuotient RelativePrincipalizationSpan GermIdealOrder
  MonomialPartEtale DerivativeIdealAlongEtale BlowupConstruction
  HironakaG1ProperNormalInitialRegime RestrictedIdealExtension MarkedIdealOperationsAlong
  HironakaG8MixedBoundaryExponents HironakaRelativeNormalIdeal
  CodimOneSupport CodimOneSupportAlong AnalyticIrreducibleComponents PositiveDimensionalComponent
  HironakaG1LaterAdvancedHeadLeafExample

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev C : Set X := {p}
private abbrev D (i : Fin 3) : Set X := {z | z.val i = 0}
private abbrev P : MarkedIdeal 3 X := properNormalMarked sourceRecord
private abbrev M : MarkedIdeal 3 X := {P with E := [D 0, D 1]}
private abbrev O := maskA M B q
private abbrev A := CMfd.of (n := 3) O
private abbrev L := lowerMarkedM M 1 B q
private abbrev e : BlowupTower A A := .refl
private abbrev W := ordMask (M := A) L 1
private abbrev V := CMfd.of (n := 3) W
private abbrev J := compAt (X := A) L 1 e
private abbrev E : BlowupTower V V := .refl
private abbrev R₂ := invFamily (by decide : 0 < 3) 2
private abbrev R₁ := invFamily (by decide : 0 < 3) 1
private abbrev R₀ := invFamily (by decide : 0 < 3) 0
private abbrev D' (i : Fin 3) : Set Y := geoStrictTransform π C (D i)
private abbrev F : Set Y := π ⁻¹' C
private abbrev φ (z : W) : Y := z.val.val
private abbrev c (z : Y) : ℂ := yChart.toFun z (2 : Fin 3)

private theorem J_mark : J.d = 1 := by
  obtain ⟨_, _, _, hd, _, _⟩ := joint_advanced_canonical_positive_successor
  exact hd

section LastMask

variable (z : W)

private abbrev O' := maskA J E z
private abbrev A' := CMfd.of (n := 3) (O' z)
private abbrev S := lowerMarkedM J 1 E z
private abbrev T' : BlowupTower (A' z) (A' z) := .refl
private abbrev r (x : O' z) : Y := φ x.val
private abbrev g (x : O' z) : ℂ := c (r z x)

private abbrev K' := memberRestrict J (membersThrough J.E J.E z)

set_option backward.isDefEq.respectTransparency false in
private theorem selected_carrier (hzF : φ z ∈ F) : (K' z).N = J.N ∩ φ ⁻¹' F := by
  have hE : ∀ H ∈ J.E, H ∈ J.E := fun _ h => h
  rw [memberRestrict_N, memberInter_membersThrough hE, J_boundary]
  ext x
  constructor
  · rintro ⟨hxN, hx⟩
    exact ⟨hxN, hx _ (by simp) hzF⟩
  · rintro ⟨hxN, hxF⟩
    refine ⟨hxN, ?_⟩
    intro H hH hzH
    rcases List.mem_cons.mp hH with rfl | hH
    · exact hzH.elim
    · rw [List.mem_singleton] at hH
      rw [hH]
      exact hxF

set_option backward.isDefEq.respectTransparency false in
private theorem selected_eq : S z = MarkedIdeal.pullback (Subtype.val : O' z → W) (K' z) := by
  change MarkedIdeal.pullback (Subtype.val : O' z → W)
    (memberRestrict (barMarked J) (membersThrough (barMarked J).E (origMembers J E) z)) = _
  have hOrig : origMembers J E = J.E := List.take_length
  rw [J_bar]
  erw [hOrig]

private theorem S_carrier (hzF : φ z ∈ F) :
    (S z).N = r z ⁻¹' (D' 0 ∩ F) := by
  rw [selected_eq]
  change (Subtype.val : O' z → W) ⁻¹' (K' z).N = _
  rw [selected_carrier z hzF, J_carrier]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem S_member (hJ : IsInvDomain 2 J) {x : O' z}
    (hx : r z x ∈ yChart.source) :
    (S z).ideal.mem x (g z) := by
  rw [selected_eq]
  have hK : (K' z).IsWellFormed := isWellFormed_memberRestrict (by decide) hJ.isWellFormed _
  have hMem : (K' z).ideal.mem x.val (c ∘ φ) := by
    rw [memberRestrict_ideal, coeffMarkedAlong_eq_of_mark_one J J_mark hJ.isWellFormed.isCoherent]
    exact J_normal_member hx
  exact comp_val_mem_pullback_val (O' z) hK.isCoherent hMem

set_option backward.isDefEq.respectTransparency false in
private theorem S_data (hJ : IsInvDomain 2 J) (hJz : z ∈ J.cosupp)
    (hLev : level J E z = 1) (hz : z ∈ O' z) :
    IsInvDomain 1 (S z) ∧ (⟨z, hz⟩ : O' z) ∈ (S z).cosupp := by
  have hTest : IsGeoTestTower (barMarked J) E := trivial
  refine ⟨isInvDomain_lowerMarked_succ (X := V) J hJ.isWellFormed hJ.one_le_d (by decide) E
    hTest hJ.dimLE hLev, ?_⟩
  rw [selected_eq]
  have hK : (K' z).IsWellFormed := isWellFormed_memberRestrict (by decide) hJ.isWellFormed _
  rw [cosupp_pullback_val _ (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hK.isCoherent h)]
  change z ∈ (K' z).cosupp
  rw [cosupp_memberRestrict hJ.isWellFormed hJ.one_le_d]
  exact ⟨hJz, fun i hi => (mem_membersThrough.mp hi).2⟩

private def chart : ComplexChart 3 Y :=
  ⟨yChart.homeo, atlasHomeo_mem_atlas yChart.toPartialEquiv (Or.inl ⟨yChart, rfl⟩)⟩

private def normalProjection : ComplexModel 3 →L[ℂ] ComplexModel 3 :=
  (ContinuousLinearMap.smulRight (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3))
    (EuclideanSpace.single (2 : Fin 3) (1 : ℂ)))

private abbrev f (w : ComplexModel 3) : Y := yChart.invFun (normalProjection w)

set_option backward.isDefEq.respectTransparency false in
private theorem germ_curve (hzF : φ z ∈ F) (hz : z ∈ O' z) (hAnchor : φ z = q) :
    ∃ θ : ComplexModel 3 → O' z,
      θ 0 = ⟨z, hz⟩ ∧
      (∀ᶠ w : ComplexModel 3 in 𝓝 0,
        MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) θ w) ∧
      ∀ᶠ w : ComplexModel 3 in 𝓝 0, θ w ∈ (S z).N ∧ g z (θ w) = w (2 : Fin 3) := by
  let x : O' z := ⟨z, hz⟩
  let ψ₁ := openInv O z.val
  let ψ₂ := openInv W z
  let ψ₃ := openInv (O' z) x
  have h₁ := isLocalInverseAt_val (n := 3) O z.val
  have h₂ := isLocalInverseAt_val (n := 3) W z
  have h₃ := isLocalInverseAt_val (n := 3) (O' z) x
  have hf₀ : f 0 = q := by
    change yChart.invFun (normalProjection 0) = yChart.invFun 0
    rw [map_zero]
  have hfDiff (w : ComplexModel 3) :
      MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) f w := by
    have hT : normalProjection w ∈ chart.val.target := chart_all (normalProjection w)
    exact (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel 3)) chart.property hT).comp w
      normalProjection.mdifferentiableAt
  have hf : Tendsto f (𝓝 0) (𝓝 q) := by
    rw [← hf₀]
    exact (hfDiff 0).continuousAt.tendsto
  have hs₁ : Tendsto ψ₁ (𝓝 q) (𝓝 z.val) := by
    rw [← hAnchor]
    exact h₁.tendsto
  have hs₂ : Tendsto ψ₂ (𝓝 z.val) (𝓝 z) := h₂.tendsto
  let θ := ψ₃ ∘ ψ₂ ∘ ψ₁ ∘ f
  have hAt : θ 0 = x := by
    change ψ₃ (ψ₂ (ψ₁ (f 0))) = x
    have h₁z : ψ₁ (φ z) = z.val := h₁.left_inv.self_of_nhds
    have h₂z : ψ₂ z.val = z := h₂.left_inv.self_of_nhds
    rw [hf₀, ← hAnchor, h₁z, h₂z]
    exact h₃.left_inv.self_of_nhds
  have hNear₁ : ∀ᶠ w in 𝓝 0, (ψ₁ (f w)).val = f w := by
    have hNear : ∀ᶠ y in 𝓝 q, (ψ₁ y).val = y := by
      rw [← hAnchor]
      exact h₁.right_inv
    exact hf.eventually hNear
  refine ⟨θ, hAt, ?_, ?_⟩
  · have hm₁ : ∀ᶠ w in 𝓝 0, MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) ψ₁ (f w) := by
      have hNear : ∀ᶠ y in 𝓝 q, MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) ψ₁ y := by
        rw [← hAnchor]
        exact h₁.mdiff_inv
      exact hf.eventually hNear
    filter_upwards [hm₁, (hs₁.comp hf).eventually h₂.mdiff_inv,
      (hs₂.comp (hs₁.comp hf)).eventually h₃.mdiff_inv] with w hw₁ hw₂ hw₃
    exact hw₃.comp w (hw₂.comp w (hw₁.comp w (hfDiff w)))
  · have hNear₂ := (hs₁.comp hf).eventually h₂.right_inv
    have hNear₃ := (hs₂.comp (hs₁.comp hf)).eventually h₃.right_inv
    filter_upwards [hNear₁, hNear₂, hNear₃] with w hw₁ hw₂ hw₃
    have hVal : r z (θ w) = f w := by
      change (ψ₃ (ψ₂ (ψ₁ (f w)))).val.val.val = f w
      change (ψ₂ (ψ₁ (f w))).val = ψ₁ (f w) at hw₂
      change (ψ₃ (ψ₂ (ψ₁ (f w)))).val = ψ₂ (ψ₁ (f w)) at hw₃
      rw [hw₃, hw₂, hw₁]
    obtain ⟨_, hD, hF, hg⟩ := normal_line (w (2 : Fin 3))
    change f w ∈ D' 0 at hD
    change f w ∈ F at hF
    change c (f w) = w (2 : Fin 3) at hg
    refine ⟨?_, ?_⟩
    · rw [S_carrier z hzF]
      change r z (θ w) ∈ D' 0 ∩ F
      rw [hVal]
      exact ⟨hD, hF⟩
    · change c (r z (θ w)) = _
      rw [hVal, hg]

private theorem chart_intersection_zero (w : Y) (hV : w ∈ yChart.source)
    (hD : w ∈ D' 0) (hF : w ∈ F) (hC : c w = 0) : w = q := by
  have h0 := (strict_chart_coordinate 0 (by decide) w hV).mp hD
  have hp : π w = p := mem_singleton_iff.mp hF
  have hp0 : p.val = 0 := map_zero (tangentInclusion 2 1)
  have h1 := congrArg (fun x : X => x.val (1 : Fin 3)) hp
  change (π w).val (1 : Fin 3) = p.val (1 : Fin 3) at h1
  rw [chart_projection w hV, hp0, monomial_apply, if_neg (by simp)] at h1
  apply yChart.toPartialEquiv.injOn hV chart_q.1
  change yChart.toFun w = yChart.toFun q
  rw [chart_q.2]
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact hC

set_option backward.isDefEq.respectTransparency false in
private theorem nmPart_eq (hE : (S z).E = [∅]) :
    nmPart (M := A' z) (S z) = restrictOn 3 (S z).N (S z).ideal := by
  apply nonmonomial_eq_restrictOn_of_boundary_zero (X := A' z)
  intro H hH x
  rw [hE, List.mem_singleton] at hH
  subst H
  exact divExpAlong_eq_zero_of_notMem (by simp) (fun h => h.2)

set_option maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem selected_order_one (hz : z ∈ O' z) (hAnchor : φ z = q)
    (hzF : φ z ∈ F) (hJ : IsInvDomain 2 J) (hS : IsInvDomain 1 (S z))
    (hx : (⟨z, hz⟩ : O' z) ∈ (S z).cosupp) (hd : (S z).d = 1) (hE : (S z).E = [∅]) :
    nmOrd (M := A' z) (S z) (⟨z, hz⟩ : O' z) = 1 := by
  let x : O' z := ⟨z, hz⟩
  have hOne : x ∈ ordGe (M := A' z) (S z) 1 := by
    change x ∈ cosupport 3 (S z).N (nmPart (M := A' z) (S z)) 1
    rw [nmPart_eq z hE]
    have hx₁ := hx
    change x ∈ cosupport 3 (S z).N (S z).ideal (S z).d at hx₁
    rw [hd] at hx₁
    exact cosupport_subset_of_restrictLe restrictLe_restrictOn 1 hx₁
  have hTwo : x ∉ ordGe (M := A' z) (S z) 2 := by
    intro h
    have hxV : r z x ∈ yChart.source := by
      change φ z ∈ yChart.source
      rw [hAnchor]
      exact chart_q.1
    have hg := S_member z hJ hxV
    have hgN := le_nonmonomialPartAlong_self (N := (S z).N) (E := (S z).E)
      hS.isWellFormed.isCoherent x _ hg
    obtain ⟨θ, hθ₀, hθ, hNear⟩ := germ_curve z hzF hz hAnchor
    have hVan : VanishesToOrderOn 3 (S z).N (θ 0) 2 (g z) := by
      rw [hθ₀]
      exact h.2 _ hgN
    obtain ⟨b, hb, hEq⟩ := vanishesToOrderOn_comp (θ := θ) (p := (0 : ComplexModel 3)) hθ hVan
    have hSame : (fun w : ComplexModel 3 => w (2 : Fin 3)) =ᶠ[𝓝 0] b := by
      filter_upwards [hEq, hNear] with w he hn
      exact hn.2.symm.trans (he hn.1)
    let Φ : LocalHolomorphicEquivAt (n := 3) (chartAt (ComplexModel 3) (0 : ComplexModel 3) 0) :=
      BlowupExistenceOriginIdeal.idEquivAt
    exact MonomialCase.flatCoord_notMem_idealPow_two Φ 2 (mem_flatDomain_self Φ)
      (OrderTaylor.mem_idealPow_congr hb hSame.symm)
  exact Nat.le_antisymm (nmOrd_le_of_notMem hTwo) (succ_le_nmOrd_of_mem ⟨1, hTwo⟩ hOne)

private abbrev O'' := ordMask (M := A' z) (S z) 1
private abbrev A'' := CMfd.of (n := 3) (O'' z)
private abbrev Q := compAt (X := A' z) (S z) 1 (T' z)
private abbrev T'' : BlowupTower (A'' z) (A'' z) := .refl

set_option backward.isDefEq.respectTransparency false in
private theorem Q_carrier : (Q z).N = (Subtype.val : O'' z → O' z) ⁻¹' (S z).N := by
  simp only [Q, compAt, companionOf, companionAlong_N]
  rfl

private theorem Q_mark (hd : (S z).d = 1) : (Q z).d = 1 := by
  simp only [Q, compAt, companionOf, companionAlong_d]
  change (if 1 < (S z).d then 1 * ((S z).d - 1) else 1) = _
  simp [hd]

set_option backward.isDefEq.respectTransparency false in
private theorem Q_boundary (hE : (S z).E = [∅]) : (Q z).E = [∅] := by
  simp only [Q, compAt, companionOf, companionAlong_E]
  change (S z).E.map ((Subtype.val : O'' z → O' z) ⁻¹' ·) = _
  rw [hE]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem Q_member (hS : IsInvDomain 1 (S z)) (hd : (S z).d = 1)
    {x : O'' z} (hg : (S z).ideal.mem x.val (g z)) :
    (Q z).ideal.mem x (g z ∘ (Subtype.val : O'' z → O' z)) := by
  let I : MarkedIdeal 3 (A'' z) := MarkedIdeal.pullback (M' := A'' z)
    (Subtype.val : O'' z → O' z) (S z)
  have hI := (isInvDomain_pullback_val (M := A' z) (𝔪 := S z) (O'' z) hS).isWellFormed.isCoherent
  have hMem : I.ideal.mem x (g z ∘ (Subtype.val : O'' z → O' z)) :=
    comp_val_mem_pullback_val (O'' z) hS.isWellFormed.isCoherent hg
  have hNm := le_nonmonomialPartAlong_self (N := I.N) (E := I.E) hI x _ hMem
  change (companionOf 3 (M := A'' z) I 1).ideal.mem x _
  rw [companionOf, companionAlong_ideal, show I.d = 1 from hd, if_neg (by decide : ¬ 1 < 1)]
  exact hNm

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem Q_special (hzF : φ z ∈ F) (hAnchor : φ z = q) (hJ : IsInvDomain 2 J)
    (hS : IsInvDomain 1 (S z)) (hd : (S z).d = 1) (hE : (S z).E = [∅])
    (hz : z ∈ O' z) (hy : (⟨z, hz⟩ : O' z) ∈ O'' z)
    (hQ : IsInvDomain 1 (Q z)) (hCos : (⟨⟨z, hz⟩, hy⟩ : O'' z) ∈ (Q z).cosupp) :
    IsSpecial (Q z) (T'' z) (⟨⟨z, hz⟩, hy⟩ : O'' z) := by
  let x : O' z := ⟨z, hz⟩
  let y : O'' z := ⟨x, hy⟩
  have hg0 : g z x = 0 := by
    change c (φ z) = 0
    rw [hAnchor]
    change yChart.toFun q (2 : Fin 3) = 0
    simp [chart_q.2]
  have hLvl : level (Q z) (T'' z) y = 0 := by
    have ho : origMembers (Q z) (T'' z) = (Q z).E := List.take_length
    unfold level
    rw [ho, Q_boundary z hE]
    simp [BoundaryCount.boundaryCount]
  have hQd := Q_mark z hd
  have hBar : barMarked (Q z) = Q z := by
    change coeffMarkedAlong (homMarkedAlong (Q z)) = Q z
    have hI := hQ.isWellFormed.isCoherent
    rw [homMarkedAlong_eq_of_mark_one (Q z) hQd hI, coeffMarkedAlong_eq_of_mark_one (Q z) hQd hI]
  have hyN : y ∈ (Q z).N := hCos.1
  obtain ⟨k, hk, hReg⟩ := hQ.dimLE y hyN
  have hNot0 : k ≠ 0 := by
    intro h0
    rw [h0] at hReg
    obtain ⟨U, hU, hyU, hIso⟩ := exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hReg
    obtain ⟨θ, hθ₀, hθ, hNear⟩ := germ_curve z hzF hz hAnchor
    have hθT : Tendsto θ (𝓝 0) (𝓝 x) := by
      have heq : θ 0 = x := hθ₀
      rw [← heq]
      exact hθ.self_of_nhds.continuousAt.tendsto
    let ψ := openInv (O'' z) y
    have hψ := isLocalInverseAt_val (n := 3) (O'' z) y
    have hT : Tendsto (ψ ∘ θ) (𝓝 0) (𝓝 y) := hψ.tendsto.comp hθT
    have hNear' : ∀ᶠ w : ComplexModel 3 in 𝓝 0,
        ψ (θ w) ∈ U ∧ (ψ (θ w)).val = θ w ∧ θ w ∈ (S z).N ∧ g z (θ w) = w (2 : Fin 3) := by
      exact (hT.eventually (hU.mem_nhds hyU)).and ((hθT.eventually hψ.right_inv).and hNear)
    obtain ⟨w, ⟨hwU, hwV, hwN, hwG⟩, hw0⟩ :=
      exists_coord_ne_zero_of_mem_nhds hNear' (2 : Fin 3)
    have hwQ : ψ (θ w) ∈ (Q z).N := by
      rw [Q_carrier]
      change (ψ (θ w)).val ∈ (S z).N
      rw [hwV]
      exact hwN
    have heq : ψ (θ w) = y := hIso ⟨hwQ, hwU⟩
    rw [heq] at hwV
    rw [← hwV, hg0] at hwG
    exact hw0 hwG.symm
  have hRegN : RegularAtDim (n := 3) (Q z).N y 1 := by
    have h : k = 1 := by omega
    rw [h] at hReg
    exact hReg
  have hMap : Continuous (r z ∘ (Subtype.val : O'' z → O' z)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_subtype_val))
  have hyV : r z y.val ∈ yChart.source := by
    change φ z ∈ yChart.source
    rw [hAnchor]
    exact chart_q.1
  have hLoc : ∀ᶠ u in 𝓝 y, u ∈ (Q z).cosupp ↔ u ∈ ({y} : Set (O'' z)) := by
    filter_upwards [hMap.continuousAt.eventually (yChart.isOpen_source.mem_nhds hyV)] with u hu
    constructor
    · intro h
      have huN : u.val ∈ (S z).N := by
        have hN := h.1
        change u ∈ (Q z).N at hN
        rw [Q_carrier] at hN
        exact hN
      have hDF : r z u.val ∈ D' 0 ∩ F := by
        rw [S_carrier z hzF] at huN
        exact huN
      have hG := Q_member z hS hd (S_member z hJ hu)
      have hHol := GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hG
      have hVan := h.2 _ hG
      rw [hQd] at hVan
      have h0 := (vanishesToOrderOn_one_iff h.1 hHol).mp hVan
      have heq := chart_intersection_zero (r z u.val) hu hDF.1 hDF.2 h0
      apply mem_singleton_iff.mpr
      exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext (heq.trans hAnchor.symm))))
    · intro heq
      rw [mem_singleton_iff.mp heq]
      exact hCos
  have hSingle : RegularAtDim (n := 3) ({y} : Set (O'' z)) y 0 := by
    obtain ⟨Φ, hΦ, hzero⟩ := NormalCrossings.exists_centred_coordinates (n := 3) y
    refine ⟨by decide, mem_singleton _, Φ, hΦ, hzero, ?_⟩
    intro w hw hwΦ
    constructor
    · intro hw'
      rw [mem_singleton_iff.mp hw', hzero]
      rw [← BlowupExistenceOriginIdeal.zero_eq_complexCoordinatePlane]
      exact mem_singleton _
    · intro hP
      rw [← BlowupExistenceOriginIdeal.zero_eq_complexCoordinatePlane] at hP
      apply mem_singleton_iff.mpr
      apply (complexChartAt (n := 3) y).val.injOn hw (mem_complexChartAt_source y)
      have heq : Φ.toFun ((complexChartAt (n := 3) y).val w) =
          Φ.toFun ((complexChartAt (n := 3) y).val y) :=
        (mem_singleton_iff.mp hP).trans hzero.symm
      have hInv := congrArg Φ.invFun heq
      rwa [Φ.left_inv _ hwΦ, Φ.left_inv _ Φ.center_mem_source] at hInv
  have hRegCos := regularAtDim_of_eventually_mem_iff (hLoc.mono fun _ h => h.symm) hSingle
  refine Or.inl ⟨hLvl, ?_⟩
  change y ∈ codimOnePartAlong (barMarked (Q z)).N (barMarked (Q z)).ideal (barMarked (Q z)).d
  rw [hBar]
  exact ⟨0, hRegN, hRegCos⟩

set_option maxHeartbeats 750000 in
set_option backward.isDefEq.respectTransparency false in
private theorem selected_leaf_value (hz : z ∈ O' z) (hAnchor : φ z = q)
    (hzF : φ z ∈ F) (hJ : IsInvDomain 2 J) (hzJ : z ∈ J.cosupp) (hL : level J E z = 1)
    (hd : (S z).d = 1) (hE : (S z).E = [∅]) :
    R₁.inv (S z) (T' z) (⟨z, hz⟩ : O' z) =
      positiveSuccessorRead 1 (toLex (0, (⊤ : WithTop (ValTy 0)))) := by
  obtain ⟨hS, hx⟩ := S_data z hJ hzJ hL hz
  have hOrd := selected_order_one z hz hAnchor hzF hJ hS hx hd hE
  have h := original_positive_order_successor_read (k := 0) (by decide : 0 < 3) (X := A' z)
    (S z) hS (T' z) trivial (⟨z, hz⟩ : O' z) hx 1 hOrd (by decide)
  obtain ⟨hy, hQ, _, _, hCos, hVal⟩ := h
  have hSp := Q_special z hzF hAnchor hJ hS hd hE hz hy hQ hCos
  have hLevel : level (Q z) (T'' z) (⟨⟨z, hz⟩, hy⟩ : O'' z) = 0 := by
    have ho : origMembers (Q z) (T'' z) = (Q z).E := List.take_length
    unfold level
    rw [ho, Q_boundary z hE]
    simp [BoundaryCount.boundaryCount]
  have hStep : Seq.StepOneValueMasked.stepOneInvM (X := A'' z) R₀ (Q z) (T'' z)
      (⟨⟨z, hz⟩, hy⟩ : O'' z) = toLex (0, (⊤ : WithTop (ValTy 0))) := by
    change Seq.StepOneValueMasked.stepOneInvL (X := A'' z) R₀ (Q z) (lowerMarkedM (Q z))
      (T'' z) (⟨⟨z, hz⟩, hy⟩ : O'' z) = _
    rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R₀ (Q z) (lowerMarkedM (Q z)) (T'' z) hSp,
      hLevel]
  exact hVal.trans (congrArg (positiveSuccessorRead 1) hStep)

end LastMask

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The finite born-positive leaf of the actual canonical advanced head
has order one, then a special level-zero branch on the last selected curve. -/
theorem joint_advanced_head_exact_upper_value :
    Seq.StepOneValueMasked.stepOneInvM R₂ M B q =
      toLex (1, (positiveSuccessorRead 1
        (toLex (1, (↑(positiveSuccessorRead 1 (toLex (0, (⊤ : WithTop (ValTy 0))))) :
          WithTop (ValTy 1)))) : WithTop (ValTy 2))) := by
  obtain ⟨hq, hw, _, hd, hE, hz, _, hUpper⟩ := joint_advanced_head_finite_inner_leaf
  let z : W := ⟨⟨q, hq⟩, hw⟩
  obtain ⟨hJ, _, hCos⟩ := J_data hq hw
  have hLev : level J E z = 1 := by
    obtain ⟨_, hq', hw', _, hLev', _⟩ := joint_advanced_canonical_positive_successor
    have heq : (⟨⟨q, hq'⟩, hw'⟩ : W) = z := rfl
    rw [← heq]
    exact hLev'
  have hF : φ z ∈ F := by
    change π q ∈ C
    have hqp : π q = p := joint_first_point_blowup_positive_normal_contact.2.2.2.1
    rw [hqp]
    exact mem_singleton _
  have hLeaf := selected_leaf_value z hz rfl hF hJ hCos hLev hd hE
  exact hUpper.trans (congrArg (fun v : ValTy 1 =>
    toLex (1, (positiveSuccessorRead 1 (toLex (1, (v : WithTop (ValTy 1)))) :
      WithTop (ValTy 2)))) hLeaf)

end
end Hironaka.HironakaG1LaterAdvancedHeadNumericalExample
