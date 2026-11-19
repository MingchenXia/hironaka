import Hironaka.Resolution.HironakaG34JointMaskEquivariance
import Hironaka.Resolution.HironakaG1RecursiveBornOrderTwoBarExample

/-! Coordinate differentiation on the actual middle chart and its transfer
to the literal order-two companion. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1RecursiveBornOrderTwoTangentExample
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  HironakaRelativeNormalIdeal HironakaActualOpenZeroSectionDifferentials
  HironakaActualNativeSectionInitialBar
  HironakaG1LaterPositiveNormalExample HironakaG1RecursiveBornFiniteExample
  HironakaG1RecursiveBornOrderExample HironakaG1RecursiveBornResidualExample
  GermIdealOrder RelativePrincipalizationSpan DerivativeIdeal DerivativeIdealAlong
  DerivativeIdealAlongCoherent TangentDirectionAlong InvertibleIdealQuotient
  DerivativeIdealAlongTransform CompanionReduction

private abbrev U₀ : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U₀)
private abbrev p : X := zeroSection U₀ ⟨0, mem_univ _⟩
private abbrev F : Set Y := π ⁻¹' ({p} : Set X)
private abbrev Q₀ := geoTransformAlong record B
private abbrev coord (i : Fin 3) (z : Y) : ℂ := yChart.toFun z i
private def e : ComplexChart 3 Y :=
  ⟨yChart.homeo, atlasHomeo_mem_atlas yChart.toPartialEquiv (Or.inl ⟨yChart, rfl⟩)⟩
private def field (i : Fin 3) (_ : Y) : ℂ := if i = 0 then 1 else 0
private def v : ComplexModel 3 := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)

private theorem born_iff {z : Y} (hz : z ∈ yChart.source) :
    z ∈ F ↔ coord 1 z = 0 := by
  have hp : p.val = 0 := map_zero (tangentInclusion 2 1)
  constructor
  · intro h
    have hi := congrArg (fun x : X => x.val (1 : Fin 3)) (mem_singleton_iff.mp h)
    change (π z).val (1 : Fin 3) = p.val (1 : Fin 3) at hi
    rw [chart_projection z hz, hp, monomial_apply] at hi
    simpa using hi
  · intro he
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    rw [chart_projection z hz, hp]
    ext i
    by_cases hi : i = 1
    · subst i
      simpa [monomial_apply] using he
    · simp [monomial_apply, hi, he]

private theorem field_eq (g : Y → ℂ) (z : Y) : fieldDeriv e field g z = chartDeriv e v g z := by
  classical
  simp [fieldDeriv, field, v]

private theorem coord_deriv_at {z : Y} (_hz : z ∈ yChart.source) :
    fieldDeriv e field (coord 0) z = 1 := by
  rw [field_eq]
  change fderiv ℂ (coord 0 ∘ yChart.invFun) (yChart.toFun z) v = 1
  have hEq : (coord 0 ∘ yChart.invFun) = fun u : ComplexModel 3 => u (0 : Fin 3) := by
    funext u
    have hh : yChart.toFun (yChart.invFun u) = u := yChart.toPartialEquiv.right_inv (chart_all u)
    change yChart.toFun (yChart.invFun u) (0 : Fin 3) = u (0 : Fin 3)
    rw [hh]
  rw [hEq]
  change fderiv ℂ (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)) (yChart.toFun z) v = 1
  rw [ContinuousLinearMap.fderiv]
  simp [v]

private theorem field_tangent {x : Y} (hx : x ∈ yChart.source) :
    IsTangentField F e field x := by
  have hx' : x ∈ e.val.source := hx
  have hHol (m : Fin 3) : HolomorphicAt 3 (field m) x := holomorphicAt_const _
  refine ⟨hx', hHol, fun g hg => ⟨holomorphicAt_fieldDeriv hx' hHol hg.1, ?_⟩⟩
  have hV := hg.2.eventually_nhds
  filter_upwards [hV, hg.1.eventually_nhds, yChart.isOpen_source.mem_nhds hx] with z hzV hzG hz hF
  let w := yChart.toFun z
  have hw : w (1 : Fin 3) = 0 := (born_iff hz).mp hF
  have hInv : Tendsto yChart.invFun (𝓝 w) (𝓝 z) := yChart.homeo.tendsto_symm (x := z) hz
  let line : ℂ → ComplexModel 3 := fun t => w + ((1 : ℂ →L[ℂ] ℂ).smulRight v) t
  have hline : HasFDerivAt line ((1 : ℂ →L[ℂ] ℂ).smulRight v) 0 := by
    simpa only [line] using (((1 : ℂ →L[ℂ] ℂ).smulRight v).hasFDerivAt (x := (0 : ℂ))).const_add w
  have hT : Tendsto line (𝓝 0) (𝓝 w) := by
    simpa [line] using hline.continuousAt.tendsto
  have hZero : (fun t => g (yChart.invFun (line t))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [(hInv.comp hT).eventually hzV] with t ht
    apply ht
    have hs := yChart.toPartialEquiv.map_target (chart_all (line t))
    have hr : yChart.toFun (yChart.invFun (line t)) = line t :=
      yChart.toPartialEquiv.right_inv (chart_all (line t))
    apply (born_iff hs).mpr
    change yChart.toFun (yChart.invFun (line t)) (1 : Fin 3) = 0
    rw [hr]
    simp [line, v, hw]
  have hGD : DifferentiableAt ℂ (g ∘ yChart.invFun) w := by
    have hLeft : yChart.invFun w = z := yChart.toPartialEquiv.left_inv hz
    have hMd := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel 3)) e.property (chart_all w)
    have hAt := hzG.self_of_nhds
    have hg' : MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) g (yChart.invFun w) := by
      rw [hLeft]
      exact hAt
    exact mdifferentiableAt_iff_differentiableAt.mp (hg'.comp w hMd)
  have hL0 : line 0 = w := by simp [line]
  have hGD' : HasFDerivAt (g ∘ yChart.invFun) (fderiv ℂ (g ∘ yChart.invFun) w) (line 0) :=
    hL0.symm ▸ hGD.hasFDerivAt
  have hComp := hGD'.comp (0 : ℂ) hline
  have hDeq := hZero.fderiv_eq (𝕜 := ℂ)
  change fderiv ℂ ((g ∘ yChart.invFun) ∘ line) 0 = fderiv ℂ (fun _ : ℂ => (0 : ℂ)) 0 at hDeq
  rw [hComp.fderiv, fderiv_const_apply] at hDeq
  have ht := congrArg (fun d : ℂ →L[ℂ] ℂ => d 1) hDeq
  rw [field_eq]
  change fderiv ℂ (g ∘ yChart.invFun) w v = 0
  simpa using ht

open MonomialPartAlong InvDomainTowerAlong NormalCrossings
  RestrictedIdealExtension HomogenizedGlueing GermIdealPullbackCalculus BlowupSNCTransform MonomialPart

private abbrev I := nonmonomialPartAlong 3 Q₀.N Q₀.ideal Q₀.E
private abbrev K := restrictOn 3 F I

private theorem coherent_I : I.IsCoherent := by
  have h := isInvDomain_geoTransformAlong domain B test
  exact isCoherent_nonmonomialPartAlong (by decide : 0 < 3) h.isWellFormed.isClosedSubmanifold_N
    h.isWellFormed.isSNCDivisor h.isWellFormed.isTransverse h.isWellFormed.isCoherent h.isNonzeroAlongAt

private theorem F_smooth : IsClosedSubmanifold 3 F := by
  have h := isInvDomain_geoTransformAlong domain B test
  have hS : IsSNCDivisor 3 [F] := (show Q₀.E = [F] from stage_boundary) ▸ h.isWellFormed.isSNCDivisor
  exact isClosedSubmanifold_get (by decide : 0 < 3) hS (0 : Fin 1)

private theorem coherent_K : K.IsCoherent :=
  isCoherent_restrictOn coherent_I (VanishingIdealCoherent.isCoherent_vanishingIdeal F_smooth)

private theorem square_mem (i : Fin 3) (hi : i ≠ 1) : K.mem q (fun z => coord i z ^ 2) := by
  have he : (fun z => coord i z ^ 2) = residualGen i := by
    funext z
    simp [residualGen, coord, hi]
  have hf : HolomorphicAt 3 (fun z => coord i z ^ 2) q :=
    holomorphicAt_pow_of (yChart.holomorphicAt_coord chart_q.1 i) 2
  apply le_restrictOn coherent_I
  apply (residual_span _).mpr
  exact isInSpanAt_self ⟨i, he⟩ hf

/-- The first ratio coordinate is a genuine mark-two tangent direction
for the exact restricted residual in the actual middle chart. -/
theorem ambient_coordinate_tangent :
    ∃ V : Opens Y, q ∈ V ∧ IsTangentDirectionAlong F K 2 V (coord 0) := by
  have hNear := eventually_mem coherent_K (square_mem 0 (by decide))
  obtain ⟨V, hSub, hV, hqV⟩ := eventually_nhds_iff.mp
    (hNear.and (yChart.isOpen_source.mem_nhds chart_q.1))
  refine ⟨⟨V, hV⟩, hqV, hV, ?_, ?_⟩
  · intro x hx
    have h := hSub x hx
    have hu := yChart.holomorphicAt_coord h.2 0
    have hs : DerivGenAlong F K x (fieldDeriv e field (fun z => coord 0 z ^ 2)) :=
      Or.inr (Or.inr ⟨e, field, _, field_tangent h.2, h.1, rfl⟩)
    change (derivIdealAlong F K).mem x (coord 0)
    refine isInSpanAt_of_eq_mul hs hu (holomorphicAt_const (2⁻¹ : ℂ)) ?_
    have hp := fieldDeriv_pow (ξ := field) (show x ∈ e.val.source from h.2) hu 1
    filter_upwards [hp, yChart.isOpen_source.mem_nhds h.2] with y hy hyV
    rw [hy, coord_deriv_at hyV]
    simp
    ring
  · intro x hx _
    exact ⟨e, field, field_tangent (hSub x hx).2, by rw [coord_deriv_at (hSub x hx).2]; exact one_ne_zero⟩

open ResolutionInvariantSpec GeneralValue NonmonomialOrderTail
  StepOneValue StepOneValueMasked CompanionRebase CompanionReductionAlong
  MarkedIdealBiholomorphism HironakaG34JointMaskEquivariance DerivativeIdealAlongEtale
  ContactEquivalenceAlong MonomialPartEtale BlowupRestrictOpen
  HironakaG1RecursiveBornOrderTwoCompanionExample
  HironakaG1RecursiveBornResidualExample HironakaG1PositiveNormalNonspecialExample HomogenizedIdealAlong
  StepOneLowerDomain CodimOneSupportAlong CodimOneSupport AnalyticSubsetOpens
  SNCGlobalPrimeComponents RegularPointDimension MarkedIdealRestrictOpen BoundaryCount

private abbrev W := ordMask (M := Y) Q₀ 1
private abbrev V := CMfd.of (n := 3) W
private abbrev J : MarkedIdeal 3 V := compAt record 1 B
private abbrev R : BlowupTower V V := .refl
private abbrev O (z : W) := maskA J R z
private abbrev L (z : W) := lowerMarkedM J 1 R z

private theorem J_ideal :
    J.ideal = GermIdeal.pullback (m := 3) (Subtype.val : W → Y) I := by
  have hA := isInvDomain_geoTransformAlong domain B test
  have hH := hA.isWellFormed
  have hM := isCoherent_monomialPartAlong (by decide : 0 < 3) hH.isClosedSubmanifold_N
    hH.isSNCDivisor hH.isTransverse hH.isCoherent hA.isNonzeroAlongAt
  let R' : MarkedIdeal 3 V := MarkedIdeal.pullback (Subtype.val : W → Y) Q₀
  have hR' : R'.d = 1 := rfl
  change (companionOf 3 (M := V) R' 1).ideal = _
  rw [companionOf, companionAlong_ideal, hR', if_neg (by decide : ¬ 1 < 1)]
  exact (pullback_nonmonomialPartAlong (fun u => ⟨_, isLocalInverseAt_val (n := 3) W u⟩)
    hH.isCoherent hM coherent_I).symm

private theorem L_ideal (z : W) (hJ : J.ideal.IsCoherent) :
    (L z).ideal = GermIdeal.pullback (m := 3) (Subtype.val : O z → W) J.ideal := by
  have hMark : J.d = 1 := by simp only [J, compAt, companionOf, companionAlong_d]; rfl
  have hBar : barMarked J = J := by
    change coeffMarkedAlong (homMarkedAlong J) = J
    rw [homMarkedAlong_eq_of_mark_one J hMark hJ, coeffMarkedAlong_eq_of_mark_one J hMark hJ]
  have hk : (coeffMarkedAlong (barMarked J)).ideal = J.ideal := by
    rw [hBar, coeffMarkedAlong_eq_of_mark_one J hMark hJ]
  change GermIdeal.pullback (m := 3) (Subtype.val : O z → W) (coeffMarkedAlong (barMarked J)).ideal = _
  rw [hk]

private theorem tangent_open {M : CMfd.{0} 3} (U : Opens M) {D : Set M} {A : GermIdeal 3 M}
    (hA : A.IsCoherent) {S : Set M} {g : M → ℂ}
    (ht : IsTangentDirectionAlong D A 2 S g) :
    IsTangentDirectionAlong ((Subtype.val : U → M) ⁻¹' D)
      (GermIdeal.pullback (m := 3) (Subtype.val : U → M) A) 2
      ((Subtype.val : U → M) ⁻¹' S) (g ∘ Subtype.val) :=
  isTangentDirectionAlong_pullback (fun u : U => ⟨_, isLocalInverseAt_val (n := 3) U u⟩)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hA hg) ht

private theorem restrict_open {M : CMfd.{0} 3} (U : Opens M) {D : Set M} {A : GermIdeal 3 M}
    (hD : IsClosedSubmanifold 3 D) (hA : A.IsCoherent) :
    GermIdeal.pullback (m := 3) (Subtype.val : U → M) (restrictOn 3 D A) =
      restrictOn 3 ((Subtype.val : U → M) ⁻¹' D)
        (GermIdeal.pullback (m := 3) (Subtype.val : U → M) A) :=
  pullback_restrictOn_of_local (M := M) (M' := CMfd.of (n := 3) U) (f := (Subtype.val : U → M)) (fun u : U => ⟨_, isLocalInverseAt_val (n := 3) U u⟩) hD hA

private theorem singleton_regular {M : CMfd.{0} 3} (x : M) :
    RegularAtDim (n := 3) ({x} : Set M) x 0 := by
  let e := complexChartAt (n := 3) x
  let q := e.val x
  let Φ : LocalHolomorphicEquivAt (n := 3) q := {
    source := e.val.target
    target := (fun w : ComplexModel 3 => w + q) ⁻¹' e.val.target
    isOpen_source := e.val.open_target
    isOpen_target := e.val.open_target.preimage (continuous_id.add_const q)
    center_mem_source := e.val.map_source (mem_complexChartAt_source x)
    toFun := fun z => z - q
    invFun := fun z => z + q
    toFun_holomorphic := (differentiable_id.sub_const q).differentiableOn
    invFun_holomorphic := (differentiable_id.add_const q).differentiableOn
    mapsTo_toFun := by intro z hz; simpa only [mem_preimage, sub_add_cancel] using hz
    mapsTo_invFun := fun _ hw => hw
    left_inv := fun z _ => sub_add_cancel z q
    right_inv := fun z _ => add_sub_cancel_right z q }
  refine ⟨Nat.zero_le 3, mem_singleton _, Φ, Subset.rfl, sub_self q, ?_⟩
  intro y hy _
  constructor
  · intro hyx
    rw [mem_singleton_iff.mp hyx]
    change q - q ∈ complexCoordinatePlane 3 0
    rw [sub_self]
    intro i _
    rfl
  · intro hz
    have heq : e.val y - q = 0 := by
      ext i
      exact hz i (Nat.zero_le _)
    exact mem_singleton_iff.mpr (e.val.injOn hy (mem_complexChartAt_source x) (sub_eq_zero.mp heq))

set_option maxHeartbeats 1100000 in
/-- The prescribed first coordinate really is tangent on a neighborhood
inside the literal order-two mask. Its ordered boundary is empty. -/
theorem actual_order_two_coordinate_tangent :
    ∃ (hq : q ∈ W) (hz : (⟨q, hq⟩ : W) ∈ O ⟨q, hq⟩),
      let z : W := ⟨q, hq⟩
      let Z := CMfd.of (n := 3) (O z)
      let x : O z := ⟨z, hz⟩
      let M : MarkedIdeal 3 Z := L z
      let U := ordMask (M := Z) M 2
      let P := CMfd.of (n := 3) U
      let Q : MarkedIdeal 3 P := compAt (X := Z) M 2 (BlowupTower.refl (X := Z))
      ∃ (hx : x ∈ U) (S : Opens U),
        let a : U := ⟨x, hx⟩
        Q.E = [] ∧ a ∈ Q.cosupp ∧ a ∈ S ∧
        ¬ IsSpecial Q (BlowupTower.refl (X := P)) a ∧
        IsTangentDirectionAlong Q.N Q.ideal Q.d S (fun u : U => coord 0 u.val.val.val) := by
  obtain ⟨hq, hz, hx, hQeq, hQ, _, ha, _, _, _⟩ := selected_born_order_two_companion
  obtain ⟨hq', hz', _, _, hN, _, _⟩ := selected_born_trace_gens
  have eq₁ : hq' = hq := Subsingleton.elim _ _
  subst hq'
  have eq₂ : hz' = hz := Subsingleton.elim _ _
  subst hz'
  obtain ⟨_, hJ, _, _, _⟩ := actual_positive_companion_level
  obtain ⟨S₀, hqS, hTang⟩ := ambient_coordinate_tangent
  let z : W := ⟨q, hq⟩
  let Z := CMfd.of (n := 3) (O z)
  let x : O z := ⟨z, hz⟩
  let M : MarkedIdeal 3 Z := L z
  let U := ordMask (M := Z) M 2
  let P := CMfd.of (n := 3) U
  let Q : MarkedIdeal 3 P := compAt (X := Z) M 2 (BlowupTower.refl (X := Z))
  let a : U := ⟨x, hx⟩
  let φ₁ : W → Y := Subtype.val
  let φ₂ : O z → W := Subtype.val
  let φ₃ : U → O z := Subtype.val
  let D₁ : Set W := φ₁ ⁻¹' F
  let D₂ : Set (O z) := φ₂ ⁻¹' D₁
  let D₃ : Set U := φ₃ ⁻¹' D₂
  let I₁ := GermIdeal.pullback (m := 3) φ₁ I
  let I₂ := GermIdeal.pullback (m := 3) φ₂ I₁
  let I₃ := GermIdeal.pullback (m := 3) φ₃ I₂
  let K₁ := GermIdeal.pullback (m := 3) φ₁ K
  let K₂ := GermIdeal.pullback (m := 3) φ₂ K₁
  let K₃ := GermIdeal.pullback (m := 3) φ₃ K₂
  have hi₁ : I₁.IsCoherent := isCoherent_pullback contMDiff_subtype_val coherent_I
  have hi₂ : I₂.IsCoherent := isCoherent_pullback contMDiff_subtype_val hi₁
  have hk₁ : K₁.IsCoherent := isCoherent_pullback contMDiff_subtype_val coherent_K
  have hk₂ : K₂.IsCoherent := isCoherent_pullback contMDiff_subtype_val hk₁
  have hD₁ : IsClosedSubmanifold 3 D₁ := isClosedSubmanifold_preimage_val F_smooth W
  have hD₂ : IsClosedSubmanifold 3 D₂ := isClosedSubmanifold_preimage_val hD₁ (O z)
  have hk₁' : K₁ = restrictOn 3 D₁ I₁ := restrict_open W F_smooth coherent_I
  have hk₂' : K₂ = restrictOn 3 D₂ I₂ := by
    change GermIdeal.pullback (m := 3) φ₂ K₁ = _
    rw [hk₁']
    exact restrict_open (O z) hD₁ hi₁
  have hk₃' : K₃ = restrictOn 3 D₃ I₃ := by
    change GermIdeal.pullback (m := 3) φ₃ K₂ = _
    rw [hk₂']
    exact restrict_open U hD₂ hi₂
  let M' : MarkedIdeal 3 P := MarkedIdeal.pullback φ₃ M
  have hQeq : Q = (⟨M'.N, [], restrictOn 3 M'.N M'.ideal, 2⟩ : MarkedIdeal 3 P) := hQeq
  have hQN : Q.N = D₃ := by
    have hqN := congrArg (fun C : MarkedIdeal 3 P => C.N) hQeq
    exact hqN.trans (congrArg ((Subtype.val : U → O z) ⁻¹' ·) hN)
  have hQI : Q.ideal = K₃ := by
    have hqI := congrArg (fun C : MarkedIdeal 3 P => C.ideal) hQeq
    have hM' : M'.ideal = I₃ := by
      have hL : (L z).ideal = I₂ := by
        exact (L_ideal z hJ.isWellFormed.isCoherent).trans
          (congrArg (fun a : GermIdeal 3 V => GermIdeal.pullback (m := 3) φ₂ a) J_ideal)
      exact congrArg (fun a : GermIdeal 3 Z => GermIdeal.pullback (m := 3) φ₃ a) hL
    have hM'N : M'.N = D₃ :=
      congrArg ((Subtype.val : U → O z) ⁻¹' ·) hN
    exact hqI.trans (by rw [hM'N, hM', hk₃'])
  have hQE : Q.E = [] := congrArg (fun C : MarkedIdeal 3 P => C.E) hQeq
  have hQd : Q.d = 2 := congrArg (fun C : MarkedIdeal 3 P => C.d) hQeq
  have h₁ := tangent_open W coherent_K hTang
  have h₂ := tangent_open (O z) hk₁ h₁
  have h₃ := tangent_open U hk₂ h₂
  let S : Opens U := ⟨_, h₃.isOpen⟩
  have haS : a ∈ S := hqS
  have ht : IsTangentDirectionAlong D₃ K₃ 2 S (fun u : U => coord 0 u.val.val.val) := h₃
  have hReg : RegularAtDim (n := 3) Q.N a 2 := by
    have hA := isInvDomain_geoTransformAlong domain B test
    have hS : IsSNCDivisor 3 [F] := (show Q₀.E = [F] from stage_boundary) ▸ hA.isWellFormed.isSNCDivisor
    have hqF := (born_iff chart_q.1).mpr (by change yChart.toFun q 1 = 0; rw [chart_q.2]; rfl)
    have hr := regularAtDim_member hS (0 : Fin 1) hqF
    rw [hQN]
    exact regularAtDim_preimage_val_iff.mpr (regularAtDim_preimage_val_iff.mpr
      (regularAtDim_preimage_val_iff.mpr hr))
  have hSq (i : Fin 3) (hi : i ≠ 1) :
      Q.ideal.mem a (fun u : U => coord i u.val.val.val ^ 2) := by
    have h₁ := comp_val_mem_pullback_val W coherent_K (x := z) (square_mem i hi)
    have h₂ := comp_val_mem_pullback_val (O z) hk₁ (x := x) h₁
    have h₃ := comp_val_mem_pullback_val U hk₂ (x := a) h₂
    have h := show K₃.mem a (fun u : U => coord i u.val.val.val ^ 2) from h₃
    exact hQI.symm ▸ h
  have hNear : ∀ᶠ u : U in 𝓝 a, u ∈ Q.cosupp ↔ u ∈ ({a} : Set U) := by
    have hc : Continuous (fun u : U => u.val.val.val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    filter_upwards [eventually_mem hQ.isWellFormed.isCoherent (hSq 0 (by decide)),
      eventually_mem hQ.isWellFormed.isCoherent (hSq 2 (by decide)),
      hc.continuousAt.eventually (yChart.isOpen_source.mem_nhds chart_q.1)] with u hu₀ hu₂ hChart
    constructor
    · intro hu
      have h0 := (vanishesToOrderOn_one_iff hu.1
        (GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hu₀)).mp
          ((hu.2 _ hu₀).mono (hQd.symm ▸ (by decide : 1 ≤ 2)))
      have h2 := (vanishesToOrderOn_one_iff hu.1
        (GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hu₂)).mp
          ((hu.2 _ hu₂).mono (hQd.symm ▸ (by decide : 1 ≤ 2)))
      have hm : u ∈ D₃ := hQN ▸ hu.1
      have h1 := (born_iff hChart).mp (show u.val.val.val ∈ F from hm)
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply yChart.toPartialEquiv.injOn hChart chart_q.1
      change yChart.toFun u.val.val.val = yChart.toFun q
      rw [chart_q.2]
      ext i
      fin_cases i
      · exact eq_zero_of_pow_eq_zero h0
      · exact h1
      · exact eq_zero_of_pow_eq_zero h2
    · intro hu
      rw [mem_singleton_iff.mp hu]
      exact ha
  have hCReg : RegularAtDim (n := 3) Q.cosupp a 0 :=
    regularAtDim_of_eventually_mem_iff (hNear.mono fun _ h => h.symm) (singleton_regular (M := P) a)
  let T := BlowupTower.refl (X := P)
  have hLev : level Q T a = 0 := by
    change boundaryCount (Q.E.take Q.E.length) a = _
    rw [hQE]
    rfl
  have hNS : ¬ IsSpecial Q T a := by
    rintro (⟨_, k, hN, hC⟩ | ⟨h, _⟩)
    · change RegularAtDim (n := 3) Q.N a (k + 1) at hN
      change RegularAtDim (n := 3) (barMarked Q).cosupp a k at hC
      rw [cosupp_barMarked Q hQ.isWellFormed hQ.one_le_d] at hC
      have h := eq_of_regularAtDim hN hReg
      have h' := eq_of_regularAtDim hC hCReg
      omega
    · rw [hLev] at h
      omega
  exact ⟨hq, hz, hx, S, hQE, ha, haS, hNS, hQN.symm ▸ hQI.symm ▸ hQd.symm ▸ ht⟩

open CanonicalCentres ContactLowerValue ContactStageKept ContactStageInvDomain
  StepOneCanonicalTail HironakaG1InitialPositiveGeneralRead

set_option maxHeartbeats 1300000 in
/-- The canonical Step One value at the actual order-two companion reads
the prescribed first-coordinate contact, on an open in its literal mask. -/
theorem actual_order_two_canonical_coordinate_read :
    ∃ (hq : q ∈ W) (hz : (⟨q, hq⟩ : W) ∈ O ⟨q, hq⟩),
      let z : W := ⟨q, hq⟩
      let Z := CMfd.of (n := 3) (O z)
      let x : O z := ⟨z, hz⟩
      let M : MarkedIdeal 3 Z := L z
      let U := ordMask (M := Z) M 2
      let P := CMfd.of (n := 3) U
      let Q : MarkedIdeal 3 P := compAt (X := Z) M 2 (BlowupTower.refl (X := Z))
      ∃ (hx : x ∈ U) (S : Opens U) (ha : (⟨x, hx⟩ : U) ∈ S),
        let a : U := ⟨x, hx⟩
        let u : U → ℂ := fun y => coord 0 y.val.val.val
        let T := BlowupTower.refl (X := P)
        let J' : MarkedIdeal 3 (CMfd.of (n := 3) S) := contactMarkedKept Q u T S
        let R₁ := invFamily (by decide : 0 < 3) 1
        let w := R₁.inv J' (BlowupTower.refl (X := CMfd.of (n := 3) S)) (⟨a, ha⟩ : S)
        IsInvDomain 1 J' ∧
        Seq.StepOneValueMasked.stepOneInvM R₁ Q T a = toLex (0, (w : WithTop (ValTy 1))) ∧
        (invFamily (by decide : 0 < 3) 3).inv record B q =
          positiveSuccessorRead 1 (toLex (1, (positiveSuccessorRead 2
            (toLex (0, (w : WithTop (ValTy 1)))) : WithTop (ValTy 2)))) := by
  obtain ⟨hq, hz, hx, V₀, hQE, ha, haV, hNS, hTan⟩ := actual_order_two_coordinate_tangent
  obtain ⟨hq', hz', hx', _, hQ, hMax, _, hZero, _, hRead⟩ := selected_born_order_two_companion
  have eq₁ : hq' = hq := Subsingleton.elim _ _
  subst hq'
  have eq₂ : hz' = hz := Subsingleton.elim _ _
  subst hz'
  have eq₃ : hx' = hx := Subsingleton.elim _ _
  subst hx'
  let z : W := ⟨q, hq⟩
  let Z := CMfd.of (n := 3) (O z)
  let x : O z := ⟨z, hz⟩
  let M : MarkedIdeal 3 Z := L z
  let U := ordMask (M := Z) M 2
  let P := CMfd.of (n := 3) U
  let Q : MarkedIdeal 3 P := compAt (X := Z) M 2 (BlowupTower.refl (X := Z))
  let a : U := ⟨x, hx⟩
  let u : U → ℂ := fun y => coord 0 y.val.val.val
  let T := BlowupTower.refl (X := P)
  let R₁ := invFamily (by decide : 0 < 3) 1
  let Bad : Set U := codimOnePartAlong (barMarked Q).N (barMarked Q).ideal (barMarked Q).d
  have hb := isWellFormed_barMarked Q hQ.isWellFormed
  have hd := ContactIndependenceAlong.one_le_coeffMarkedAlong_d (homMarkedAlong Q)
  have hClosed : IsClosed Bad := isClosed_codimOnePartAlong hb.isCoherent hb.isClosedSubmanifold_N hd
    (isMaximalOrderAlong_barMarked Q hQ.isWellFormed hQ.one_le_d hMax)
  have haBad : a ∉ Bad := fun h => hNS (Or.inl ⟨hZero, h⟩)
  let S : Opens U := ⟨(V₀ : Set U) ∩ Badᶜ, V₀.isOpen.inter hClosed.isOpen_compl⟩
  have haS : a ∈ S := ⟨haV, haBad⟩
  have hEmpty : origMembers Q T = [] := by
    change Q.E.take Q.E.length = []
    rw [hQE]
    rfl
  let J' : MarkedIdeal 3 (CMfd.of (n := 3) S) := contactMarkedKept Q u T S
  have hDom : IsInvDomain 1 J' := by
    refine isInvDomain_stage_coeffHomAlong_of_le Q hQ.isWellFormed hQ.one_le_d hQ.dimLE
      V₀ hTan T trivial S (fun y hy => hy.1) (fun y hy _ => hy.2) ?_
    intro D hD
    change D ∈ origMembers Q T at hD
    rw [hEmpty] at hD
    exact (List.not_mem_nil hD).elim
  have hCos : a ∈ (barMarked Q).cosupp :=
    (cosupp_barMarked Q hQ.isWellFormed hQ.one_le_d).symm ▸ ha
  have hData : Seq.StepOneValueMasked.LowerDataL R₁ Q (lowerMarkedM Q) 0 T T a :=
    Seq.StepOneCanonicalTail.lowerDataL_refl (k := 2) Q R₁ hQ.isWellFormed hQ.one_le_d (by decide : 0 < 3) hMax
      hQ.dimLE T trivial hCos ⟨hZero, hNS⟩
  have hValue := Seq.ContactLowerValue.lowerValueL_zero_eq R₁ Q hQ.isWellFormed hQ.one_le_d T T trivial hTan S
    (fun y hy => hy.1) (fun D hD => False.elim (by rw [hEmpty] at hD; exact List.not_mem_nil hD))
    hDom trivial haS hCos hData
  let w := R₁.inv J' (BlowupTower.refl (X := CMfd.of (n := 3) S)) (⟨a, haS⟩ : S)
  have hStep : Seq.StepOneValueMasked.stepOneInvM R₁ Q T a = toLex (0, (w : WithTop (ValTy 1))) := by
    change Seq.StepOneValueMasked.stepOneInvL R₁ Q (lowerMarkedM Q) T a = _
    rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R₁ Q (lowerMarkedM Q) T hNS, hZero]
    change toLex (0, Seq.StepOneValueMasked.lowerValueL R₁ Q (lowerMarkedM Q) 0 T T a) = _
    rw [hValue]
    rfl
  refine ⟨hq, hz, hx, S, haS, hDom, hStep, ?_⟩
  exact hRead.trans (congrArg (fun t : ℕ ×ₗ WithTop (ValTy 1) =>
    positiveSuccessorRead 1 (toLex (1, (positiveSuccessorRead 2 t : WithTop (ValTy 2))))) hStep)

end
end Hironaka.HironakaG1RecursiveBornOrderTwoTangentExample
