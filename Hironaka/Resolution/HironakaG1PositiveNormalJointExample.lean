import Hironaka.Resolution.HironakaG1PositiveNormalNonspecialExample
import Hironaka.Resolution.HironakaG8LogClosureHistory
import Hironaka.Resolution.HironakaActualNativeSectionStepOneHistory

/-! The coordinate generators on the actual open product and its zero section. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalJointExample
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  GermIdealPullbackCalculus RelativePrincipalizationSpan InvertibleIdealQuotient IdealOrderArithmetic
  RestrictedIdealExtension HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaActualCoherentWeightedCoefficientMarked HironakaG8LogClosureHistory
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualWeightedNormalPadding
  HironakaActualCentreJointJets HironakaRelativeNormalIdeal
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaG1PositiveNormalNonspecialExample

private theorem pullback_generators {n m : ℕ} {X : CMfd.{0} n} {Y : CMfd.{0} m} {ι : Type}
    (g : ι → X → ℂ)
    (hg : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i))
    (f : Y → X) (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    GermIdeal.pullback (m := m) f (finiteFunctionIdeal (n := n) g) =
      finiteFunctionIdeal (n := m) (fun i => g i ∘ f) := by
  refine GermIdeal.ext (funext fun x => funext fun a => propext ⟨?_, ?_⟩)
  · intro ha
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp ha)
    rintro _ ⟨b, hb, rfl⟩
    refine (isInSpanAt_comp' hf hb).mono ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · intro ha
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ ha)
    rintro _ ⟨i, rfl⟩
    exact ⟨g i, isInSpanAt_self ⟨i, rfl⟩ (Eventually.of_forall fun z => hg i z), rfl⟩

private theorem sum_generators {n : ℕ} {X : CMfd.{0} n} {ι κ : Type}
    (f : ι → X → ℂ) (g : κ → X → ℂ)
    (hf : ∀ i x, HolomorphicAt n (f i) x) (hg : ∀ i x, HolomorphicAt n (g i) x) :
    sumIdeal (finiteFunctionIdeal (n := n) f) (finiteFunctionIdeal (n := n) g) =
      finiteFunctionIdeal (n := n) (Sum.elim f g) := by
  refine GermIdeal.ext (funext fun x => funext fun a => propext ⟨?_, ?_⟩)
  · intro ha
    refine IsInSpanAt.trans ?_ (mem_sumIdeal_iff.mp ha)
    rintro b (hb | hb)
    · exact hb.mono (by rintro _ ⟨i, rfl⟩; exact ⟨.inl i, rfl⟩)
    · exact hb.mono (by rintro _ ⟨i, rfl⟩; exact ⟨.inr i, rfl⟩)
  · intro ha
    refine mem_sumIdeal_iff.mpr (ha.mono ?_)
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i => exact Or.inl (isInSpanAt_self ⟨i, rfl⟩ (hf i x))
    | inr i => exact Or.inr (isInSpanAt_self ⟨i, rfl⟩ (hg i x))

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev D : Set U := (Subtype.val : U → ComplexModel 2) ⁻¹' firstCoordinateDivisor

/-- The input record in the top open of the actual two-dimensional model. -/
def sourceRecord : MarkedIdeal 2 U :=
  ⟨univ, [D], GermIdeal.pullback (m := 2) (Subtype.val : U → ComplexModel 2) coordinatePairIdeal, 1⟩

private theorem pair_hol (i : Bool) :
    MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ) (coordinatePairGenerator i) := by
  cases i
  · exact (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).mdifferentiable.pow 2
  · exact (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).mdifferentiable

private abbrev projectedModel (z : ComplexModel 3) := tangentProjection 2 1 z

private theorem projection_comp_val :
    (Subtype.val : U → ComplexModel 2) ∘ projection U =
      projectedModel ∘ (Subtype.val : productOpen U → ComplexModel 3) := rfl

/-- The genuine section ideal retains exactly the two pulled-back
coordinate generators, on the whole ambient open. -/
theorem section_source_generators :
    (sectionMarked sourceRecord).ideal = GermIdeal.pullback (m := 3)
      (Subtype.val : productOpen U → ComplexModel 3)
      (finiteFunctionIdeal (n := 3) (fun i => coordinatePairGenerator i ∘ projectedModel)) := by
  change GermIdeal.pullback (m := 3) (projection U)
    (GermIdeal.pullback (m := 2) Subtype.val coordinatePairIdeal) = _
  rw [← coherent_pullback_comp contMDiff_subtype_val (projection_contMDiff U)
    coordinatePairIdeal coordinatePairIdeal_coherent, projection_comp_val]
  rw [coherent_pullback_comp (tangentProjection 2 1).contMDiff contMDiff_subtype_val
    coordinatePairIdeal coordinatePairIdeal_coherent]
  congr 1
  exact pullback_generators (X := CMfd.of (n := 2) (ComplexModel 2))
    (Y := CMfd.of (n := 3) (ComplexModel 3)) coordinatePairGenerator pair_hol
    projectedModel (tangentProjection 2 1).contMDiff

/-- The padded ideal is exactly the coordinate triple ideal on the whole
actual product open. -/
theorem proper_source_generators :
    (properNormalMarked sourceRecord).ideal = GermIdeal.pullback (m := 3)
      (Subtype.val : productOpen U → ComplexModel 3) paddedCoordinateIdeal := by
  let i : productOpen U → ComplexModel 3 := Subtype.val
  let g : Bool → ComplexModel 3 → ℂ := fun j => coordinatePairGenerator j ∘ projectedModel
  have hgh (j : Bool) : MDifferentiable 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) (g j) :=
    (pair_hol j).comp (tangentProjection 2 1).mdifferentiable
  have hi : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) ∞ i := contMDiff_subtype_val
  have hiM : MDifferentiable 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) i :=
    hi.mdifferentiable (by simp)
  change sumIdeal (sectionMarked sourceRecord).ideal
    (finiteFunctionIdeal (fun _ : Unit => fun z => relativeNormalCoordinate U z ^ 1)) = _
  rw [section_source_generators, pullback_generators
    (X := CMfd.of (n := 3) (ComplexModel 3)) (Y := X) g hgh i contMDiff_subtype_val]
  rw [sum_generators (X := X) (fun j => g j ∘ i)
      (fun _ : Unit => fun z => relativeNormalCoordinate U z ^ 1)
      (fun j _ => Eventually.of_forall fun z => ((hgh j).comp hiM) z)
      (fun _ _ => Eventually.of_forall fun z => ((normalCoordinate_mdifferentiable U).pow 1) z)]
  rw [show paddedCoordinateIdeal = finiteFunctionIdeal paddedGenerator from rfl,
    pullback_generators (X := CMfd.of (n := 3) (ComplexModel 3)) (Y := X)
      paddedGenerator paddedGenerator_hol i contMDiff_subtype_val]
  congr 1
  funext j z
  rcases j with (_ | _) | _
  · rfl
  · rfl
  · change relativeNormalCoordinate U z ^ 1 = z.val 2
    simp [relativeNormalCoordinate, HironakaActualZeroCoordinateContactSeed.addedCoordinate,
      HironakaActualGraphFunctionalIdeal.graphFunction, HironakaActualZeroCoordinateContactSeed.zeroFunction]

open GermIdealOrder HadamardBridge HironakaSharpOriginalProductTraceOrder NonmonomialOrderLocal
  MarkedIdealRestrictOpen HironakaActualNativeSectionInitialBar

private theorem orders_comp {n m : ℕ} {A : CMfd.{0} n} {B : CMfd.{0} m}
    {f : B → A} (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {V : Set A} {W : Set B} (hW : W ⊆ f ⁻¹' V) {p : B} {r : ℕ} {g : A → ℂ}
    (h : VanishesToOrderOn n V (f p) r g) : VanishesToOrderOn m W p r (g ∘ f) := by
  obtain ⟨a, ha, hEq⟩ := h
  refine ⟨a ∘ f, comp_mem_idealPow_pointIdeal
    (Eventually.of_forall fun _ => (hf.mdifferentiable (by simp)).mdifferentiableAt) r ha, ?_⟩
  exact (hf.continuous.continuousAt.eventually hEq).mono fun _ hx hz => hx (hW hz)

private theorem traceOrder_split {n m : ℕ} {A : CMfd.{0} n} {B : CMfd.{0} m}
    {f : B → A} {j : A → B} (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hj : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ j)
    (hfj : f ∘ j = id) {V : Set A} {W : Set B} (hW : W ⊆ f ⁻¹' V) (hV : V ⊆ j ⁻¹' W)
    (I : GermIdeal n A) (hI : I.IsCoherent) (q : A) :
    ordinaryTraceOrder (X := B) W (GermIdeal.pullback (m := m) f I) (j q) =
      ordinaryTraceOrder (X := A) V I q := by
  unfold ordinaryTraceOrder nmOrd
  congr 1
  ext r
  apply not_congr
  rw [ordGe_ordinaryTraceMarked_eq_cosupport W _ (isCoherent_pullback hf hI),
    ordGe_ordinaryTraceMarked_eq_cosupport V I hI]
  have hq : f (j q) = q := congrFun hfj q
  constructor
  · rintro ⟨hqW, hr⟩
    refine ⟨hq ▸ hW hqW, fun g hg => ?_⟩
    have hg' : I.mem (f (j q)) g := hq.symm ▸ hg
    have hgc : (GermIdeal.pullback (m := m) f I).mem (j q) (g ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g, hg', rfl⟩
        ((GermIdeal.IsCoherent.holomorphicAt_mem hI hg').comp_contMDiff
          (Eventually.of_forall fun x => hf x)))
    simpa only [Function.comp_assoc, hfj, Function.comp_id] using orders_comp hj hV (hr (g ∘ f) hgc)
  · rintro ⟨hqV, hr⟩
    refine ⟨hV hqV, fun g hg => IsInSpanAt.vanishesToOrderOn (GermIdeal.mem_pullback_iff.mp hg) ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact orders_comp hf hW (hq.symm ▸ hr a (hq ▸ ha))

private abbrev originBase : U := ⟨0, mem_univ _⟩
private abbrev origin : productOpen U := zeroSection U originBase
private abbrev verticalMember : Set X := projection U ⁻¹' D

private theorem origin_value : origin.val = 0 := by
  change tangentInclusion 2 1 0 = 0
  exact map_zero _

private theorem verticalMember_eq :
    verticalMember = (Subtype.val : productOpen U → ComplexModel 3) ⁻¹' paddedFirstCoordinateDivisor := by
  ext z
  rfl

/-- Ordinary trace order is preserved by restricting a coherent ideal and its carrier to an open. -/
theorem ordinaryTraceOrder_pullback_open {n : ℕ} {A : CMfd.{0} n} (O : Opens A)
    (V : Set A) (I : GermIdeal n A) (hI : I.IsCoherent) (q : O) :
    ordinaryTraceOrder (X := CMfd.of (n := n) O) ((Subtype.val : O → A) ⁻¹' V)
        (GermIdeal.pullback (m := n) (Subtype.val : O → A) I) q =
      ordinaryTraceOrder (X := A) V I q.val := by
  apply nmOrd_congr
  intro r
  rw [ordGe_ordinaryTraceMarked_eq_cosupport _ _ (isCoherent_pullback contMDiff_subtype_val hI),
    ordGe_ordinaryTraceMarked_eq_cosupport _ _ hI]
  let K : MarkedIdeal n A := ⟨V, [], I, r⟩
  have hHol : ∀ x g, K.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  change q ∈ (MarkedIdeal.pullback (Subtype.val : O → A) K).cosupp ↔ q.val ∈ K.cosupp
  rw [cosupp_pullback_val K hHol O]
  rfl

/-- The exact order of the genuine padded ideal on the actual selected member. -/
theorem proper_source_trace_order :
    ordinaryTraceOrder (X := X) verticalMember (properNormalMarked sourceRecord).ideal origin = 1 := by
  have hC : paddedCoordinateIdeal.IsCoherent :=
    isCoherent_finiteFunctionIdeal paddedGenerator paddedGenerator_hol
  rw [proper_source_generators, verticalMember_eq,
    ordinaryTraceOrder_pullback_open (A := CMfd.of (n := 3) (ComplexModel 3)) _ _ _ hC, origin_value]
  exact padded_coordinate_triple_selected_trace_order

/-- The exact order of the genuine section ideal on the actual section
intersection with the selected member. -/
theorem section_source_trace_order :
    ordinaryTraceOrder (X := X) (zeroPlane U ∩ verticalMember) (sectionMarked sourceRecord).ideal origin = 2 := by
  let A := CMfd.of (n := 2) (ComplexModel 2)
  let f : X → A := (Subtype.val : U → ComplexModel 2) ∘ projection U
  let j : A → X := fun z => zeroSection U ⟨z, mem_univ _⟩
  have hfj : f ∘ j = id := by
    funext z
    exact tangentProjection_tangentInclusion 2 1 z
  have hf : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 2) ∞ f :=
    contMDiff_subtype_val.comp (projection_contMDiff U)
  have hj : ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 3) ∞ j := by
    apply (ContMDiff.subtypeVal_comp_iff (productOpen U) _).mp
    exact (tangentInclusion 2 1).contMDiff
  have hW : zeroPlane U ∩ verticalMember ⊆ f ⁻¹' firstCoordinateDivisor := fun _ hz => hz.2
  have hV : firstCoordinateDivisor ⊆ j ⁻¹' (zeroPlane U ∩ verticalMember) := by
    intro z hz
    refine ⟨⟨mem_univ _, actualJointNormalProjection_tangent 2 1 z⟩, ?_⟩
    change f (j z) ∈ firstCoordinateDivisor
    have hzEq : f (j z) = z := congrFun hfj z
    exact hzEq.symm ▸ hz
  have hI : (sectionMarked sourceRecord).ideal = GermIdeal.pullback (m := 3) f coordinatePairIdeal :=
    (coherent_pullback_comp contMDiff_subtype_val (projection_contMDiff U)
      coordinatePairIdeal coordinatePairIdeal_coherent).symm
  rw [hI]
  exact (traceOrder_split hf hj hfj hW hV coordinatePairIdeal coordinatePairIdeal_coherent 0).trans
    actual_coordinate_pair_selected_trace_order

open NormalCrossings ResolutionInvariantSpec HironakaPrincipalizationBoundary
  InvDomainTowerAlong HironakaAdmissibleSequence

private theorem snc_model_first : IsSNCDivisor 2 [firstCoordinateDivisor] := by
  classical
  refine ⟨fun H hH => ?_, fun z => ?_⟩
  · rw [List.mem_singleton] at hH
    rw [hH]
    exact isClosed_eq (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).continuous continuous_const
  · refine ⟨fun _ => {0}, ?_, fun _ _ => Finset.card_singleton _, ?_⟩
    · let Φ : LocalHolomorphicEquivAt (n := 2) (chartAt (ComplexModel 2) z z) :=
        { source := univ
          target := univ
          isOpen_source := isOpen_univ
          isOpen_target := isOpen_univ
          center_mem_source := mem_univ _
          toFun := fun w => w - z
          invFun := fun w => w + z
          toFun_holomorphic := (differentiable_id.sub_const z).differentiableOn
          invFun_holomorphic := (differentiable_id.add_const z).differentiableOn
          mapsTo_toFun := mapsTo_univ _ _
          mapsTo_invFun := mapsTo_univ _ _
          left_inv := fun w _ => sub_add_cancel w z
          right_inv := fun w _ => add_sub_cancel_right w z }
      refine ⟨Φ, ?_, sub_self _, ?_⟩
      · intro w hw
        change w ∈ Set.univ
        exact mem_univ _
      · intro i hi w hw hwΦ
        have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
        have hGet : [firstCoordinateDivisor].get i = firstCoordinateDivisor := by
          rw [Fin.eq_zero i]
          rfl
        change z ∈ [firstCoordinateDivisor].get i at hi
        rw [hGet] at hi
        change w ∈ [firstCoordinateDivisor].get i ↔ w - z ∈ coordSubspace ({0} : Finset (Fin 2))
        rw [hGet]
        have hiz : z (0 : Fin 2) = 0 := hi
        simp [firstCoordinateDivisor, coordSubspace, hiz]
    · intro i _ j _ _
      exact (Fin.eq_zero i).trans (Fin.eq_zero j).symm

private theorem pair_nonzero (z : ComplexModel 2) :
    DivisorExponentAlong.IsNonzeroAlongAt univ coordinatePairIdeal z := by
  apply isNonzeroAlongAt_univ_iff_exists.mpr
  let f : ComplexModel 2 → ℂ := EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)
  have hf : HolomorphicAt 2 f z := Eventually.of_forall fun _ =>
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).mdifferentiableAt
  refine ⟨f, isInSpanAt_self ⟨true, rfl⟩ hf, ?_⟩
  by_contra! h
  have hzero : f =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := h
  have hd := hzero.fderiv_eq (𝕜 := ℂ)
  change fderiv ℂ (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)) z =
    fderiv ℂ (fun _ : ComplexModel 2 => (0 : ℂ)) z at hd
  rw [ContinuousLinearMap.fderiv, fderiv_const_apply] at hd
  have hbad := congrArg (fun L : ComplexModel 2 →L[ℂ] ℂ => L (PiLp.single 2 (0 : Fin 2) 1)) hd
  simp at hbad

/-- The explicit source lies in the invariant domain in dimension two. -/
theorem sourceRecord_domain : IsInvDomain 2 sourceRecord := by
  let A := CMfd.of (n := 2) (ComplexModel 2)
  let M : MarkedIdeal 2 A := ⟨univ, [firstCoordinateDivisor], coordinatePairIdeal, 1⟩
  have h : IsInvDomain 2 M := isInvDomain_univ_of_isSNCDivisor
    coordinatePairIdeal_coherent pair_nonzero snc_model_first
  exact InvDomainTowerAlong.isInvDomain_pullback_val U h

open StepOneValue StepOneValueMasked BoundaryCount StepOneLowerDomain BlowupTowerTransforms
  HironakaActualSectionBoundaryGeometry HironakaActualNativeInvariantDomain
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionStepOneHistory
  HironakaG1ProperCarrierNormalContact HironakaG8MixedOrderInvariance CanonicalCentres

private theorem one_member_level {n : ℕ} {Y : CMfd.{0} n}
    (M : MarkedIdeal n Y) (D' : Set Y) (he : M.E = [D']) (p : Y) (hp : p ∈ D') :
    level M (BlowupTower.refl (X := Y)) p = 1 := by
  have he' : origMembers M (BlowupTower.refl (X := Y)) = M.E := by
    change (barMarked (X := Y) M).E.take M.E.length = M.E
    change M.E.take M.E.length = M.E
    simp
  simp [level, he', he, hp, boundaryCount]

private theorem cosupp_of_positive_selected_order {n : ℕ} {Y : CMfd.{0} n}
    (M : MarkedIdeal n Y) (hI : M.ideal.IsCoherent) (hd : M.d = 1)
    (V : Set Y) (hV : V ⊆ M.N) (p : Y)
    (hr : 1 ≤ ordinaryTraceOrder (X := Y) V M.ideal p) : p ∈ M.cosupp := by
  have h := mem_ordGe_of_succ_le (𝔪 := ordinaryTraceMarked (X := Y) V M.ideal) (q := 0) hr
  rw [ordGe_ordinaryTraceMarked_eq_cosupport V M.ideal hI] at h
  refine ⟨hV h.1, hd.symm ▸ fun g hg => ?_⟩
  have hHol := GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  exact (vanishesToOrderOn_one_iff (hV h.1) hHol).mpr
    ((vanishesToOrderOn_one_iff h.1 hHol).mp (h.2 g hg))

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency false in
/-- At the origin of the common empty history, the actual padded and
native section records are both nonspecial at level one. Their masked
lower invariant first entries are respectively one and two. -/
theorem joint_positive_nonspecial_first_entries :
    let P : MarkedIdeal 3 X := properNormalMarked sourceRecord
    let S : MarkedIdeal 3 X := sectionMarked sourceRecord
    let T : BlowupTower X X := .refl
    let Z := nativeManifold (Y := X) (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U)
    let B : MarkedIdeal 2 Z := nativePullback (Y := X) (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U) S
    let N : BlowupTower Z Z := .refl
    let p : X := origin
    ∃ (z : Z) (hZero : IsClosed (zeroPlane U))
      (pO : lowerMask P 1 T p) (zO : lowerMask B 1 N z),
      Lift (Nat.le_succ 2) (zeroPlane U) hZero (zeroPlane_regular U) S.E T
        (zeroPlane U) hZero (zeroPlane_regular U) N ∧
      z.val = p ∧ pO.val = p ∧ zO.val = z ∧
      p ∈ P.cosupp ∧ p ∈ S.cosupp ∧
      level P T p = 1 ∧ level B N z = 1 ∧
      ¬ IsSpecial P T p ∧ ¬ IsSpecial S T p ∧ ¬ IsSpecial B N z ∧
      fstEntry ((canonicalInvariant 3).inv (lowerMarkedM P 1 T p)
        (BlowupTower.refl (X := CMfd.of (n := 3) (lowerMask P 1 T p))) pO) = 1 ∧
      fstEntry ((canonicalInvariant 2).inv (lowerMarkedM B 1 N z)
        (BlowupTower.refl (X := CMfd.of (n := 2) (lowerMask B 1 N z))) zO) = 2 := by
  intro P S T Z B N p
  have hN : (zeroPlane U : Set X) = S.N := rfl
  have hPN : P.N = univ := preimage_univ
  have hP := properNormalMarked_isInvDomain sourceRecord sourceRecord_domain
  have hS := section_projected_domain 2 sourceRecord.N sourceRecord.E sourceRecord.ideal sourceRecord.d sourceRecord_domain
  have hV : IsClosedSubmanifold 3 (zeroPlane U) :=
    liftedCarrier_closed_submanifold (HomogenizedGlueingTower.isClosedSubmanifold_univ (n := 2) (M := U))
  have hTr : IsTransverse 3 (zeroPlane U) S.E :=
    isTransverse_liftedCarrier sourceRecord.N sourceRecord.E sourceRecord_domain.isWellFormed.isTransverse
  have hB := isInvDomain_nativePullback (X := X) (by decide : 0 < 3) (Nat.le_succ 2)
    (zeroPlane_regular U) S hS (hN.symm ▸ subset_rfl) hTr
  have hpV : p ∈ zeroPlane U := ⟨mem_univ _, actualJointNormalProjection_tangent 2 1 originBase.val⟩
  let z : Z := ⟨p, hpV⟩
  have hpD : p ∈ verticalMember := by
    change tangentProjection 2 1 (tangentInclusion 2 1 0) ∈ firstCoordinateDivisor
    rw [tangentProjection_tangentInclusion]
    simp [firstCoordinateDivisor]
  have hLift : Lift (Nat.le_succ 2) (zeroPlane U) hV.1 (zeroPlane_regular U) S.E T
    (zeroPlane U) hV.1 (zeroPlane_regular U) N := Lift.refl
  have hPD : P.E = [verticalMember] := rfl
  have hSD : S.E = [verticalMember] := rfl
  have hPL := one_member_level P verticalMember hPD p hpD
  have hSL := one_member_level S verticalMember hSD p hpD
  have hPO : ordinaryTraceOrder (X := X) (P.N ∩ verticalMember) P.ideal p = 1 := by
    rw [hPN, univ_inter]
    exact proper_source_trace_order
  have hSO : ordinaryTraceOrder (X := X) (S.N ∩ verticalMember) S.ideal p = 2 :=
    hN ▸ section_source_trace_order
  have hNSP := not_isSpecial_of_mark_one_single_member_trace_order P rfl
    hP.isWellFormed.isCoherent verticalMember hPD p hpD (by rw [hPO]; decide)
  have hNSS := not_isSpecial_of_mark_one_single_member_trace_order S rfl
    hS.isWellFormed.isCoherent verticalMember hSD p hpD (by rw [hSO]; decide)
  have hChron := actual_section_step_one_chronology U sourceRecord.N
    sourceRecord_domain.isWellFormed.isClosedSubmanifold_N sourceRecord.E
    sourceRecord_domain.isWellFormed.isSNCDivisor S.ideal hS.isWellFormed.isCoherent sourceRecord.d hLift
  have hBL : level B N z = 1 := (hChron.2.2.1 z).1.symm.trans hSL
  have hNSB : ¬ IsSpecial B N z := fun h => hNSS ((hChron.2.2.1 z).2.mpr h)
  have hpO : p ∈ lowerMask P 1 T p :=
    mem_maskA P hP.isWellFormed hP.one_le_d (by decide) T trivial hPL.ge hNSP
  have hzO : z ∈ lowerMask B 1 N z :=
    mem_maskA B hB.isWellFormed hB.one_le_d (by decide) N trivial hBL.ge hNSB
  refine ⟨z, hV.1, ⟨p, hpO⟩, ⟨z, hzO⟩, hLift, rfl, rfl, rfl, ?_, ?_, hPL, hBL, hNSP, hNSS, hNSB, ?_, ?_⟩
  · exact cosupp_of_positive_selected_order P hP.isWellFormed.isCoherent rfl _
      inter_subset_left p (by rw [hPO])
  · exact cosupp_of_positive_selected_order S hS.isWellFormed.isCoherent rfl _
      inter_subset_left p (hSO.symm ▸ (by decide : 1 ≤ 2))
  · exact (positive_mark_one_single_member_fst P rfl hP.isWellFormed.isCoherent
      verticalMember hPD p hpD ⟨p, hpO⟩).trans hPO
  · exact (positive_normal_mark_one_native_fst sourceRecord sourceRecord_domain rfl rfl D rfl z
      hpD ⟨z, hzO⟩).trans section_source_trace_order

end
end Hironaka.HironakaG1PositiveNormalJointExample
