import Hironaka.Analytic.Unibranch.OriginalNativeHSNextCommonBase

/-! Actual equal-profile update of an honest PAST overlap.
Blueprint FIRST: original-native-hs-equal-outer-successor.tex.
SAME computed next states, prescribed ORIGINAL base, and real physical histories.
No next comparison, future range, phase or termination packet is supplied. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSEqualOuterSuccessor
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSOuterHistory OriginalNativeHSShadowOuterState
  OriginalNativeHSCurrentOverlap OriginalRelativelyCompactRestriction
  Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus
  Hironaka.HironakaEmbeddedNativeMorphism

private theorem saturate {A B D P : Type} [TopologicalSpace P]
    (a : A → B) (p : B → P) (q : D → B) (pn : D → P) (pc : A → P)
    (W V : Set P) (O : Set A) (hq : ∀ y, pn y = p (q y))
    (ha : range a = p ⁻¹' W) (hc : ∀ z, pc z = p (a z))
    (hVW : V ⊆ W) (hF : pc ⁻¹' closure V ⊆ O) : pn ⁻¹' V ⊆ q ⁻¹' (a '' O) := by
  intro y hy
  have hyW : p (q y) ∈ W := hVW (hq y ▸ hy)
  obtain ⟨z,hz⟩ := (show q y ∈ range a from ha.symm ▸ hyW)
  refine ⟨z,hF ?_,hz⟩
  change pc z ∈ closure V
  rw [hc z,hz,← hq y]
  exact subset_closure hy

private theorem factor_range {A B D : SourceReducedComplexSpace}
    (k : A ⟶ B) (e : B ⟶ D) (b : A ⟶ D)
    (he : LocallyRingedSpace.IsOpenImmersion e.hom.left) (hs : k ≫ e = b) :
    range k.hom.left.base = e.hom.left.base ⁻¹' range b.hom.left.base := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x,(congrArg (fun f : A ⟶ D => f.hom.left.base x) hs).symm⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,he.base_open.injective ((congrArg (fun f : A ⟶ D => f.hom.left.base x) hs).trans hx)⟩

private def nativeIsoOfRange {A B D : SourceReducedComplexSpace} (f : A ⟶ D) (g : B ⟶ D)
    (hf : LocallyRingedSpace.IsOpenImmersion f.hom.left)
    (hg : LocallyRingedSpace.IsOpenImmersion g.hom.left)
    (hr : range f.hom.left.base = range g.hom.left.base) : A ≅ B := by
  let := hf
  let := hg
  let e := openImmersionIsoOfRangeEq f.hom.left g.hom.left hr
  have hs : e.hom ≫ g.hom.left = f.hom.left := openImmersionIsoOfRangeEq_hom_fac _ _ hr
  have hp : e.hom ≫ B.obj.hom = A.obj.hom := by
    rw [← Over.w g.hom,← Category.assoc,hs]
    exact Over.w f.hom
  exact ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk e hp)

private theorem nativeIsoOfRange_square {A B D : SourceReducedComplexSpace} (f : A ⟶ D) (g : B ⟶ D)
    (hf : LocallyRingedSpace.IsOpenImmersion f.hom.left)
    (hg : LocallyRingedSpace.IsOpenImmersion g.hom.left)
    (hr : range f.hom.left.base = range g.hom.left.base) :
    (nativeIsoOfRange f g hf hg hr).hom ≫ g = f := by
  let := hf
  let := hg
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact openImmersionIsoOfRangeEq_hom_fac _ _ hr

variable {X : SourceReducedComplexSpace} {K₁ K₂ L : Set X.obj.left}
  {S : State X K₁} {T : State X K₂} (c : Context S T L)
  (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (hL : IsCompact L)
  (hL₁ : L ⊆ K₁) (hL₂ : L ⊆ K₂)
  (hneS : (singularShadow S).Nonempty) (hneT : (singularShadow T).Nonempty)

include hneS in
private theorem singularLeft : (shadow S ∩ intrinsicSingularLocus S.source.obj).Nonempty := by
  simpa only [singularShadow,inter_comm] using hneS
include hneT in
private theorem singularRight : (shadow T ∩ intrinsicSingularLocus T.source.obj).Nonempty := by
  simpa only [singularShadow,inter_comm] using hneT

private abbrev SN := OriginalNativeHSShadowOuterRun.next S hK₁ hneS
private abbrev TN := OriginalNativeHSShadowOuterRun.next T hK₂ hneT
private abbrev Z := endpoint S c.openSet c.compactClosure c.leftRange
private abbrev r : Z c ⟶ restriction X c.openSet c.compactClosure := (Context.commonHistory c).projection
private abbrev iW : restriction X c.openSet c.compactClosure ⟶ X := Context.baseInclusion c
local notation "aS" => Context.leftMap c
local notation "aT" => Context.rightMap c
local notation "haS" => Context.leftMap_isOpenImmersion c
local notation "haT" => Context.rightMap_isOpenImmersion c
local notation "C" => Context.commonCompact c
local notation "hC" => Context.commonCompact_isCompact c hL
local notation "hIS" => Context.left_image_in_shadow c hL₁
local notation "hIT" => Context.right_image_in_shadow c hL₂
local notation "Ω" => OriginalNativeHSOuterPhaseCoupling.overlapOpen S.history T.history
  (baseShadow S) (baseShadow T) (baseShadow_compact S hK₁) (baseShadow_compact T hK₂) hneS hneT (aS) (aT)
local notation "hΩ" => OriginalNativeHSOuterPhaseCoupling.compact_subset_overlap S.history T.history
  (baseShadow S) (baseShadow T) (baseShadow_compact S hK₁) (baseShadow_compact T hK₂) hneS hneT (aS) (aT) (C) (hIS) (hIT)
local notation "N" => OriginalNativeHSNextCommonBase.phaseNeighbourhood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT
local notation "V" => OriginalNativeHSNextCommonBase.openSet c hK₁ hK₂ hL hL₁ hL₂ hneS hneT
local notation "hV" => OriginalNativeHSNextCommonBase.compactClosure c hK₁ hK₂ hL hL₁ hL₂ hneS hneT
local notation "vS" => OriginalNativeHSNextCommonBase.closure_leftRange c hK₁ hK₂ hL hL₁ hL₂ hneS hneT
local notation "vT" => OriginalNativeHSNextCommonBase.closure_rightRange c hK₁ hK₂ hL hL₁ hL₂ hneS hneT

private abbrev phaseLeft : SourceReducedComplexSpace :=
  OriginalNativeHSEqualProfilePhaseComparison.leftEndpoint S.source T.source
    (shadow S) (shadow T) (shadow_compact S hK₁) (shadow_compact T hK₂)
    (singularLeft hneS) (singularRight hneT) (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT) (Ω) (hΩ)
private abbrev phaseRight : SourceReducedComplexSpace :=
  OriginalNativeHSEqualProfilePhaseComparison.rightEndpoint S.source T.source
    (shadow S) (shadow T) (shadow_compact S hK₁) (shadow_compact T hK₂)
    (singularLeft hneS) (singularRight hneT) (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT) (Ω) (hΩ)
private abbrev phaseLeftHistory : PhysicalHistory (N).source
    (phaseLeft c hK₁ hK₂ hL hL₁ hL₂ hneS hneT) :=
  OriginalNativeHSEqualProfilePhaseComparison.leftHistory S.source T.source
    (shadow S) (shadow T) (shadow_compact S hK₁) (shadow_compact T hK₂)
    (singularLeft hneS) (singularRight hneT) (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT) (Ω) (hΩ)
private abbrev phaseRightHistory : PhysicalHistory (N).source
    (phaseRight c hK₁ hK₂ hL hL₁ hL₂ hneS hneT) :=
  OriginalNativeHSEqualProfilePhaseComparison.rightHistory S.source T.source
    (shadow S) (shadow T) (shadow_compact S hK₁) (shadow_compact T hK₂)
    (singularLeft hneS) (singularRight hneT) (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT) (Ω) (hΩ)

local notation "PL" => phaseLeft c hK₁ hK₂ hL hL₁ hL₂ hneS hneT
local notation "PR" => phaseRight c hK₁ hK₂ hL hL₁ hL₂ hneS hneT
local notation "HL" => phaseLeftHistory c hK₁ hK₂ hL hL₁ hL₂ hneS hneT
local notation "HR" => phaseRightHistory c hK₁ hK₂ hL hL₁ hL₂ hneS hneT

private abbrev coupledLeft : (PL) ⟶ (SN hK₁ hneS).source :=
  OriginalNativeHSOuterPhaseCoupling.leftMap S.history T.history
    (baseShadow S) (baseShadow T) (baseShadow_compact S hK₁) (baseShadow_compact T hK₂)
    hneS hneT (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT)
private abbrev coupledRight : (PR) ⟶ (TN hK₂ hneT).source :=
  OriginalNativeHSOuterPhaseCoupling.rightMap S.history T.history
    (baseShadow S) (baseShadow T) (baseShadow_compact S hK₁) (baseShadow_compact T hK₂)
    hneS hneT (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT)

local notation "lS" => coupledLeft c hK₁ hK₂ hL hL₁ hL₂ hneS hneT
local notation "lT" => coupledRight c hK₁ hK₂ hL hL₁ hL₂ hneS hneT

private theorem coupledLeft_open : LocallyRingedSpace.IsOpenImmersion (lS).hom.left :=
  OriginalNativeHSOuterPhaseCoupling.leftMap_isOpenImmersion S.history T.history
    (baseShadow S) (baseShadow T) (baseShadow_compact S hK₁) (baseShadow_compact T hK₂)
    hneS hneT (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT)
private theorem coupledRight_open : LocallyRingedSpace.IsOpenImmersion (lT).hom.left :=
  OriginalNativeHSOuterPhaseCoupling.rightMap_isOpenImmersion S.history T.history
    (baseShadow S) (baseShadow T) (baseShadow_compact S hK₁) (baseShadow_compact T hK₂)
    hneS hneT (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT)

/-- The LITERAL left computed next-history prescribed endpoint. -/
abbrev leftEndpoint := endpoint (SN hK₁ hneS) (V) (hV) (vS)
abbrev rightEndpoint := endpoint (TN hK₂ hneT) (V) (hV) (vT)
private abbrev leftInclusion : leftEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ⟶ (SN hK₁ hneS).source :=
  OriginalNativeHSCurrentOverlap.inclusion (SN hK₁ hneS) (V) (hV) (vS)
private abbrev rightInclusion : rightEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ⟶ (TN hK₂ hneT).source :=
  OriginalNativeHSCurrentOverlap.inclusion (TN hK₂ hneT) (V) (hV) (vT)
private abbrev leftHistory := OriginalNativeHSCurrentOverlap.history (SN hK₁ hneS) (V) (hV) (vS)
private abbrev rightHistory := OriginalNativeHSCurrentOverlap.history (TN hK₂ hneT) (V) (hV) (vT)
private abbrev nextOriginalLeft : (SN hK₁ hneS).source ⟶ X :=
  (SN hK₁ hneS).history.projection ≫ (SN hK₁ hneS).inclusion
private abbrev nextOriginalRight : (TN hK₂ hneT).source ⟶ X :=
  (TN hK₂ hneT).history.projection ≫ (TN hK₂ hneT).inclusion
private abbrev phaseOriginalLeft : (PL) ⟶ X := (HL).projection ≫ (N).inclusion ≫ r c ≫ iW c
private abbrev phaseOriginalRight : (PR) ⟶ X := (HR).projection ≫ (N).inclusion ≫ r c ≫ iW c

private theorem left_image_subset : range
    (leftInclusion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base ⊆ range (lS).hom.left.base := by
  rintro _ ⟨y,rfl⟩
  have hrange : range (lS).hom.left.base =
      (OriginalNativeHSShadowOuterRun.next_sourceMap S hK₁ hneS).hom.left.base ⁻¹'
        ((aS).hom.left.base '' ((N).openSet : Set (Z c).obj.left)) :=
    OriginalNativeHSOuterPhaseCoupling.leftMap_range S.history T.history
      (baseShadow S) (baseShadow T) (baseShadow_compact S hK₁) (baseShadow_compact T hK₂)
      hneS hneT (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT)
  apply (Set.ext_iff.mp hrange _).mpr
  apply saturate (aS).hom.left.base
    (S.history.projection ≫ S.inclusion).hom.left.base
    (OriginalNativeHSShadowOuterRun.next_sourceMap S hK₁ hneS).hom.left.base
    (nextOriginalLeft hK₁ hneS).hom.left.base (r c ≫ iW c).hom.left.base
    (c.openSet : Set X.obj.left) (V : Set X.obj.left) ((N).openSet : Set (Z c).obj.left)
    (fun z => congrArg (fun f : (SN hK₁ hneS).source ⟶ X => f.hom.left.base z)
      (OriginalNativeHSShadowOuterRun.next_projection_square S hK₁ hneS))
    (Context.left_range c)
    (fun z => congrArg (fun f : Z c ⟶ X => f.hom.left.base z) (Context.left_square c))
    (fun _ hz => OriginalNativeHSNextCommonBase.closure_subset_old c hK₁ hK₂ hL hL₁ hL₂ hneS hneT (subset_closure hz))
    (fun _ hz => OriginalNativeHSNextCommonBase.whole_fibre c hK₁ hK₂ hL hL₁ hL₂ hneS hneT _ hz)
  exact y.property

private theorem right_image_subset : range
    (rightInclusion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base ⊆ range (lT).hom.left.base := by
  rintro _ ⟨y,rfl⟩
  have hrange : range (lT).hom.left.base =
      (OriginalNativeHSShadowOuterRun.next_sourceMap T hK₂ hneT).hom.left.base ⁻¹'
        ((aT).hom.left.base '' ((N).openSet : Set (Z c).obj.left)) :=
    OriginalNativeHSOuterPhaseCoupling.rightMap_range S.history T.history
      (baseShadow S) (baseShadow T) (baseShadow_compact S hK₁) (baseShadow_compact T hK₂)
      hneS hneT (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT)
  apply (Set.ext_iff.mp hrange _).mpr
  apply saturate (aT).hom.left.base
    (T.history.projection ≫ T.inclusion).hom.left.base
    (OriginalNativeHSShadowOuterRun.next_sourceMap T hK₂ hneT).hom.left.base
    (nextOriginalRight hK₂ hneT).hom.left.base (r c ≫ iW c).hom.left.base
    (c.openSet : Set X.obj.left) (V : Set X.obj.left) ((N).openSet : Set (Z c).obj.left)
    (fun z => congrArg (fun f : (TN hK₂ hneT).source ⟶ X => f.hom.left.base z)
      (OriginalNativeHSShadowOuterRun.next_projection_square T hK₂ hneT))
    (Context.right_range c)
    (fun z => congrArg (fun f : Z c ⟶ X => f.hom.left.base z) (Context.right_square c))
    (fun _ hz => OriginalNativeHSNextCommonBase.closure_subset_old c hK₁ hK₂ hL hL₁ hL₂ hneS hneT (subset_closure hz))
    (fun _ hz => OriginalNativeHSNextCommonBase.whole_fibre c hK₁ hK₂ hL hL₁ hL₂ hneS hneT _ hz)
  exact y.property

private theorem left_lift : ∃ k : leftEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ⟶ (PL),
    LocallyRingedSpace.IsOpenImmersion k.hom.left ∧
      k ≫ (lS) = leftInclusion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT :=
  OriginalNativeSmoothOpenLocality.exists_native_open_lift (lS)
    (leftInclusion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
    (coupledLeft_open c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
    (OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion
      (SN hK₁ hneS).inclusion (SN hK₁ hneS).inclusion_isOpenImmersion (V) (hV) (vS) (SN hK₁ hneS).history)
    (left_image_subset c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
private theorem right_lift : ∃ k : rightEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ⟶ (PR),
    LocallyRingedSpace.IsOpenImmersion k.hom.left ∧
      k ≫ (lT) = rightInclusion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT :=
  OriginalNativeSmoothOpenLocality.exists_native_open_lift (lT)
    (rightInclusion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
    (coupledRight_open c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
    (OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion
      (TN hK₂ hneT).inclusion (TN hK₂ hneT).inclusion_isOpenImmersion (V) (hV) (vT) (TN hK₂ hneT).history)
    (right_image_subset c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)

def leftLift : leftEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ⟶ (PL) :=
  (left_lift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).choose
def rightLift : rightEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ⟶ (PR) :=
  (right_lift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).choose
theorem leftLift_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion
    (leftLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left := (left_lift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).choose_spec.1
theorem rightLift_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion
    (rightLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left := (right_lift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).choose_spec.1
theorem leftLift_square : leftLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ≫ (lS) =
    leftInclusion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT := (left_lift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).choose_spec.2
theorem rightLift_square : rightLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ≫ (lT) =
    rightInclusion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT := (right_lift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).choose_spec.2

private theorem left_phase_original : (lS) ≫ nextOriginalLeft hK₁ hneS =
    phaseOriginalLeft c hK₁ hK₂ hL hL₁ hL₂ hneS hneT := by
  have hphase : (lS) ≫ OriginalNativeHSShadowOuterRun.next_sourceMap S hK₁ hneS =
      (HL).projection ≫ (N).inclusion ≫ (aS) :=
    OriginalNativeHSOuterPhaseCoupling.left_old_square S.history T.history
      (baseShadow S) (baseShadow T) (baseShadow_compact S hK₁) (baseShadow_compact T hK₂)
      hneS hneT (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT)
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  have hn := congrArg (fun f : (SN hK₁ hneS).source ⟶ X => f.hom.left.base ((lS).hom.left.base z))
    (OriginalNativeHSShadowOuterRun.next_projection_square S hK₁ hneS)
  have hp := congrArg (fun f : (PL) ⟶ S.source => f.hom.left.base z) hphase
  have hc := congrArg (fun f : Z c ⟶ X =>
    f.hom.left.base ((N).inclusion.hom.left.base ((HL).projection.hom.left.base z))) (Context.left_square c)
  exact hn.trans ((congrArg (S.history.projection ≫ S.inclusion).hom.left.base hp).trans hc.symm)

private theorem right_phase_original : (lT) ≫ nextOriginalRight hK₂ hneT =
    phaseOriginalRight c hK₁ hK₂ hL hL₁ hL₂ hneS hneT := by
  have hphase : (lT) ≫ OriginalNativeHSShadowOuterRun.next_sourceMap T hK₂ hneT =
      (HR).projection ≫ (N).inclusion ≫ (aT) :=
    OriginalNativeHSOuterPhaseCoupling.right_old_square S.history T.history
      (baseShadow S) (baseShadow T) (baseShadow_compact S hK₁) (baseShadow_compact T hK₂)
      hneS hneT (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT)
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  have hn := congrArg (fun f : (TN hK₂ hneT).source ⟶ X => f.hom.left.base ((lT).hom.left.base z))
    (OriginalNativeHSShadowOuterRun.next_projection_square T hK₂ hneT)
  have hp := congrArg (fun f : (PR) ⟶ T.source => f.hom.left.base z) hphase
  have hc := congrArg (fun f : Z c ⟶ X =>
    f.hom.left.base ((N).inclusion.hom.left.base ((HR).projection.hom.left.base z))) (Context.right_square c)
  exact hn.trans ((congrArg (T.history.projection ≫ T.inclusion).hom.left.base hp).trans hc.symm)

theorem leftLift_range : range (leftLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base =
    (phaseOriginalLeft c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base ⁻¹' (V : Set X.obj.left) := by
  have hr := factor_range (leftLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT) (lS)
    (leftInclusion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
    (coupledLeft_open c hK₁ hK₂ hL hL₁ hL₂ hneS hneT) (leftLift_square c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
  have hi : range (leftInclusion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base =
      (nextOriginalLeft hK₁ hneS).hom.left.base ⁻¹' (V : Set X.obj.left) := by
    change range (Subtype.val : preimageOpen (OriginalNativePrescribedOpenHistory.pullbackOpen
      (SN hK₁ hneS).inclusion (V)) (SN hK₁ hneS).history.projection → (SN hK₁ hneS).source.obj.left) = _
    rw [Subtype.range_coe]
    rfl
  ext y
  have hm := Set.ext_iff.mp hr y
  rw [hi] at hm
  have hy := congrArg (fun f : (PL) ⟶ X => f.hom.left.base y) (left_phase_original c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
  exact hm.trans (iff_of_eq (congrArg (fun x : X.obj.left => x ∈ (V : Set X.obj.left)) hy))
theorem rightLift_range : range (rightLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base =
    (phaseOriginalRight c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base ⁻¹' (V : Set X.obj.left) := by
  have hr := factor_range (rightLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT) (lT)
    (rightInclusion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
    (coupledRight_open c hK₁ hK₂ hL hL₁ hL₂ hneS hneT) (rightLift_square c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
  have hi : range (rightInclusion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base =
      (nextOriginalRight hK₂ hneT).hom.left.base ⁻¹' (V : Set X.obj.left) := by
    change range (Subtype.val : preimageOpen (OriginalNativePrescribedOpenHistory.pullbackOpen
      (TN hK₂ hneT).inclusion (V)) (TN hK₂ hneT).history.projection → (TN hK₂ hneT).source.obj.left) = _
    rw [Subtype.range_coe]
    rfl
  ext y
  have hm := Set.ext_iff.mp hr y
  rw [hi] at hm
  have hy := congrArg (fun f : (PR) ⟶ X => f.hom.left.base y) (right_phase_original c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
  exact hm.trans (iff_of_eq (congrArg (fun x : X.obj.left => x ∈ (V : Set X.obj.left)) hy))

local notation "hProfileType" => OriginalNativeHSFactoryTerminalFrame.profile S.source (shadow S)
  (shadow_compact S hK₁) (singularLeft hneS) = OriginalNativeHSFactoryTerminalFrame.profile T.source (shadow T)
    (shadow_compact T hK₂) (singularRight hneT)

private def phaseComparison (hProfile : hProfileType) : (PR) ≅ (PL) :=
  OriginalNativeHSEqualProfilePhaseComparison.comparison S.source T.source
    (shadow S) (shadow T) (shadow_compact S hK₁) (shadow_compact T hK₂)
    (singularLeft hneS) (singularRight hneT) (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT) (Ω) (hΩ) hProfile

private theorem phase_comparison_original (hProfile : hProfileType) :
    (phaseComparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile).hom ≫
      phaseOriginalLeft c hK₁ hK₂ hL hL₁ hL₂ hneS hneT =
        phaseOriginalRight c hK₁ hK₂ hL hL₁ hL₂ hneS hneT := by
  have h : (phaseComparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile).hom ≫ (HL).projection =
      (HR).projection := OriginalNativeHSEqualProfilePhaseComparison.comparison_projection S.source T.source
    (shadow S) (shadow T) (shadow_compact S hK₁) (shadow_compact T hK₂)
    (singularLeft hneS) (singularRight hneT) (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT) (Ω) (hΩ) hProfile
  simpa only [phaseOriginalLeft,phaseOriginalRight,Category.assoc] using
    congrArg (fun f => f ≫ (N).inclusion ≫ r c ≫ iW c) h

private abbrev rightToLeftPhase (hProfile : hProfileType) :=
  rightLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ≫ (phaseComparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile).hom

private theorem rightToLeftPhase_open (hProfile : hProfileType) :
    LocallyRingedSpace.IsOpenImmersion (rightToLeftPhase c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile).hom.left := by
  have he : LocallyRingedSpace.IsOpenImmersion
      (phaseComparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile).hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft (phaseComparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile)).hom
    infer_instance
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _
    (rightLift_isOpenImmersion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT) _ he

private theorem comparison_range (hProfile : hProfileType) :
    range (leftLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base =
      range (rightToLeftPhase c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile).hom.left.base := by
  let F := phaseComparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile
  have hF := phase_comparison_original c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile
  ext z
  constructor
  · intro hz
    have hzV := (Set.ext_iff.mp (leftLift_range c hK₁ hK₂ hL hL₁ hL₂ hneS hneT) z).mp hz
    have hInv : F.hom.hom.left.base (F.inv.hom.left.base z) = z :=
      congrArg (fun f : (PL) ⟶ (PL) => f.hom.left.base z) F.inv_hom_id
    have hq := congrArg (fun f : (PR) ⟶ X => f.hom.left.base (F.inv.hom.left.base z)) hF
    have hp : F.inv.hom.left.base z ∈ range (rightLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base := by
      apply (Set.ext_iff.mp (rightLift_range c hK₁ hK₂ hL hL₁ hL₂ hneS hneT) _).mpr
      change (phaseOriginalRight c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base (F.inv.hom.left.base z) ∈ (V : Set X.obj.left)
      exact ((congrArg (phaseOriginalLeft c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base hInv).symm.trans hq) ▸ hzV
    obtain ⟨y,hy⟩ := hp
    exact ⟨y,(congrArg F.hom.hom.left.base hy).trans hInv⟩
  · rintro ⟨y,rfl⟩
    apply (Set.ext_iff.mp (leftLift_range c hK₁ hK₂ hL hL₁ hL₂ hneS hneT) _).mpr
    have hzV := (Set.ext_iff.mp (rightLift_range c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
      ((rightLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base y)).mp ⟨y,rfl⟩
    have hp := congrArg (fun f : (PR) ⟶ X => f.hom.left.base
      ((rightLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base y)) hF
    change (phaseOriginalLeft c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base
      (F.hom.hom.left.base ((rightLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base y)) ∈ (V : Set X.obj.left)
    exact hp.symm ▸ hzV

/-- ACTUAL full native iso of the LITERAL prescribed next-history endpoints. -/
def comparison (hProfile : hProfileType) :
    leftEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ≅ rightEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT :=
  nativeIsoOfRange (leftLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
    (rightToLeftPhase c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile)
    (leftLift_isOpenImmersion c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
    (rightToLeftPhase_open c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile)
    (comparison_range c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile)

private theorem comparison_phase_square (hProfile : hProfileType) :
    (comparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile).hom ≫
      rightToLeftPhase c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile =
        leftLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT :=
  nativeIsoOfRange_square _ _ _ _ _

private theorem left_endpoint_square :
    (leftHistory c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).projection ≫ inclusion X (V) (hV) =
      leftLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ≫ phaseOriginalLeft c hK₁ hK₂ hL hL₁ hL₂ hneS hneT := by
  have hs := OriginalNativePrescribedOpenHistory.projection_square
    (SN hK₁ hneS).inclusion (SN hK₁ hneS).inclusion_isOpenImmersion (V) (hV) (vS) (SN hK₁ hneS).history
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro y
  have ha := congrArg (fun f : leftEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ⟶ X => f.hom.left.base y) hs
  have hb := congrArg (fun f => f.hom.left.base y) (leftLift_square c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
  have hc := congrArg (fun f : (PL) ⟶ X => f.hom.left.base
    ((leftLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base y))
      (left_phase_original c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
  exact ha.trans ((congrArg (nextOriginalLeft hK₁ hneS).hom.left.base hb.symm).trans hc)

private theorem right_endpoint_square :
    (rightHistory c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).projection ≫ inclusion X (V) (hV) =
      rightLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ≫ phaseOriginalRight c hK₁ hK₂ hL hL₁ hL₂ hneS hneT := by
  have hs := OriginalNativePrescribedOpenHistory.projection_square
    (TN hK₂ hneT).inclusion (TN hK₂ hneT).inclusion_isOpenImmersion (V) (hV) (vT) (TN hK₂ hneT).history
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro y
  have ha := congrArg (fun f : rightEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ⟶ X => f.hom.left.base y) hs
  have hb := congrArg (fun f => f.hom.left.base y) (rightLift_square c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
  have hc := congrArg (fun f : (PR) ⟶ X => f.hom.left.base
    ((rightLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base y))
      (right_phase_original c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
  exact ha.trans ((congrArg (nextOriginalRight hK₂ hneT).hom.left.base hb.symm).trans hc)

theorem comparison_projection (hProfile : hProfileType) :
    (comparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile).hom ≫
      (rightHistory c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).projection =
        (leftHistory c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).projection := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro y
  apply (inclusion_isOpenImmersion X (V) (hV)).base_open.injective
  let E := comparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile
  let F := phaseComparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile
  have h1 := congrArg (fun f : rightEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ⟶ X =>
    f.hom.left.base (E.hom.hom.left.base y)) (right_endpoint_square c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
  have h2 := congrArg (fun f : (PR) ⟶ X => f.hom.left.base
    ((rightLift c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base (E.hom.hom.left.base y)))
      (phase_comparison_original c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile)
  have h3 := congrArg (fun f => f.hom.left.base y)
    (comparison_phase_square c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile)
  have h4 := congrArg (fun f : leftEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT ⟶ X =>
    f.hom.left.base y) (left_endpoint_square c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
  exact h1.trans (h2.symm.trans
    ((congrArg (phaseOriginalLeft c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).hom.left.base h3).trans h4.symm))

theorem comparison_scalar (hProfile : hProfileType) :
    (comparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile).hom.hom.left ≫
      (rightEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).obj.hom =
        (leftEndpoint c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).obj.hom :=
  Over.w (comparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile).hom.hom

/-- A genuinely constructed next PAST context, with no future comparison input. -/
def next (hProfile : hProfileType) : Context (SN hK₁ hneS) (TN hK₂ hneT) L where
  openSet := (V)
  compactClosure := (hV)
  contains := OriginalNativeHSNextCommonBase.contains c hK₁ hK₂ hL hL₁ hL₂ hneS hneT
  leftRange := (vS)
  rightRange := (vT)
  comparison := comparison c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile
  square := comparison_projection c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile

include hL hL₁ hL₂ in
theorem exists_context (hProfile : hProfileType) :
    ∃ d : Context (OriginalNativeHSShadowOuterRun.next S hK₁ hneS)
      (OriginalNativeHSShadowOuterRun.next T hK₂ hneT) L, d.openSet ≤ c.openSet := by
  refine ⟨next c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hProfile,?_⟩
  intro x hx
  exact OriginalNativeHSNextCommonBase.closure_subset_old c hK₁ hK₂ hL hL₁ hL₂ hneS hneT (subset_closure hx)

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSEqualOuterSuccessor
