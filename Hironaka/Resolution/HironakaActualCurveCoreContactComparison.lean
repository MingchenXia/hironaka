import Hironaka.Resolution.HironakaActualInitialCountCoreComparison
import Hironaka.Invariant.StepOneTangentChange

/-! Actual ANYTEST curve semantics replaces lower CAN in the genuine
whole-boundary contact-reference comparison. The actual prefix and tails,
all old empty slots and every chronological birth remain unchanged. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualCurveCoreContactComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupTowerIsomorphism
  HironakaActualRecursiveCoreValues NonmonomialOrderLocal HomogenizedIdealAlong
  StepOneValue StepOneTangentChange MaximalOrderStepOneB ContactStageKept
  ContactStageInvDomain HomogenizedGlueingTower MaxLocusLocal
  StepOneValueMasked StepOneMaskTower StepOneLowerDomain StepOneRegime StepOneCompare
  BlowupTowerSplit HironakaActualInitialCountCoreComparison CanonicalCentres HironakaStageCenters
open ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ}

/-- The ACTUAL projected curve value commutes with real open restriction
on ANY source TEST, without native or lower CAN. -/
theorem actual_curve_core_restrict (hn : 0<n) (k : ℕ) {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M) (U : Opens X)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (p : openPreimage T U) (hp : (p : Y) ∈ (geoTransformAlong M T).cosupp) :
    coreInv hn (k+1) (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) p =
      coreInv hn (k+1) M T p := by
  have hU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hTU := isGeoTestTower_restrict U hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent T hT
  have hpU : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M)
      (restrict U T)).cosupp := by
    rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
      hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent U T hT]
    exact hp
  rw [actual_curve_core_value hn k _ hU _ hTU p hpU,
    actual_curve_core_value hn k M hM T hT p hp]
  apply congrArg (curveCoreValue k)
  rw [geoTransformAlong_restrict U hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent T hT]
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  exact nmOrd_pullback_val hn hCurrent.isWellFormed hCurrent.isNonzeroAlongAt _ p

/-- Actual tower isomorphisms preserve the projected native curve value
on ANY source TEST; domains/tests/cosupports are derived geometrically. -/
theorem actual_curve_core_isTowerIso (hn : 0<n) (k : ℕ) {X X' Y Y' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower M T)
    (p : Y') (hp : χ p ∈ (geoTransformAlong M T).cosupp) :
    coreInv hn (k+1) (MarkedIdeal.pullback Φ M) T' p = coreInv hn (k+1) M T (χ p) := by
  have hM' := InvDomainTowerAlong.isInvDomain_pullback Φ hM
  have hT' := (IsTowerIso.isGeoTestTower_iff Φ hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hIso).mpr hT
  have hp' : p ∈ (geoTransformAlong (MarkedIdeal.pullback Φ M) T').cosupp := by
    rw [IsTowerIso.cosupp_geoTransformAlong Φ hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hIso hT]
    exact hp
  rw [actual_curve_core_value hn k _ hM' _ hT' p hp',
    actual_curve_core_value hn k M hM T hT (χ p) hp]
  exact congrArg (curveCoreValue k) (nmOrd_geoTransformAlong_isTowerIso hn Φ hM hIso hT p)

private theorem curve_core_nested (hn : 0<n) (k : ℕ) {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) {W V : Opens X} (hVW : V≤W)
    (hW : IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : W → X) M))
    (T : BlowupTower X Y)
    (hTW : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → X) M) (restrict W T)) :
    IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : V → X) M) ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) ∧
      ∀ p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T)).cosupp,
        coreInv hn (k+1) (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) p =
          coreInv hn (k+1) (MarkedIdeal.pullback (Subtype.val : W → X) M) (restrict W T)
            ⟨(p : Y), openPreimage_mono T hVW p.2⟩ := by
  have hNested := InvDomainTowerAlong.isInvDomain_pullback_val (nestedOpens W V) hW
  have hTestNested := isGeoTestTower_restrict (nestedOpens W V)
    hW.isWellFormed.isClosedSubmanifold_N hW.isWellFormed.isCoherent (restrict W T) hTW
  have hIso := (isTowerIso_restrict_nestedOpens (X := X) hVW T).symm
  have hEq := pullback_symm_nestedOpensDiffeo (M := X) hI hVW
  have hV := InvDomainTowerAlong.isInvDomain_pullback (nestedOpensDiffeo (n := n) hVW).symm hNested
  rw [hEq] at hV
  have hTV := (IsTowerIso.isGeoTestTower_iff (nestedOpensDiffeo (n := n) hVW).symm
    hNested.isWellFormed.isClosedSubmanifold_N hNested.isWellFormed.isCoherent hIso).mpr hTestNested
  rw [hEq] at hTV
  refine ⟨hV, hTV, ?_⟩
  intro p hp
  have hCos := IsTowerIso.cosupp_geoTransformAlong (nestedOpensDiffeo (n := n) hVW).symm
    hNested.isWellFormed.isClosedSubmanifold_N hNested.isWellFormed.isCoherent hIso hTestNested
  rw [hEq] at hCos
  have hpNested := hp
  rw [hCos] at hpNested
  have hCore := actual_curve_core_isTowerIso hn k (nestedOpensDiffeo (n := n) hVW).symm
    _ hNested hIso hTestNested p hpNested
  rw [hEq] at hCore
  rw [hCore]
  apply actual_curve_core_restrict hn k _ hW (nestedOpens W V) (restrict W T) hTW
  have hpW := hpNested
  rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hW.isWellFormed.isClosedSubmanifold_N hW.isWellFormed.isCoherent
    (nestedOpens W V) (restrict W T) hTW] at hpW
  exact hpW

/-- Actual source dimension-two geometry DERIVES both kept contact curve
domains/tests and then their ANYTEST core comparison. No lower CAN input. -/
theorem actual_kept_contact_curve_core_comparison
    (hn : 0<n) (k : ℕ) {X : CMfd.{u} n}
    (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J) {x : X} (hx : x ∈ J.cosupp)
    {u v : X → ℂ} (U₁ U₂ : Opens X)
    (hu : TangentDirectionAlong.IsTangentDirectionAlong J.N J.ideal J.d U₁ u) (hxU₁ : x∈U₁)
    (hv : TangentDirectionAlong.IsTangentDirectionAlong J.N J.ideal J.d U₂ v) (hxU₂ : x∈U₂) :
    ∃ O : Opens X, x∈O ∧ ∀ {Y Z : CMfd.{u} n} (T₀ : BlowupTower X Y) (T₁ : BlowupTower Y Z),
      IsGeoTestTower (barMarked J) (T₀.append T₁) →
      ∀ (W W' : Opens Y), (W : Set Y) ⊆ openPreimage T₀ U₁ →
        (W' : Set Y) ⊆ openPreimage T₀ U₂ →
        (∀ H∈(geoTransformAlong (barMarked J) T₀).E.take J.E.length, Disjoint (W : Set Y) H) →
        (∀ H∈(geoTransformAlong (barMarked J) T₀).E.take J.E.length, Disjoint (W' : Set Y) H) →
        (∀ y∈W, y∈strictAlong T₀ (J.N∩{p | u p=0}) →
          y∉CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked J) T₀).N
            (geoTransformAlong (barMarked J) T₀).ideal (geoTransformAlong (barMarked J) T₀).d) →
        (∀ y∈W', y∈strictAlong T₀ (J.N∩{p | v p=0}) →
          y∉CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked J) T₀).N
            (geoTransformAlong (barMarked J) T₀).ideal (geoTransformAlong (barMarked J) T₀).d) →
        IsInvDomain 1 (contactMarkedKept J u T₀ W) ∧
        IsInvDomain 1 (contactMarkedKept J v T₀ W') ∧
        IsGeoTestTower (contactMarkedKept J u T₀ W) (restrict W T₁) ∧
        IsGeoTestTower (contactMarkedKept J v T₀ W') (restrict W' T₁) ∧
        (geoTransformAlong (contactMarkedKept J u T₀ W) (restrict W T₁)).cosupp=
          (Subtype.val : openPreimage T₁ W → Z) ⁻¹' (geoTransformAlong (barMarked J) (T₀.append T₁)).cosupp ∧
        (geoTransformAlong (contactMarkedKept J v T₀ W') (restrict W' T₁)).cosupp=
          (Subtype.val : openPreimage T₁ W' → Z) ⁻¹' (geoTransformAlong (barMarked J) (T₀.append T₁)).cosupp ∧
        ∀ (p : openPreimage T₁ W) (q : openPreimage T₁ W'), (p : Z)=q →
          T₀.proj (T₁.proj p)∈O → (p : Z)∈(geoTransformAlong (barMarked J) (T₀.append T₁)).cosupp →
          coreInv hn (k+1) (contactMarkedKept J u T₀ W) (restrict W T₁) p=
            coreInv hn (k+1) (contactMarkedKept J v T₀ W') (restrict W' T₁) q := by
  obtain ⟨O, hxO, hO⟩ := exists_tail_iso_opens (M := X) hJ.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d hx hu hxU₁ hv hxU₂
  refine ⟨O, hxO, ?_⟩
  intro Y Z T₀ T₁ hT W W' hWU hW'U hmW hmW' hZ hZ'
  have hT₀ := ((isGeoTestTower_append_iff (barMarked J) T₀ T₁).mp hT).1
  have hDu : IsInvDomain 1 (contactMarkedKept J u T₀ W) :=
    isInvDomain_stage_coeffHomAlong_of_le J hJ.isWellFormed hJ.one_le_d hJ.dimLE
      U₁ hu T₀ hT₀ W hWU hZ
      (fun H hH y hy _ => Set.disjoint_left.mp (hmW H hH) hy)
  have hDv : IsInvDomain 1 (contactMarkedKept J v T₀ W') :=
    isInvDomain_stage_coeffHomAlong_of_le J hJ.isWellFormed hJ.one_le_d hJ.dimLE
      U₂ hv T₀ hT₀ W' hW'U hZ'
      (fun H hH y hy _ => Set.disjoint_left.mp (hmW' H hH) hy)
  have hTu := ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le J
    hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d
    U₁ hu T₀ T₁ hT W hWU
  have hTv := ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le J
    hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d
    U₂ hv T₀ T₁ hT W' hW'U
  refine ⟨hDu, hDv, hTu.1, hTv.1, hTu.2, hTv.2, ?_⟩
  intro p q hpq hpO hpCos
  have hT' : IsGeoTestTower (stepOneMarked J.N J.ideal J.d) (T₀.append T₁) :=
    StepOneRegime.isGeoTestTower_stepOneMarked_of_coeffHom J _ hT
  have hpCos' : (p : Z) ∈ (geoTransformAlong (stepOneMarked J.N J.ideal J.d) (T₀.append T₁)).cosupp := by
    rw [StepOneRegime.cosupp_geoTransformAlong_stepOneMarked]
    exact hpCos
  have hpW' : T₁.proj (p : Z)∈W' := by rw [hpq]; exact q.2
  obtain ⟨Vu, Vv, hzu, hzv, ψ, ξ, hVuW, hVvW', hIso, hξ, hψS⟩ :=
    hO T₀ T₁ hT' W W' p p.2 hpW' hpO hpCos'
  have hψKept : MarkedIdeal.pullback ψ (contactMarkedKept J u T₀ Vu)=
      contactMarkedKept J v T₀ Vv := by
    dsimp only [contactMarkedKept]
    rw [pullback_val_restrictedCoeffHom_eq J T₀ u Vu
        (fun H hH y hy => Set.disjoint_left.mp (hmW H hH) (hVuW hy)),
      pullback_val_restrictedCoeffHom_eq J T₀ v Vv
        (fun H hH y hy => Set.disjoint_left.mp (hmW' H hH) (hVvW' hy)),
      pullback_replicate_empty, hψS]
  have hcu := isCoherent_restrictedCoeff J hJ.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N u T₀ hT₀
  have hcv := isCoherent_restrictedCoeff J hJ.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N v T₀ hT₀
  obtain ⟨hDVu, hTVu, hValu⟩ := curve_core_nested hn k _ hcu hVuW hDu T₁ hTu.1
  obtain ⟨_hDVv, _hTVv, hValv⟩ := curve_core_nested hn k _ hcv hVvW' hDv T₁ hTv.1
  have hCosu : (⟨(p : Z),hzu⟩ : openPreimage T₁ Vu) ∈
      (geoTransformAlong (contactMarkedKept J u T₀ Vu) (restrict Vu T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le J
      hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d
      U₁ hu T₀ T₁ hT Vu (fun y hy => hWU (hVuW hy))).2]
    exact hpCos
  have hCosv : (⟨(p : Z),hzv⟩ : openPreimage T₁ Vv) ∈
      (geoTransformAlong (contactMarkedKept J v T₀ Vv) (restrict Vv T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le J
      hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d
      U₂ hv T₀ T₁ hT Vv (fun y hy => hW'U (hVvW' hy))).2]
    exact hpCos
  have hCore := actual_curve_core_isTowerIso hn k ψ _ hDVu hIso hTVu
    ⟨(p : Z),hzv⟩ (by rw [hξ]; exact hCosu)
  rw [hξ, hψKept] at hCore
  have hpEq : (⟨(p : Z),hVuW hzu⟩ : openPreimage T₁ W)=p := rfl
  have hqEq : (⟨(p : Z),hVvW' hzv⟩ : openPreimage T₁ W')=q := Subtype.ext hpq
  have hValu' := hValu ⟨(p : Z),hzu⟩ hCosu
  have hValv' := hValv ⟨(p : Z),hzv⟩ hCosv
  rw [hpEq] at hValu'
  rw [hqEq] at hValv'
  exact hValu'.symm.trans (hCore.symm.trans hValv')

private theorem split_at_length {X : CMfd.{u} n} :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), split T T.length=⟨X,.refl,T⟩
  | _, .refl => rfl
  | _, .step T C π hπ => by
      change (⟨(split T T.length).1, (split T T.length).2.1,
        .step (split T T.length).2.2 C π hπ⟩ :
          Σ A : CMfd.{u} n, BlowupTower X A × BlowupTower A _) = _
      rw [split_at_length T]

private theorem native_zero_full_run {X Y : CMfd.{u} n}
    {d : ℕ} {Λ : Type v} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n d Λ)
    (J : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y)
    (hNotSpecial : ¬IsSpecial J T y) (hLevel : level J T y=0)
    (hRun : regimeRun (stepRegime J 0) T y=T.length)
    (hOwn : y∈openPreimage T (lowerMask J 0 (.refl : BlowupTower X X) (T.proj y))) :
    Seq.StepOneValueMasked.stepOneInvM R J T y=
      toLex (0, ((R.inv (lowerMarkedM J 0 (.refl : BlowupTower X X) (T.proj y))
        (restrict (lowerMask J 0 (.refl : BlowupTower X X) (T.proj y)) T)
          ⟨y,hOwn⟩ : Λ) : WithTop Λ)) := by
  change Seq.StepOneValueMasked.stepOneInvL R J (lowerMarkedM J) T y=_
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R J _ T hNotSpecial,hLevel,hRun]
  unfold head tail
  rw [split_at_length T]
  have hOwn' : T.proj y∈lowerMask J 0 (.refl : BlowupTower X X) (T.proj y) := hOwn
  rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem R J _ hOwn']

private theorem initial_zero_chosen_contact_comparison
    (hn : 0<n) (k : ℕ) {X : CMfd.{u} n} (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (a : X) (ha : a∈(barMarked J).cosupp)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T)
    (p : openPreimage T (lowerMask J 0 (.refl : BlowupTower X X) a))
    (hpParent : (p : Y)∈(geoTransformAlong (barMarked J) T).cosupp) :
    ∃ hOwn : (p : Y)∈openPreimage T (lowerMask J 0 (.refl : BlowupTower X X) (T.proj p)),
      coreInv hn (k+1) (lowerMarkedM J 0 (.refl : BlowupTower X X) a)
        (restrict (lowerMask J 0 (.refl : BlowupTower X X) a) T) p =
      coreInv hn (k+1) (lowerMarkedM J 0 (.refl : BlowupTower X X) (T.proj p))
        (restrict (lowerMask J 0 (.refl : BlowupTower X X) (T.proj p)) T) ⟨(p : Y),hOwn⟩ := by
  have hT' : IsGeoTestTower (barMarked J) ((.refl : BlowupTower X X).append T) := by
    simpa only [BlowupTower.refl_append] using hT
  have hClosed : ∀H∈J.E,IsClosed H := fun H hH=>hJ.isWellFormed.isSNCDivisor.1 H hH
  let z := T.proj (p : Y)
  have hzBar : z∈(barMarked J).cosupp := proj_mem_cosupp_of_mem_cosupp (𝔪 := barMarked J)
    hJ.isWellFormed.isClosedSubmanifold_N
    (isCoherent_barMarked J hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent)
    T hT hpParent
  have hzJ : z∈J.cosupp := by
    rw [←cosupp_barMarked J hJ.isWellFormed hJ.one_le_d]
    exact hzBar
  have hzLevel : level J (.refl : BlowupTower X X) z=0 :=
    level_eq_zero_of_mem_maskB J hClosed (.refl : BlowupTower X X) .refl p.2
  have hzNotSpecial : ¬IsSpecial J (.refl : BlowupTower X X) z := by
    rintro (⟨_,hZ⟩ | ⟨hPos,_⟩)
    · exact (interior_subset p.2).2.2 hZ
    · omega
  obtain ⟨hzOwn,_hOwnDomain⟩ := mem_lowerMask_and_isInvDomain_M J hJ.isWellFormed hJ.one_le_d
    hn hMax hJ.dimLE (.refl : BlowupTower X X) trivial hzBar ⟨hzLevel,hzNotSpecial⟩
  have hzOwnT : (p : Y)∈openPreimage T (lowerMask J 0 (.refl : BlowupTower X X) z) := hzOwn
  obtain ⟨_haU,hu⟩ := tangentChoice_spec J (exists_tangent_of_mem_cosupp J
    hJ.isWellFormed hJ.one_le_d hMax (.refl : BlowupTower X X) trivial ha)
  obtain ⟨hzU,hv⟩ := tangentChoice_spec J (exists_tangent_of_mem_cosupp J
    hJ.isWellFormed hJ.one_le_d hMax (.refl : BlowupTower X X) trivial hzBar)
  let U₁ : Opens X := ⟨(tangentChoice J a).1,hu.isOpen⟩
  let U₂ : Opens X := ⟨(tangentChoice J z).1,hv.isOpen⟩
  obtain ⟨O,hzO,hCompare⟩ := actual_kept_contact_curve_core_comparison hn k J hJ hzJ
    U₁ U₂ hu (interior_subset p.2).1 hv hzU
  have hComparison := hCompare (.refl : BlowupTower X X) T hT'
    (maskB J (.refl : BlowupTower X X) a) (maskB J (.refl : BlowupTower X X) z)
    (fun y hy=>(interior_subset hy).1) (fun y hy=>(interior_subset hy).1)
    (fun H hH=>Set.disjoint_left.mpr (fun y hy hyH=>(interior_subset hy).2.1 H hH hyH))
    (fun H hH=>Set.disjoint_left.mpr (fun y hy hyH=>(interior_subset hy).2.1 H hH hyH))
    (fun y hy _=>(interior_subset hy).2.2) (fun y hy _=>(interior_subset hy).2.2)
  have hSameCore := hComparison.2.2.2.2.2.2 p
    (⟨(p : Y),hzOwnT⟩ : openPreimage T (lowerMask J 0 (.refl : BlowupTower X X) z))
    rfl hzO (by simpa only [BlowupTower.refl_append] using hpParent)
  exact ⟨hzOwnT,hSameCore⟩

private theorem projected_native_zero {X Y : CMfd.{u} n}
    (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y)
    (value : ValTy (k+1))
    (hNative : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T y=
      toLex (0,(value : WithTop (ValTy (k+1))))) :
    stepOneCoreInv hn k J T y=
      toLex (0,((eraseGamma (k+1) value : ValTy (k+1)) : WithTop (ValTy (k+1)))) := by
  unfold stepOneCoreInv
  rw [hNative]
  rfl

/-- The ACTUAL independently chosen initial tangent reference is compared
to the fixed contact model by proof on EVERY original parent TEST. -/
theorem actual_initial_zero_count_curve_core_comparison
    (hn : 0<n) (k : ℕ) {X : CMfd.{u} n} (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (a : X)
    (ha : a∈(barMarked J).cosupp) (hLevel : level J (.refl : BlowupTower X X) a=0)
    (hNotSpecial : ¬IsSpecial J (.refl : BlowupTower X X) a) :
    let W := lowerMask J 0 (.refl : BlowupTower X X) a
    let L := lowerMarkedM J 0 (.refl : BlowupTower X X) a
    a∈W ∧ IsInvDomain 1 L ∧
      ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (barMarked J) T →
        IsGeoTestTower L (restrict W T) ∧
        (geoTransformAlong L (restrict W T)).cosupp=
          (Subtype.val : openPreimage T W → Y) ⁻¹' (geoTransformAlong (barMarked J) T).cosupp ∧
        ∀ p∈(geoTransformAlong L (restrict W T)).cosupp,
          stepOneCoreInv hn k J T p=toLex (0, ((curveCoreValue k
            (nmOrd (geoTransformAlong L (restrict W T)) p) : ValTy (k+1)) : WithTop (ValTy (k+1)))) := by
  dsimp only
  obtain ⟨hW,hL⟩ := mem_lowerMask_and_isInvDomain_M J hJ.isWellFormed hJ.one_le_d
    hn hMax hJ.dimLE (.refl : BlowupTower X X) trivial ha ⟨hLevel,hNotSpecial⟩
  refine ⟨hW,hL,?_⟩
  intro Y T hT
  have hT' : IsGeoTestTower (barMarked J) ((.refl : BlowupTower X X).append T) := by
    simpa only [BlowupTower.refl_append] using hT
  obtain ⟨hTL,hCos⟩ := isGeoTestTower_cosupp_lowerMarkedB J hJ.isWellFormed
    hJ.one_le_d hMax (.refl : BlowupTower X X) T hT' ha
  simp only [BlowupTower.refl_append] at hCos
  refine ⟨hTL,hCos,?_⟩
  intro p hp
  have hpParent : (p : Y)∈(geoTransformAlong (barMarked J) T).cosupp := by
    have hpB : p∈(geoTransformAlong (lowerMarkedB J (.refl : BlowupTower X X) a)
        (restrict (maskB J (.refl : BlowupTower X X) a) T)).cosupp := hp
    rw [hCos] at hpB
    exact hpB
  have hClosed : ∀H∈J.E,IsClosed H := fun H hH=>hJ.isWellFormed.isSNCDivisor.1 H hH
  have hpLevel' := level_eq_zero_of_mem_maskB J hClosed (.refl : BlowupTower X X) T p.2
  have hpLevel : level J T p=0 := by simpa only [BlowupTower.refl_append] using hpLevel'
  have hReg := stepRegime_and_le_regimeRun_of_mem_lowerMask J hJ.isWellFormed hJ.one_le_d
    hMax (.refl : BlowupTower X X) T hT' hLevel p.2 hpLevel'
  simp only [BlowupTower.refl_append] at hReg
  have hRun : regimeRun (stepRegime J 0) T p=T.length :=
    (regimeRun_le_length _ T p).antisymm hReg.2
  let z := T.proj (p : Y)
  obtain ⟨hzOwnT,hSameCore⟩ := initial_zero_chosen_contact_comparison hn k J hJ hMax a ha
    T hT p hpParent
  have hNative : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T p=
      toLex (0, (((invFamily hn (k+1)).inv (lowerMarkedM J 0 (.refl : BlowupTower X X) z)
        (restrict (lowerMask J 0 (.refl : BlowupTower X X) z) T)
          ⟨(p : Y),hzOwnT⟩ : ValTy (k+1)) : WithTop (ValTy (k+1)))) := native_zero_full_run (invFamily hn (k+1)) J T p hReg.1.2 hpLevel hRun hzOwnT
  have hProjected := projected_native_zero hn k J T p _ hNative
  have hCurve := actual_curve_core_value hn k (lowerMarkedM J 0 (.refl : BlowupTower X X) a) hL
    (restrict (lowerMask J 0 (.refl : BlowupTower X X) a) T) hTL p hp
  exact hProjected.trans (congrArg
    (fun value : ValTy (k+1) => toLex (0,(value : WithTop (ValTy (k+1)))))
    (hSameCore.symm.trans hCurve))

/-- The geometric ACTUAL native zero-count core cut DERIVES the lower
order cuts and actual fixed companion TEST by prefix induction. -/
theorem actual_initial_zero_count_native_core_cut_presentation
    (hn : 0<n) (k : ℕ) {X : CMfd.{u} n} (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (a : X)
    (ha : a∈(barMarked J).cosupp) (hLevel : level J (.refl : BlowupTower X X) a=0)
    (hNotSpecial : ¬IsSpecial J (.refl : BlowupTower X X) a) (q : ℕ) (hq : 1≤q) :
    let W := lowerMask J 0 (.refl : BlowupTower X X) a
    let L := lowerMarkedM J 0 (.refl : BlowupTower X X) a
    let V := NonmonomialOrderTail.ordMask L q
    let A := MarkedIdeal.pullback (Subtype.val : V → W) L
    let O := CompanionRebase.companionOf n (M := CMfd.of (n := n) V) A q
    IsInvDomain 1 L ∧ IsInvDomain 1 O ∧ IsMaximalOrderAlong O.N O.ideal O.d ∧
      ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (barMarked J) T →
        StageCentres (fun S C => ∀ c∈C,
          toLex (0, ((curveCoreValue k q : ValTy (k+1)) : WithTop (ValTy (k+1)))) ≤
            stepOneCoreInv hn k J S c) T →
          IsGeoTestTower O (restrict V (restrict W T)) ∧
          (geoTransformAlong O (restrict V (restrict W T))).cosupp=
            (Subtype.val : openPreimage (restrict W T) V → openPreimage T W) ⁻¹'
              {p | p∈(geoTransformAlong L (restrict W T)).cosupp ∧
                toLex (0, ((curveCoreValue k q : ValTy (k+1)) : WithTop (ValTy (k+1)))) ≤
                  stepOneCoreInv hn k J T p} := by
  dsimp only
  let W := lowerMask J 0 (.refl : BlowupTower X X) a
  let L := lowerMarkedM J 0 (.refl : BlowupTower X X) a
  obtain ⟨_hW,hL,hFuture⟩ := actual_initial_zero_count_curve_core_comparison
    hn k J hJ hMax a ha hLevel hNotSpecial
  obtain ⟨hO,hMaxO,_hReflTest,_hReflCos⟩ :=
    actual_curve_core_masked_whole_presentation (X := CMfd.of (n := n) W)
      hn k L hL q hq (.refl : BlowupTower (CMfd.of (n := n) W) _) trivial trivial
  refine ⟨hL,hO,hMaxO,?_⟩
  have hLowerCuts : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (barMarked J) T →
      StageCentres (fun S C => ∀ c∈C,
        toLex (0, ((curveCoreValue k q : ValTy (k+1)) : WithTop (ValTy (k+1)))) ≤
          stepOneCoreInv hn k J S c) T →
      StageCentres (fun S C => C⊆ordGe (geoTransformAlong L S) q) (restrict W T) := by
    intro Y T
    induction T with
    | refl => intro _ _; trivial
    | @step Y Z S C π hπ ih =>
      intro hT hCuts
      obtain ⟨hTL,_hCos,_hValue⟩ := hFuture (.step S C π hπ) hT
      obtain ⟨hSL,_hCosS,hValueS⟩ := hFuture S hT.1
      have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hL (restrict W S) hSL
      refine ⟨ih hT.1 hCuts.1,?_⟩
      intro p hp
      have hpCos : p∈(geoTransformAlong L (restrict W S)).cosupp := hTL.2.2.1 hp
      have hCut := hCuts.2 p hp
      rw [hValueS p hpCos,Prod.Lex.toLex_le_toLex] at hCut
      have hOrder : q≤nmOrd (geoTransformAlong L (restrict W S)) p := by
        simpa only [lt_self_iff_false,true_and,false_or,WithTop.coe_le_coe,
          (curveCoreValue_strictMono k).le_iff_le] using hCut
      exact (mem_ordGe_iff hCurrent.isWellFormed hCurrent.isNonzeroAlongAt
        ((geoTransformAlong L (restrict W S)).cosupp_subset_N hpCos) q).mpr hOrder
  intro Y T hT hCuts
  obtain ⟨hTL,_hCosL,hValues⟩ := hFuture T hT
  obtain ⟨_hO,_hMaxO,hTO,hCosO⟩ := actual_curve_core_masked_whole_presentation
    (X := CMfd.of (n := n) W) hn k L hL q hq (restrict W T) hTL (hLowerCuts T hT hCuts)
  refine ⟨hTO,?_⟩
  rw [hCosO]
  apply congrArg (fun S : Set (openPreimage T W) =>
    (Subtype.val : openPreimage (restrict W T) (NonmonomialOrderTail.ordMask L q) → openPreimage T W) ⁻¹' S)
  ext p
  constructor
  · rintro ⟨hp,hCore⟩
    refine ⟨hp,?_⟩
    rw [hValues p hp,Prod.Lex.toLex_le_toLex]
    rw [actual_curve_core_value hn k L hL (restrict W T) hTL p hp] at hCore
    exact Or.inr ⟨rfl,WithTop.coe_le_coe.mpr hCore⟩
  · rintro ⟨hp,hNative⟩
    refine ⟨hp,?_⟩
    rw [actual_curve_core_value hn k L hL (restrict W T) hTL p hp]
    rw [hValues p hp,Prod.Lex.toLex_le_toLex] at hNative
    simpa only [lt_self_iff_false,true_and,false_or,WithTop.coe_le_coe] using hNative

end
end Hironaka.HironakaActualCurveCoreContactComparison
