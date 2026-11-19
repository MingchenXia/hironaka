import Hironaka.Resolution.HironakaG8NativeRelativeSuccessor
import Hironaka.Resolution.HironakaG8NativeSimultaneousTransport
import Hironaka.Resolution.HironakaG8NativeNumericalOverlap
import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint
import Hironaka.Resolution.HironakaG8NativePrefixReplay
import Hironaka.Resolution.HironakaActualWholeAmbientHSSuperlevel
import Hironaka.Resolution.HironakaOriginalSelectedContactCosupport
import Hironaka.Resolution.HironakaG8OpenHoloEmbeddingComposition
import Hironaka.Resolution.HironakaG8SingularFootprintExtension
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Invariant.StepOneTangentChange
import Hironaka.Resolution.HironakaG8NativePrefixWindowRestriction
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
import Hironaka.Resolution.HironakaActualOriginalPowerTransform
import Hironaka.Resolution.HironakaG3CentresOverGenericFactor

/-! Finite clearing of a fixed native profile over a neighborhood
of a compact base task, with successive physical shrinkings. -/

set_option autoImplicit false
set_option maxHeartbeats 3200000

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeRelativeClearing

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec NormalCrossings HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  HironakaStageCenters MaxLocusLocal HironakaOriginalTerminalOverlapComparison
  HironakaG11PresLineState HironakaG11PresTowerState HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11InvCommonMark HironakaActualVanishingIntrinsicHSTransport
  HomogenizedGlueingTower HironakaG8NativePrefixReplay HironakaG8NativeRelativeSuccessor
  HironakaActualPowerBoundaryExponents HironakaActualWholeAmbientHSSuperlevel
  HironakaOriginalSelectedContactCosupport StepOneLowerDomain HironakaG8NativeNumericalOverlap
  HironakaG8SurfaceLimitEndpoint HironakaBaseChange HironakaG8OpenHoloEmbeddingComposition
  NormalCrossingsInvariance HironakaG8FiniteSingularTowerMerge HironakaEmbeddedBoundary
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaG8SingularFootprintExtension
  HironakaNormalCrossingsSeparationChoiceComparison MarkedIdealTowerTransport BlowupTowerIsomorphism
  StrictTransformComposition StepOneTangentChange HironakaG8NativePrefixWindowRestriction
  HironakaG1OriginalUnequalMarkCanonical HironakaSmoothSubmersionOriginalAmbientCanonical
  CanonicalCentres HironakaActualOriginalPowerTransform RestrictEmptyTower HironakaG3CentresOverGenericFactor

variable {n : ℕ} {X : CMfd.{0} n} {I : Type}

/-- The actual native records and one common positive powered mark on their
cover of the fixed profile. -/
structure NativeWindows (X : CMfd.{0} n) (I : Type) (W : Set X) (E : List (Set X))
    (H : ℕ → ℕ) (D : Set X) where
  openSet : I → Opens X
  record : ∀ i, MarkedIdeal n (CMfd.of (n := n) (openSet i))
  domain : ∀ i, IsInvDomain n (record i)
  native : ∀ i, NativeHSState (record i) ((Subtype.val : openSet i → X) ⁻¹' W) H
  boundary : ∀ i, (record i).E = E.map ((Subtype.val : openSet i → X) ⁻¹' ·)
  exponent : I → ℕ
  positive : ∀ i, 1 ≤ exponent i
  mark : ℕ
  commonMark : ∀ i, (powerMarked (record i) (exponent i)).d = mark
  covers : ∀ x ∈ D, ∃ i, x ∈ openSet i

namespace NativeWindows

variable {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
variable (A : NativeWindows X I W E H D)

/-- The actual common-mark representative for each native record. -/
abbrev powered (i : I) := powerMarked (A.record i) (A.exponent i)

theorem powered_domain (i : I) : IsInvDomain n (A.powered i) :=
  powerMarked_isInvDomain (A.record i) (A.domain i) (A.positive i)

/-- The new record is the literal pullback of the old one through both
open inclusions, retaining its weighted family and mark. -/
def restrictAmbient (O : Opens X) :
    NativeWindows (CMfd.of (n := n) O) I ((Subtype.val : O → X) ⁻¹' W)
      (E.map ((Subtype.val : O → X) ⁻¹' ·)) H ((Subtype.val : O → X) ⁻¹' D) where
  openSet i := nestedOpens O (O ⊓ A.openSet i)
  record i := MarkedIdeal.pullback
    (overlapBaseEquiv (n := n) (show O ⊓ A.openSet i ≤ O from inf_le_left)
      (show O ⊓ A.openSet i ≤ A.openSet i from inf_le_right))
    (MarkedIdeal.pullback (Subtype.val : nestedOpens (A.openSet i) (O ⊓ A.openSet i) → A.openSet i) (A.record i))
  domain i := InvDomainTowerAlong.isInvDomain_pullback _ (InvDomainTowerAlong.isInvDomain_pullback_val _ (A.domain i))
  native i := ((A.native i).restrict _).pullback _
  boundary i := by
    change (((A.record i).E.map _).map _) = (E.map _).map _
    rw [A.boundary i, List.map_map, List.map_map, List.map_map]
    rfl
  exponent := A.exponent
  positive := A.positive
  mark := A.mark
  commonMark i := A.commonMark i
  covers x hx := by
    obtain ⟨i, hi⟩ := A.covers x.val hx
    exact ⟨i, x.property, hi⟩

theorem restrictAmbient_powered (O : Opens X) (i : I) :
    (A.restrictAmbient O).powered i =
      MarkedIdeal.pullback
        (overlapBaseEquiv (n := n) (show O ⊓ A.openSet i ≤ O from inf_le_left)
          (show O ⊓ A.openSet i ≤ A.openSet i from inf_le_right))
        (MarkedIdeal.pullback (Subtype.val : nestedOpens (A.openSet i) (O ⊓ A.openSet i) → A.openSet i) (A.powered i)) := by
  let V := nestedOpens (A.openSet i) (O ⊓ A.openSet i)
  let e := overlapBaseEquiv (n := n) (show O ⊓ A.openSet i ≤ O from inf_le_left)
    (show O ⊓ A.openSet i ≤ A.openSet i from inf_le_right)
  let Q := MarkedIdeal.pullback (Subtype.val : V → A.openSet i) (A.record i)
  have hQ := InvDomainTowerAlong.isInvDomain_pullback_val V (A.domain i)
  change powerMarked (MarkedIdeal.pullback e Q) (A.exponent i) =
    MarkedIdeal.pullback e (MarkedIdeal.pullback (Subtype.val : V → A.openSet i) (A.powered i))
  have hLocal := pullback_powerMarked (X := CMfd.of (n := n) (A.openSet i)) (X' := CMfd.of (n := n) V)
    contMDiff_subtype_val (A.record i) (A.domain i).isWellFormed.isCoherent (A.exponent i)
  have hAcross := pullback_powerMarked (X := CMfd.of (n := n) V)
    (X' := CMfd.of (n := n) (nestedOpens O (O ⊓ A.openSet i))) e.contMDiff Q hQ.isWellFormed.isCoherent (A.exponent i)
  exact hAcross.symm.trans (congrArg (MarkedIdeal.pullback e) hLocal.symm)

end NativeWindows

section Replay

variable {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
variable {Y : CMfd.{0} n} {Λ : Type} [LinearOrder Λ]

/-- The actual points over the original profile whose current profile is
still at least the original one pointwise. -/
def activeSupport (T : BlowupTower X Y) (W D : Set X) (H : ℕ → ℕ) : Set Y :=
  T.proj ⁻¹' D ∩ actualWholeAmbientHSSuperlevel (vanishingIdeal (n := n) (strictTransform n T.proj W)) H

theorem isClosed_activeSupport (T : BlowupTower X Y)
    (hW : IsComplexAnalyticSubset (n := n) W) (hD : IsClosed D) :
    IsClosed (activeSupport T W D H) := by
  have hA := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
  exact (hD.preimage (HironakaLocalPrincipalization.isProperMap_proj T).continuous).inter
    (isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel _
      (CartanIrreducible.cartanCoherence _ hA) H).isClosed

local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)

/-- Actual replay of the same native windows, including values on overlaps
and the exact current support over the original profile. -/
structure ActiveWindows (A : NativeWindows X I W E H D) (T : BlowupTower X Y)
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ) : Prop where
  boundary : ∀ i, (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).E =
    (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).E.map
      ((Subtype.val : openPreimage T (A.openSet i) → Y) ⁻¹' ·)
  support : ∀ i (y : openPreimage T (A.openSet i)),
    y ∈ (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp ↔
      y.val ∈ activeSupport T W D H
  upper : ∀ i (y : openPreimage T (A.openSet i)) ℓ,
    HS[strictTransform n T.proj W] y.val ℓ ≤ H ℓ
  currentCut : ∀ i (y : openPreimage T (A.openSet i)),
    y ∈ (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp →
      y.val ∈ singularSet (n := n) (strictTransform n T.proj W) ∧
        ∀ ℓ, HS[strictTransform n T.proj W] y.val ℓ = H ℓ
  overlap : ∀ i j (y : Y) (hi : y ∈ openPreimage T (A.openSet i)) (hj : y ∈ openPreimage T (A.openSet j)),
    (⟨y, hi⟩ : openPreimage T (A.openSet i)) ∈
      (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp →
    (⟨y, hj⟩ : openPreimage T (A.openSet j)) ∈
      (geoTransformAlong (A.powered j) (restrict (A.openSet j) T)).cosupp ∧
      R.inv (A.powered i) (restrict (A.openSet i) T) ⟨y, hi⟩ =
        R.inv (A.powered j) (restrict (A.openSet j) T) ⟨y, hj⟩

theorem nativeWindows_active_replay (hn : 0 < n)
    (R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n Λ)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (A : NativeWindows X I W E H D) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
    (hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T)
    (hCan : ∀ i, IsCanonical (A.powered i) (R.toResolutionInvariant.inv (A.powered i))
      (restrict (A.openSet i) T)) :
    ActiveWindows A T R.toResolutionInvariant := by
  let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
  let Wt := strictTransform n T.proj W
  let V (i : I) : Opens Y := openPreimage T (A.openSet i)
  let S (i : I) := restrict (A.openSet i) T
  let Q (i : I) := A.powered i
  let Q' (i : I) := geoTransformAlong (Q i) (S i)
  let R₀ := R.toResolutionInvariant
  have hM : M.IsWellFormed := ⟨isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW, hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hA : IsComplexAnalyticSubset (n := n) Wt :=
    HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
  have hStrict : strictAlong T W = Wt := intrinsic_strictAlong_eq W hW T hStage
  have hQ (i : I) : IsInvDomain n (Q i) := A.powered_domain i
  have hQT (i : I) : IsGeoTestTower (Q i) (S i) :=
    R₀.isInvValue.isGeoTestTower_of_isCanonical (hQ i) (S i) (hCan i)
  have hLocal (i : I) : (Q' i).E = (geoTransformAlong M T).E.map ((Subtype.val : V i → Y) ⁻¹' ·) ∧
      HSTowerState (Q' i) ((Subtype.val : V i → Y) ⁻¹' Wt) H := by
    rw [← hStrict]
    exact powered_native_state_after_actual_restriction M hM T hT W H (A.openSet i) (A.record i)
      (A.domain i) (A.native i) (A.boundary i) (A.exponent i) (A.positive i) (hQT i)
  have hBase (i : I) : (Q i).cosupp = (Subtype.val : A.openSet i → X) ⁻¹' D := by
    rw [show (Q i).cosupp = (A.record i).cosupp from powerMarked_cosupp (A.record i) (A.domain i) (A.positive i),
      (A.native i).cosupp_eq]
    ext x
    simpa only [mem_ofPred_eq, mem_preimage, hilbertSamuelAt_vanishing_actual_open_any] using
      (Set.ext_iff.mp hExact x.val).symm
  have hProj (i : I) (y : V i) (hy : y ∈ (Q' i).cosupp) : T.proj y.val ∈ D := by
    have h := proj_mem_cosupp_of_mem_cosupp (hQ i).isWellFormed.isClosedSubmanifold_N
      (hQ i).isWellFormed.isCoherent (S i) (hQT i) hy
    rw [hBase i] at h
    change ((restrict (A.openSet i) T).proj y).val ∈ D at h
    simpa only [proj_restrict] using h
  have hStateAt (i : I) := (hLocal i).2 (.refl : BlowupTower (CMfd.of (n := n) (V i)) _) trivial
  have hUpper (i : I) (y : V i) (ℓ : ℕ) : hilbertSamuelAt (vanishingIdeal (n := n) Wt) y.val ℓ ≤ H ℓ :=
    (hilbertSamuelAt_vanishing_actual_open_any (n := n) (V i) Wt y ℓ).symm.le.trans ((hStateAt i).2.2.1 y ℓ)
  have hCut (i : I) (y : V i) : y ∈ (Q' i).cosupp ↔
      ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) Wt) y.val ℓ = H ℓ := by
    simpa only [geoTransformAlong_refl, strictAlong_refl, hilbertSamuelAt_vanishing_actual_open_any] using (hStateAt i).2.2.2.1 y
  have hSing (i : I) (y : V i) (hy : y ∈ (Q' i).cosupp) : y.val ∈ singularSet (n := n) Wt := by
    have h := (hStateAt i).2.2.2.2 hy
    change y ∈ singularSet (n := n) ((Subtype.val : V i → Y) ⁻¹' Wt) at h
    rw [HironakaResolutionSpaceLocal.singularSet_preimage_val] at h
    exact h
  refine ⟨fun i => (hLocal i).1, ?_, hUpper, fun i y hy => ⟨hSing i y hy, (hCut i y).mp hy⟩, ?_⟩
  · intro i y
    change y ∈ (Q' i).cosupp ↔ y.val ∈ activeSupport T W D H
    exact ⟨fun hy => ⟨hProj i y hy, fun ℓ => ((hCut i y).mp hy ℓ).ge⟩,
      fun hy => (hCut i y).mpr fun ℓ => le_antisymm (hUpper i y ℓ) (hy.2 ℓ)⟩
  · intro i j y hi hj hy
    refine native_window_values_agree_along hn R (A.openSet i) (A.openSet j) (A.record i) (A.record j)
      (A.domain i) (A.domain j) W H (A.native i) (A.native j) E (A.boundary i) (A.boundary j)
      (A.exponent i) (A.exponent j) (A.positive i) (A.positive j)
      ((A.commonMark i).trans (A.commonMark j).symm) ?_ T (hCan i) (hCan j) hi hj hy
    intro B hB x hx hxB
    apply hNot B hB x.val ?_ hxB
    have hxQ : x ∈ (Q i).cosupp := (powerMarked_cosupp (A.record i) (A.domain i) (A.positive i)).symm ▸ hx
    rw [hBase i] at hxQ
    exact hxQ

end Replay


section TerminalWindows

variable {B Y Z : CMfd.{0} n} {Λ : Type} [LinearOrder Λ]
variable {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
variable (A : NativeWindows X I W E H D)


/-- The actual literal restrictions resolve all inherited powered native
windows once the retained base open avoids the image of the active support. -/
theorem NativeWindows.terminal_on_open_of_disjoint
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ) (T : BlowupTower X Y)
    (hReplay : ActiveWindows A T R)
    (hCan : ∀ i, IsCanonical (A.powered i) (R.inv (A.powered i)) (restrict (A.openSet i) T))
    (O : Opens X) (hOff : Disjoint (O : Set X) (T.proj '' activeSupport T W D H))
    (i : I) :
    let A₀ := A.restrictAmbient O
    let S := restrict (A₀.openSet i) (restrict O T)
    IsCanonical (A₀.powered i) (R.inv (A₀.powered i)) S ∧
      IsGeoResolution (A₀.powered i) S := by
  dsimp only
  rw [A.restrictAmbient_powered O i]
  obtain ⟨hDom,hCan₀,f,hPoint,hCos,_,_⟩ := native_prefix_values_on_shrunk_ambient
    R (A.openSet i) O (A.powered i) (A.powered_domain i) T (hCan i)
  refine ⟨hCan₀, R.isInvValue.isGeoTestTower_of_isCanonical hDom _ hCan₀,
    Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro z hz
  have hz' := (Set.ext_iff.mp hCos z).mp hz
  have hy := (hReplay.support i (f z)).mp hz'
  have hBase : T.proj (f z).val ∈ O := by
    exact (hPoint z).symm ▸ (show T.proj z.val.val ∈ O from z.val.property)
  exact Set.disjoint_left.mp hOff hBase ⟨(f z).val,hy,rfl⟩

namespace NativeWindows

variable (φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)

/-- Pull back a literal native window along the ambient biholomorphism. -/
def preimageOpen (i : I) : Opens B :=
  ⟨φ ⁻¹' (A.openSet i : Set X), (A.openSet i).isOpen.preimage φ.continuous⟩

/-- Exact restriction of the ambient biholomorphism on each native window. -/
def windowEquiv (i : I) :
    CMfd.of (n := n) (A.preimageOpen φ i) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (A.openSet i) :=
  diffeoOpens φ (A.preimageOpen φ i) (A.openSet i) (fun _ => Iff.rfl)

/-- Carry the raw records, restricted full boundary, and common powers
through an actual biholomorphic change of ambient base. -/
def transportBase : NativeWindows B I (φ ⁻¹' W) (E.map (φ ⁻¹' ·)) H (φ ⁻¹' D) where
  openSet := A.preimageOpen φ
  record i := MarkedIdeal.pullback (A.windowEquiv φ i) (A.record i)
  domain i := InvDomainTowerAlong.isInvDomain_pullback _ (A.domain i)
  native i := (A.native i).pullback (A.windowEquiv φ i)
  boundary i := by
    change ((A.record i).E.map _)= (E.map _).map _
    rw [A.boundary i, List.map_map, List.map_map]
    rfl
  exponent := A.exponent
  positive := A.positive
  mark := A.mark
  commonMark i := A.commonMark i
  covers x hx := A.covers (φ x) hx

theorem transportBase_powered (i : I) :
    (A.transportBase φ).powered i = MarkedIdeal.pullback (A.windowEquiv φ i) (A.powered i) :=
  (pullback_powerMarked (A.windowEquiv φ i).contMDiff (A.record i)
    (A.domain i).isWellFormed.isCoherent (A.exponent i)).symm

/-- The actual same stagewise ambient isomorphism transports all terminal
native certificates on literal restrictions, with every empty position. -/
theorem terminal_transportBase (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ) {T' : BlowupTower B Z} {T : BlowupTower X Y}
    {χ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso φ T' T χ)
    (hEnd : ∀ i, IsCanonical (A.powered i) (R.inv (A.powered i)) (restrict (A.openSet i) T) ∧
      IsGeoResolution (A.powered i) (restrict (A.openSet i) T))
    (i : I) :
    let A' := A.transportBase φ
    let S := restrict (A'.openSet i) T'
    IsCanonical (A'.powered i) (R.inv (A'.powered i)) S ∧ IsGeoResolution (A'.powered i) S := by
  let hU : ∀ x : B, x ∈ A.preimageOpen φ i ↔ φ x ∈ A.openSet i := fun _ => Iff.rfl
  have hFin := isTowerIso_restrictOpens hU hIso (isTowerIso_mem_openPreimage_iff hIso hU)
  dsimp only
  rw [A.transportBase_powered φ i]
  have hD := A.powered_domain i
  exact ⟨Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R hD (A.windowEquiv φ i) hFin
      (hEnd i).1,
    (IsTowerIso.isGeoResolution_iff (A.windowEquiv φ i) hD.isWellFormed.isClosedSubmanifold_N
      hD.isWellFormed.isCoherent hFin).mpr (hEnd i).2⟩

/-- Re-use the same simultaneous maximum certificate on the actual
restricted prefix, with the inherited common-mark records. -/
theorem simultaneous_restrictAmbient
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ)
    (T : BlowupTower X Y)
    (hCan : ∀ i, IsCanonical (A.powered i) (R.inv (A.powered i)) (restrict (A.openSet i) T))
    (hSync : HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages R A.openSet A.powered T)
    (O : Opens X) :
    HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages R (A.restrictAmbient O).openSet
      (A.restrictAmbient O).powered (restrict O T) := by
  open HironakaG8NativeSimultaneousTransport in
  have hRec : (A.restrictAmbient O).powered =
      (fun i => shrunkRecord (n := n) O (A.openSet i) (A.powered i)) :=
    funext (A.restrictAmbient_powered O)
  rw [hRec]
  exact HironakaG8NativeSimultaneousTransport.native_simultaneous_stages_restrictAmbient
    R A.openSet A.powered A.powered_domain O T hCan hSync

/-- All synchronized stages survive an actual uncompressed tower
isomorphism, with their full original clock and boundary slots. -/
theorem simultaneous_transportBase (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ)
    {T' : BlowupTower B Z} {T : BlowupTower X Y}
    {χ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso φ T' T χ)
    (hCan : ∀ i, IsCanonical (A.powered i) (R.inv (A.powered i)) (restrict (A.openSet i) T))
    (hSync : HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages R A.openSet A.powered T) :
    HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages R (A.transportBase φ).openSet
      (A.transportBase φ).powered T' := by
  open HironakaG8NativeSimultaneousTransport in
  have hRec : (A.transportBase φ).powered =
      (fun i => transportedRecord φ (A.openSet i) (A.powered i)) :=
    funext (A.transportBase_powered φ)
  rw [hRec]
  exact HironakaG8NativeSimultaneousTransport.native_simultaneous_stages_of_isTowerIso
    φ R A.openSet A.powered A.powered_domain hIso hCan hSync

end NativeWindows


/-- A terminal native atlas consists of the actual retained windows and
the certified canonical resolutions on the corresponding literal
restrictions of one common ambient tower. -/
def TerminalWindows (I : Type) (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ)
    (T : BlowupTower X Y) (W D : Set X) (E : List (Set X)) (H : ℕ → ℕ) : Prop :=
  ∃ S : NativeWindows X I W E H D,
    ∀ i, IsCanonical (S.powered i) (R.inv (S.powered i)) (restrict (S.openSet i) T) ∧
      IsGeoResolution (S.powered i) (restrict (S.openSet i) T)

/-- Terminal native records with the option to retain the simultaneous
maximum certificate from every literal ambient stage. -/
def TerminalWindowsRemembering (keep : Prop) (I : Type)
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ)
    (T : BlowupTower X Y) (W D : Set X) (E : List (Set X)) (H : ℕ → ℕ) : Prop :=
  ∃ S : NativeWindows X I W E H D,
    (∀ i, IsCanonical (S.powered i) (R.inv (S.powered i)) (restrict (S.openSet i) T) ∧
      IsGeoResolution (S.powered i) (restrict (S.openSet i) T)) ∧
    (keep → HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages R S.openSet S.powered T)


end TerminalWindows

section Induction

variable {Λ : Type} [LinearOrder Λ] [WellFoundedLT Λ]

local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)
local notation "original[" W "; " E "]" => MarkedIdeal.mk (n := n) univ E (vanishingIdeal (n := n) W) 1

/-- A terminal certificate attached to one finite physical tower. -/
def TerminalCondition (n : ℕ) :=
  ∀ {X Y : CMfd.{0} n}, BlowupTower X Y → Set X → Set X → List (Set X) → (ℕ → ℕ) → Prop

/-- One finite physical tower over an open-embedded neighborhood of the
compact base task, retaining the same original boundary and clearing
the chosen profile over the entire preimage of the indicated base level. -/
def ClearedOverWith (term : TerminalCondition n) (X : CMfd.{0} n) (W D K : Set X) (E : List (Set X)) (H : ℕ → ℕ) : Prop :=
  ∃ (B : CMfd.{0} n) (j : B → X), IsOpenHoloEmbedding n j ∧ K ⊆ range j ∧
    ∃ (Y : CMfd.{0} n) (T : BlowupTower B Y),
      IsGeoTestTower original[j ⁻¹' W; E.map (j ⁻¹' ·)] T ∧
      StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj (j ⁻¹' W))) T ∧
      (∀ z ℓ, HS[strictTransform n T.proj (j ⁻¹' W)] z ℓ ≤ HS[j ⁻¹' W] (T.proj z) ℓ) ∧
      (∀ z ∈ T.proj ⁻¹' (j ⁻¹' D), toLex (HS[strictTransform n T.proj (j ⁻¹' W)] z) < toLex H) ∧
      CentresOver (j ⁻¹' D) T ∧ term T (j ⁻¹' W) (j ⁻¹' D) (E.map (j ⁻¹' ·)) H

abbrev ClearedOver (I : Type) (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ)
    (X : CMfd.{0} n) (W D K : Set X) (E : List (Set X)) (H : ℕ → ℕ) : Prop :=
  ClearedOverWith (fun T W D E H => TerminalWindows I R T W D E H) X W D K E H

abbrev ClearedOverRemembering (keep : Prop) (I : Type)
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ)
    (X : CMfd.{0} n) (W D K : Set X) (E : List (Set X)) (H : ℕ → ℕ) : Prop :=
  ClearedOverWith (fun T W D E H => TerminalWindowsRemembering keep I R T W D E H) X W D K E H


private theorem clearedOverWith_of_restrict {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {term : TerminalCondition n} (O : Opens X) (hKO : K ⊆ O)
    (h : ClearedOverWith term (CMfd.of (n := n) O) ((Subtype.val : O → X) ⁻¹' W)
      ((Subtype.val : O → X) ⁻¹' D) ((Subtype.val : O → X) ⁻¹' K)
      (E.map ((Subtype.val : O → X) ⁻¹' ·)) H) :
    ClearedOverWith term X W D K E H := by
  obtain ⟨B, j, hj, hK, Y, T, hT, hStage, hBound, hDrop, hOver, hEnd⟩ := h
  refine ⟨B, (Subtype.val : O → X) ∘ j, isOpenHoloEmbedding_comp (isOpenHoloEmbedding_val O) hj,
    ?_, Y, T, ?_, hStage, hBound, hDrop, hOver, ?_⟩
  · intro x hx
    obtain ⟨b, hb⟩ := hK (show (⟨x,hKO hx⟩ : O) ∈ (Subtype.val : O → X) ⁻¹' K from hx)
    exact ⟨b, congrArg Subtype.val hb⟩
  · rw [List.map_map] at hT
    exact hT
  · rw [List.map_map] at hEnd
    exact hEnd

omit [WellFoundedLT Λ] in
theorem ClearedOver.of_restrict {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ) (O : Opens X) (hKO : K ⊆ O)
    (h : ClearedOver I R (CMfd.of (n := n) O) ((Subtype.val : O → X) ⁻¹' W)
      ((Subtype.val : O → X) ⁻¹' D) ((Subtype.val : O → X) ⁻¹' K)
      (E.map ((Subtype.val : O → X) ⁻¹' ·)) H) :
    ClearedOver I R X W D K E H :=
  clearedOverWith_of_restrict O hKO h

omit [WellFoundedLT Λ] in
theorem ClearedOverRemembering.of_restrict {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {keep : Prop} (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ) (O : Opens X)
    (hKO : K ⊆ O)
    (h : ClearedOverRemembering keep I R (CMfd.of (n := n) O) ((Subtype.val : O → X) ⁻¹' W)
      ((Subtype.val : O → X) ⁻¹' D) ((Subtype.val : O → X) ⁻¹' K)
      (E.map ((Subtype.val : O → X) ⁻¹' ·)) H) :
    ClearedOverRemembering keep I R X W D K E H :=
  clearedOverWith_of_restrict O hKO h

omit [WellFoundedLT Λ] in
theorem ClearedOverRemembering.forget {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {keep : Prop} {R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ}
    (h : ClearedOverRemembering keep I R X W D K E H) : ClearedOver I R X W D K E H := by
  obtain ⟨B,j,hj,hK,Y,T,hT,hStage,hBound,hDrop,hOver,A,hEnd,_⟩ := h
  exact ⟨B,j,hj,hK,Y,T,hT,hStage,hBound,hDrop,hOver,A,hEnd⟩


private theorem hs_nonincrease_restrict {W : Set X} {Y : CMfd.{0} n}
    (T : BlowupTower X Y) (O : Opens X)
    (hBound : ∀ y ℓ, HS[strictTransform n T.proj W] y ℓ ≤ HS[W] (T.proj y) ℓ) :
    ∀ y ℓ, HS[strictTransform n (restrict O T).proj ((Subtype.val : O → X) ⁻¹' W)] y ℓ ≤
      HS[(Subtype.val : O → X) ⁻¹' W] ((restrict O T).proj y) ℓ := by
  intro y ℓ
  rw [strictTransform_restricted_tower O T W]
  rw [hilbertSamuelAt_vanishing_actual_open_any (openPreimage T O) _ y ℓ,
    hilbertSamuelAt_vanishing_actual_open_any O W ((restrict O T).proj y) ℓ, proj_restrict]
  exact hBound y.val ℓ

omit [WellFoundedLT Λ] in
private theorem clearedOverRemembering_of_no_active {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (keep : Prop) (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hT : IsGeoTestTower original[W;E] T)
    (hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T)
    (hOver : CentresOver D T)
    (hBound : ∀ y ℓ, HS[strictTransform n T.proj W] y ℓ ≤ HS[W] (T.proj y) ℓ)
    (A : NativeWindows X I W E H D)
    (hR : ActiveWindows A T R)
    (hCan : ∀ i, IsCanonical (A.powered i) (R.inv (A.powered i)) (restrict (A.openSet i) T))
    (hSync : keep → HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages R A.openSet A.powered T)
    (hF : IsClosed (activeSupport T W D H)) (hNe : ¬ (activeSupport T W D H ∩ T.proj ⁻¹' K).Nonempty) :
    ClearedOverRemembering keep I R X W D K E H := by
  let O : Opens X := ⟨(T.proj '' activeSupport T W D H)ᶜ,
    ((HironakaLocalPrincipalization.isProperMap_proj T).isClosedMap _ hF).isOpen_compl⟩
  have hK : K ⊆ range (Subtype.val : O → X) := by
    intro x hx
    have hO : x ∈ O := by
      rintro ⟨y, hy, rfl⟩
      exact hNe ⟨y,hy,hx⟩
    exact ⟨⟨x,hO⟩,rfl⟩
  have hM : original[W;E].IsWellFormed := ⟨isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW, hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  refine ⟨CMfd.of (n := n) O, Subtype.val, isOpenHoloEmbedding_val O, hK, _, restrict O T, ?_,
    singular_stages_restrict W O T hStage, hs_nonincrease_restrict T O hBound, ?_, centresOver_restrict O D T hOver, ?_⟩
  · rw [← pullback_val_mk_vanishingIdeal O E W]
    exact MarkedIdealRestrictOpen.isGeoTestTower_restrict O
      hM.isClosedSubmanifold_N hM.isCoherent T hT
  · intro z hz
    change ((restrict O T).proj z).val ∈ D at hz
    rw [proj_restrict] at hz
    obtain ⟨i,hi⟩ := A.covers (T.proj z.val) hz
    have hLe : ∀ ℓ, HS[strictTransform n T.proj W] z.val ℓ ≤ H ℓ :=
      hR.upper i ⟨z.val,hi⟩
    rw [strictTransform_restricted_tower O T W]
    have hHS : HS[(Subtype.val : openPreimage T O → Y) ⁻¹' strictTransform n T.proj W] z =
        HS[strictTransform n T.proj W] z.val :=
      funext (hilbertSamuelAt_vanishing_actual_open_any (openPreimage T O) _ z)
    rw [hHS]
    apply lt_of_le_of_ne (Pi.toLex_monotone hLe)
    intro hEq
    exact z.property ⟨z.val, ⟨hz, fun ℓ => (congrFun (congrArg ofLex hEq) ℓ).ge⟩, rfl⟩
  · have hOff : Disjoint (O : Set X) (T.proj '' activeSupport T W D H) :=
      Set.disjoint_left.mpr fun _ hAvoid hHit => hAvoid hHit
    exact ⟨A.restrictAmbient O, fun i => A.terminal_on_open_of_disjoint R T hR hCan O hOff i,
      fun hKeep => A.simultaneous_restrictAmbient R T hCan (hSync hKeep) O⟩

/-- Strict descent of the maximum over the fixed compact task produces
one actual finite tower on an open neighborhood of that task. Every
recursive prefix is the same restricted ambient prefix with one actual
singular blowup appended and retains every original boundary slot. -/
theorem exists_finite_native_clearing_along_remembering (hn : 0 < n) (keep : Prop)
    (R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n Λ)
    (H : ℕ → ℕ) (μ : WithTop Λ) :
    ∀ {X : CMfd.{0} n} {W D K : Set X} {E : List (Set X)}
      (_hW : IsComplexAnalyticSubset (n := n) W) (_hE : IsSNCDivisor n E)
      (_hD : IsClosed D) (_hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
      (_hK : IsCompact K)
      (_hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
      (A : NativeWindows X I W E H D) {Y : CMfd.{0} n} (T : BlowupTower X Y)
      (_hT : IsGeoTestTower original[W;E] T)
      (_hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T)
      (_hOver : CentresOver D T)
      (_hBound : ∀ y ℓ, HS[strictTransform n T.proj W] y ℓ ≤ HS[W] (T.proj y) ℓ)
      (_hCan : ∀ i, IsCanonical (A.powered i) (R.toResolutionInvariant.inv (A.powered i))
        (restrict (A.openSet i) T)),
      (keep → HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages R.toResolutionInvariant
        A.openSet A.powered T) →
      (∀ i (y : openPreimage T (A.openSet i)),
        y ∈ (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp →
        T.proj y.val ∈ K →
        (R.toResolutionInvariant.inv (A.powered i) (restrict (A.openSet i) T) y : WithTop Λ) < μ) →
      ClearedOverRemembering keep I R.toResolutionInvariant X W D K E H := by
  classical
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
    intro X W D K E hW hE hD hExact hK hNot A Y T hT hStage hOver hBound hCan hSync hRank
    let F := activeSupport T W D H
    have hF : IsClosed F := isClosed_activeSupport T hW hD
    have hR := nativeWindows_active_replay hn R hW hE hExact hNot A T hT hStage hCan
    by_cases hNe : (F ∩ T.proj ⁻¹' K).Nonempty
    · have hCover : ∀ y ∈ F, ∃ (i : I) (hy : y ∈ openPreimage T (A.openSet i)),
          (⟨y, hy⟩ : openPreimage T (A.openSet i)) ∈ (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp := by
        intro y hy
        obtain ⟨i,hi⟩ := A.covers (T.proj y) hy.1
        exact ⟨i,hi,(hR.support i ⟨y,hi⟩).mpr hy⟩
      obtain ⟨m,O,hKO,⟨i,y,hy,hyK,hym⟩,hNext⟩ := exists_relative_native_successor_with_cut
        R.toResolutionInvariant hW E hE T hT hStage A.openSet F hF hK hNe A.powered A.powered_domain
        hCan hR.boundary H hR.currentCut hCover (fun i y => (hR.support i y).mp) hR.overlap
      have hm : (m : WithTop Λ) < μ := by
        rw [← hym]
        exact hRank i y hy hyK
      dsimp only at hNext
      obtain ⟨C,Z,π,hπ,_,hWhere,_,hS,hStageS,hLocal,hStepBound,hCut⟩ := hNext
      let A' := A.restrictAmbient O
      let W' := (Subtype.val : O → X) ⁻¹' W
      let E' := E.map ((Subtype.val : O → X) ⁻¹' ·)
      let D' := (Subtype.val : O → X) ⁻¹' D
      let K' := (Subtype.val : O → X) ⁻¹' K
      let S := BlowupTower.step (restrict O T) C π hπ
      have hW' : IsComplexAnalyticSubset (n := n) W' :=
        AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hW
      have hE' : IsSNCDivisor n E' :=
        isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
      have hD' : IsClosed D' := hD.preimage continuous_subtype_val
      have hExact' : D' = {x | ∀ ℓ, HS[W'] x ℓ = H ℓ} := by
        change (Subtype.val : O → X) ⁻¹' D = _
        rw [hExact]
        ext x
        have hHS := funext (hilbertSamuelAt_vanishing_actual_open_any (n := n) O W x)
        change (∀ ℓ, HS[W] x.val ℓ = H ℓ) ↔ (∀ ℓ, HS[(Subtype.val : O → X) ⁻¹' W] x ℓ = H ℓ)
        rw [hHS]
      have hK' : IsCompact K' :=
        (Topology.IsInducing.subtypeVal.isCompact_preimage_iff (fun x hx => ⟨⟨x,hKO hx⟩,rfl⟩)).mpr hK
      have hNot' : ∀ B ∈ E', ∀ x ∈ D', x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W' := by
        intro B hB x hx hxB hBnear
        obtain ⟨B₀,hB₀,rfl⟩ := List.mem_map.mp hB
        apply hNot B₀ hB₀ x.val hx hxB
        rw [← O.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x, Filter.eventually_map]
        exact hBnear
      have hCan' (i : I) : IsCanonical (A'.powered i) (R.toResolutionInvariant.inv (A'.powered i))
          (restrict (A'.openSet i) S) := by
        change IsCanonical ((A.restrictAmbient O).powered i)
          (R.toResolutionInvariant.inv ((A.restrictAmbient O).powered i)) (restrict (A'.openSet i) S)
        rw [A.restrictAmbient_powered O i]
        exact (hLocal i).2.1
      have hBound' : ∀ y ℓ, HS[strictTransform n S.proj W'] y ℓ ≤ HS[W'] (S.proj y) ℓ := by
        intro z ℓ
        dsimp only [S]
        rw [BlowupTower.proj_step, strictTransform_comp (restrict O T).contMDiff_proj hπ.contMDiff W']
        exact (hStepBound z ℓ).trans (hs_nonincrease_restrict T O hBound (π z) ℓ)
      have hOver' : CentresOver D' S := by
        refine ⟨centresOver_restrict O D T hOver, ?_⟩
        intro z hz
        change ((restrict O T).proj z).val ∈ D
        rw [proj_restrict]
        exact (hWhere hz).1
      have hSync' : keep → HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages
          R.toResolutionInvariant A'.openSet A'.powered S := by
        intro hKeep
        refine ⟨A.simultaneous_restrictAmbient R.toResolutionInvariant T hCan (hSync hKeep) O,
          Or.inr ⟨m,?_⟩⟩
        open HironakaG8NativeSimultaneousTransport in
        have hRecords : A'.powered =
            (fun i => shrunkRecord (n := n) O (A.openSet i) (A.powered i)) :=
          funext (A.restrictAmbient_powered O)
        rw [hRecords]
        exact hCut
      apply ClearedOverRemembering.of_restrict R.toResolutionInvariant O hKO
      refine IH (m : WithTop Λ) hm hW' hE' hD' hExact' hK' hNot' A' S hS hStageS hOver' hBound' hCan' hSync' ?_
      intro i z hz _
      change z ∈ (geoTransformAlong ((A.restrictAmbient O).powered i) (restrict (A'.openSet i) S)).cosupp at hz
      change (R.toResolutionInvariant.inv ((A.restrictAmbient O).powered i) (restrict (A'.openSet i) S) z :
        WithTop Λ) < (m : WithTop Λ)
      rw [A.restrictAmbient_powered O i] at hz ⊢
      exact WithTop.coe_lt_coe.mpr ((hLocal i).2.2 z hz)
    · exact clearedOverRemembering_of_no_active keep R.toResolutionInvariant T hW hE hT hStage hOver hBound A hR hCan hSync hF hNe

/-- The compatible interface for an arbitrary existing canonical prefix. -/
theorem exists_finite_native_clearing_along (hn : 0 < n)
    (R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n Λ)
    (H : ℕ → ℕ) (μ : WithTop Λ) :
    ∀ {X : CMfd.{0} n} {W D K : Set X} {E : List (Set X)}
      (_hW : IsComplexAnalyticSubset (n := n) W) (_hE : IsSNCDivisor n E)
      (_hD : IsClosed D) (_hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
      (_hK : IsCompact K)
      (_hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
      (A : NativeWindows X I W E H D) {Y : CMfd.{0} n} (T : BlowupTower X Y)
      (_hT : IsGeoTestTower original[W;E] T)
      (_hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T)
      (_hOver : CentresOver D T)
      (_hBound : ∀ y ℓ, HS[strictTransform n T.proj W] y ℓ ≤ HS[W] (T.proj y) ℓ)
      (_hCan : ∀ i, IsCanonical (A.powered i) (R.toResolutionInvariant.inv (A.powered i))
        (restrict (A.openSet i) T)),
      (∀ i (y : openPreimage T (A.openSet i)),
        y ∈ (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp →
        T.proj y.val ∈ K →
        (R.toResolutionInvariant.inv (A.powered i) (restrict (A.openSet i) T) y : WithTop Λ) < μ) →
      ClearedOver I R.toResolutionInvariant X W D K E H := by
  intro X W D K E hW hE hD hExact hK hNot A Y T hT hStage hOver hBound hCan hRank
  exact (exists_finite_native_clearing_along_remembering hn False R H μ hW hE hD hExact hK hNot
    A T hT hStage hOver hBound hCan False.elim hRank).forget

/-- Start finite relative clearing with the empty literal prefix. -/
theorem exists_finite_native_clearing_remembering (hn : 0 < n)
    (R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n Λ)
    {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hD : IsClosed D) (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ}) (hK : IsCompact K)
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (A : NativeWindows X I W E H D) :
    ClearedOverRemembering True I R.toResolutionInvariant X W D K E H := by
  apply exists_finite_native_clearing_along_remembering hn True R H ⊤ hW hE hD hExact hK hNot A .refl trivial trivial trivial
  · intro z ℓ
    simpa only [BlowupTower.proj_refl, strictTransform_id hW.isClosed, id_eq] using (le_rfl : HS[W] z ℓ ≤ HS[W] z ℓ)
  · exact fun _ => trivial
  · exact fun _ => trivial
  · exact fun _ _ _ _ => WithTop.coe_lt_top _

/-- Start finite relative clearing with the empty literal prefix. -/
theorem exists_finite_native_clearing (hn : 0 < n)
    (R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n Λ)
    {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hD : IsClosed D) (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ}) (hK : IsCompact K)
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (A : NativeWindows X I W E H D) :
    ClearedOver I R.toResolutionInvariant X W D K E H :=
  (exists_finite_native_clearing_remembering hn R hW hE hD hExact hK hNot A).forget

private theorem clearedOverWith_exists_literal_open {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {term : TerminalCondition n} (hTransport : ∀ {A B Y Y' : CMfd.{0} n}
      (φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
      {T : BlowupTower A Y} {T' : BlowupTower B Y'}
      {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y},
      IsTowerIso φ T' T χ →
      ∀ {W D : Set A} {E : List (Set A)} {H : ℕ → ℕ}, term T W D E H →
        term T' (φ ⁻¹' W) (φ ⁻¹' D) (E.map (φ ⁻¹' ·)) H)
    (h : ClearedOverWith term X W D K E H) (hW : IsComplexAnalyticSubset (n := n) W) :
    ∃ O : Opens X, K ⊆ O ∧
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
        IsGeoTestTower original[(Subtype.val : O → X) ⁻¹' W; E.map ((Subtype.val : O → X) ⁻¹' ·)] T ∧
        StageCentres (fun S C => C ⊆ singularSet (n := n)
          (strictTransform n S.proj ((Subtype.val : O → X) ⁻¹' W))) T ∧
        (∀ z ℓ, HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z ℓ ≤
          HS[(Subtype.val : O → X) ⁻¹' W] (T.proj z) ℓ) ∧
        (∀ z ∈ T.proj ⁻¹' ((Subtype.val : O → X) ⁻¹' D),
          toLex (HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z) < toLex H) ∧
        CentresOver ((Subtype.val : O → X) ⁻¹' D) T ∧
        term T ((Subtype.val : O → X) ⁻¹' W) ((Subtype.val : O → X) ⁻¹' D)
          (E.map ((Subtype.val : O → X) ⁻¹' ·)) H := by
  obtain ⟨B,j,hj,hK,Y,T,hT,hStage,hBound,hDrop,hOver,hEnd⟩ := h
  let Wb := j ⁻¹' W
  have hWb : IsComplexAnalyticSubset (n := n) Wb :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hj.contMDiff hW
  obtain ⟨O,φ,hφ⟩ := hj
  let Wo := (Subtype.val : O → X) ⁻¹' W
  let β := φ.symm
  let tr := transport (X' := CMfd.of (n := n) O) β T
  have hβ (x : O) : j (β x) = x.val := by
    rw [hφ, φ.apply_symm_apply]
  have hWs : (β ⁻¹' Wb) = Wo := by
    ext x
    change j (β x) ∈ W ↔ x.val ∈ W
    rw [hβ]
  have hWt : φ ⁻¹' Wo = Wb := by
    ext x
    change (φ x).val ∈ W ↔ j x ∈ W
    rw [hφ]
  have hEtrace : (E.map (j ⁻¹' ·)).map (β ⁻¹' ·) = E.map ((Subtype.val : O → X) ⁻¹' ·) := by
    rw [List.map_map]
    apply congrArg E.map
    funext D
    ext x
    change j (β x) ∈ D ↔ x.val ∈ D
    rw [hβ]
  have hVan : GermIdeal.pullback (m := n) β (vanishingIdeal (n := n) Wb) = vanishingIdeal (n := n) Wo := by
    have hId := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
      β.contMDiff β.symm.contMDiff β.apply_symm_apply β.symm_apply_apply
      (g := (id : O → O)) contMDiff_id Wb
    rw [hWs, Function.comp_id] at hId
    exact hId.symm.trans (GermIdeal.ext (funext fun _ => funext fun _ =>
      propext BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff))
  have hRecord : MarkedIdeal.pullback β original[Wb; E.map (j ⁻¹' ·)] =
      original[Wo; E.map ((Subtype.val : O → X) ⁻¹' ·)] := by
    change (MarkedIdeal.mk (β ⁻¹' univ) ((E.map (j ⁻¹' ·)).map (β ⁻¹' ·))
      (GermIdeal.pullback (m := n) β (vanishingIdeal (n := n) Wb)) 1 : MarkedIdeal n O) = _
    rw [preimage_univ, hEtrace, hVan]
  have hTest := (isGeoTestTower_transport_iff (X' := CMfd.of (n := n) O) β (CartanIrreducible.cartanCoherence Wb hWb) T).mpr hT
  rw [hRecord] at hTest
  have hIso := transport_isTowerIso (X' := CMfd.of (n := n) O) β T
  have hTrace := strictTransform_preimage_of_square (A' := CMfd.of (n := n) O) β tr.back
    tr.tower.contMDiff_proj T.contMDiff_proj Wb hWb.isClosed
    (fun x => (proj_transport (X' := CMfd.of (n := n) O) β T x).symm)
  have hDs : β ⁻¹' (j ⁻¹' D) = (Subtype.val : O → X) ⁻¹' D := by
    ext x
    change j (β x) ∈ D ↔ x.val ∈ D
    rw [hβ]
  refine ⟨O, ?_, tr.target, tr.tower, hTest, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y,rfl⟩ := hK hx
    rw [hφ]
    exact (φ y).property
  · have hSing := singular_stages_of_tower_iso (X' := B) (X := CMfd.of (n := n) O)
      (T' := T) (T := tr.tower) Wo (hW.isClosed.preimage continuous_subtype_val) β.symm hIso.symm
    apply hSing
    change StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj (φ ⁻¹' Wo))) T
    rw [hWt]
    exact hStage
  · intro z ℓ
    change HS[strictTransform n tr.tower.proj Wo] z ℓ ≤ HS[Wo] (tr.tower.proj z) ℓ
    rw [← hWs, hTrace, hilbertSamuelAt_vanishing_actual_biholomorphic_any tr.back,
      hilbertSamuelAt_vanishing_actual_biholomorphic_any β,
      proj_transport (X' := CMfd.of (n := n) O) β T z]
    exact hBound _ _
  · intro z hz
    have hz' : T.proj (tr.back z) ∈ j ⁻¹' D := by
      change j (T.proj (tr.back z)) ∈ D
      rw [← proj_transport (X' := CMfd.of (n := n) O) β T z, hβ]
      exact hz
    change toLex (HS[strictTransform n tr.tower.proj Wo] z) < toLex H
    rw [← hWs, hTrace]
    have hHS := funext (hilbertSamuelAt_vanishing_actual_biholomorphic_any tr.back
      (strictTransform n T.proj Wb) z)
    rw [hHS]
    exact hDrop _ hz'
  · have hOver' := centresOver_of_isTowerIso hIso (j ⁻¹' D) hOver
    rw [hDs] at hOver'
    exact hOver'
  · have hNew : term tr.tower (β ⁻¹' Wb) (β ⁻¹' (j ⁻¹' D))
        ((E.map (j ⁻¹' ·)).map (β ⁻¹' ·)) H :=
      hTransport (B := CMfd.of (n := n) O) β hIso hEnd
    rw [hWs,hDs,hEtrace] at hNew
    exact hNew

omit [WellFoundedLT Λ] in
/-- Flatten the nested shrinkings to a single literal open subset of
the initial ambient manifold, transporting the same physical tower. -/
theorem ClearedOver.exists_literal_open {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ}
    (h : ClearedOver I R X W D K E H) (hW : IsComplexAnalyticSubset (n := n) W) :
    ∃ O : Opens X, K ⊆ O ∧
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
        IsGeoTestTower original[(Subtype.val : O → X) ⁻¹' W; E.map ((Subtype.val : O → X) ⁻¹' ·)] T ∧
        StageCentres (fun S C => C ⊆ singularSet (n := n)
          (strictTransform n S.proj ((Subtype.val : O → X) ⁻¹' W))) T ∧
        (∀ z ℓ, HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z ℓ ≤
          HS[(Subtype.val : O → X) ⁻¹' W] (T.proj z) ℓ) ∧
        (∀ z ∈ T.proj ⁻¹' ((Subtype.val : O → X) ⁻¹' D),
          toLex (HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z) < toLex H) ∧
        CentresOver ((Subtype.val : O → X) ⁻¹' D) T ∧
        TerminalWindows I R T ((Subtype.val : O → X) ⁻¹' W) ((Subtype.val : O → X) ⁻¹' D)
          (E.map ((Subtype.val : O → X) ⁻¹' ·)) H :=
  clearedOverWith_exists_literal_open (fun {A B Y Y'} φ {T T' χ} hIso {W D E H} hEnd => by
    obtain ⟨S,hS⟩ := hEnd
    exact ⟨S.transportBase (B := B) φ, fun i => S.terminal_transportBase (B := B) (T := T) (T' := T') φ _ hIso hS i⟩) h hW

omit [WellFoundedLT Λ] in
/-- Flatten the nested shrinkings to a single literal open subset of
the initial ambient manifold, transporting the same physical tower. -/
theorem ClearedOverRemembering.exists_literal_open {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {keep : Prop} {R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ}
    (h : ClearedOverRemembering keep I R X W D K E H) (hW : IsComplexAnalyticSubset (n := n) W) :
    ∃ O : Opens X, K ⊆ O ∧
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
        IsGeoTestTower original[(Subtype.val : O → X) ⁻¹' W; E.map ((Subtype.val : O → X) ⁻¹' ·)] T ∧
        StageCentres (fun S C => C ⊆ singularSet (n := n)
          (strictTransform n S.proj ((Subtype.val : O → X) ⁻¹' W))) T ∧
        (∀ z ℓ, HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z ℓ ≤
          HS[(Subtype.val : O → X) ⁻¹' W] (T.proj z) ℓ) ∧
        (∀ z ∈ T.proj ⁻¹' ((Subtype.val : O → X) ⁻¹' D),
          toLex (HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z) < toLex H) ∧
        CentresOver ((Subtype.val : O → X) ⁻¹' D) T ∧
        TerminalWindowsRemembering keep I R T ((Subtype.val : O → X) ⁻¹' W) ((Subtype.val : O → X) ⁻¹' D)
          (E.map ((Subtype.val : O → X) ⁻¹' ·)) H :=
  clearedOverWith_exists_literal_open (fun {A B Y Y'} φ {T T' χ} hIso {W D E H} hEnd => by
    obtain ⟨S,hS,hSync⟩ := hEnd
    exact ⟨S.transportBase (B := B) φ, fun i => S.terminal_transportBase (B := B) (T := T) (T' := T') φ _ hIso hS i,
      fun hKeep => S.simultaneous_transportBase (B := B) (T := T) (T' := T') φ _ hIso (fun i => (hS i).1) (hSync hKeep)⟩) h hW

/-- A compact task is cleared at this profile on a single literal base open
by a finite tower in its initial mark-one full-boundary test class. -/
theorem exists_finite_native_clearing_open_with_native (hn : 0 < n)
    (R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n Λ)
    {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hD : IsClosed D) (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ}) (hK : IsCompact K)
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (A : NativeWindows X I W E H D) :
    ∃ O : Opens X, K ⊆ O ∧
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
        IsGeoTestTower original[(Subtype.val : O → X) ⁻¹' W; E.map ((Subtype.val : O → X) ⁻¹' ·)] T ∧
        StageCentres (fun S C => C ⊆ singularSet (n := n)
          (strictTransform n S.proj ((Subtype.val : O → X) ⁻¹' W))) T ∧
        (∀ z ℓ, HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z ℓ ≤
          HS[(Subtype.val : O → X) ⁻¹' W] (T.proj z) ℓ) ∧
        (∀ z ∈ T.proj ⁻¹' ((Subtype.val : O → X) ⁻¹' D),
          toLex (HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z) < toLex H) ∧
        CentresOver ((Subtype.val : O → X) ⁻¹' D) T ∧
        TerminalWindows I R.toResolutionInvariant T ((Subtype.val : O → X) ⁻¹' W) ((Subtype.val : O → X) ⁻¹' D)
          (E.map ((Subtype.val : O → X) ⁻¹' ·)) H :=
  (exists_finite_native_clearing hn R hW hE hD hExact hK hNot A).exists_literal_open hW

/-- Forget the terminal local records when using the finite tower only
as a geometric phase in a larger resolution. -/
theorem exists_finite_native_clearing_open (hn : 0 < n)
    (R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n Λ)
    {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hD : IsClosed D) (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ}) (hK : IsCompact K)
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (A : NativeWindows X I W E H D) :
    ∃ O : Opens X, K ⊆ O ∧
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
        IsGeoTestTower original[(Subtype.val : O → X) ⁻¹' W; E.map ((Subtype.val : O → X) ⁻¹' ·)] T ∧
        StageCentres (fun S C => C ⊆ singularSet (n := n)
          (strictTransform n S.proj ((Subtype.val : O → X) ⁻¹' W))) T ∧
        (∀ z ℓ, HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z ℓ ≤
          HS[(Subtype.val : O → X) ⁻¹' W] (T.proj z) ℓ) ∧
        ∀ z ∈ T.proj ⁻¹' ((Subtype.val : O → X) ⁻¹' D),
          toLex (HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z) < toLex H := by
  obtain ⟨O,hKO,Y,T,hTest,hStage,hBound,hDrop,_,_⟩ :=
    exists_finite_native_clearing_open_with_native hn R hW hE hD hExact hK hNot A
  exact ⟨O,hKO,Y,T,hTest,hStage,hBound,hDrop⟩

end Induction

/-- The original canonical invariant and actual whole-power transform
supply raw terminal native certificates on those very same restrictions. -/
theorem TerminalWindows.raw_original_certificates (hn : 0 < n) {Y : CMfd.{0} n}
    {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {T : BlowupTower X Y}
    (h : TerminalWindows I (canonicalInvariant n) T W D E H) :
    ∃ S : NativeWindows X I W E H D,
      ∀ i, IsCanonical (S.record i) ((invFamily hn n).inv (S.record i)) (restrict (S.openSet i) T) ∧
        IsGeoResolution (S.record i) (restrict (S.openSet i) T) := by
  obtain ⟨S,hS⟩ := h
  refine ⟨S, fun i => ?_⟩
  let U := restrict (S.openSet i) T
  let P := S.record i
  let e := S.exponent i
  have hDom := S.domain i
  have hPos := S.positive i
  have hCan := (canonicalInvariant_isCanonical_power_iff P hDom e hPos U).mpr (hS i).1
  have hTest := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hDom U hCan
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom U hTest
  have hCos := (original_power_transform P hDom e hPos U hTest).2.cosupp_eq.trans
    (powerMarked_cosupp (geoTransformAlong P U) hCurrent hPos)
  rw [canonicalInvariant_eq_invFamily hn] at hCan
  exact ⟨hCan, hTest, hCos.symm.trans (hS i).2.2⟩

end
end Hironaka.HironakaG8NativeRelativeClearing
