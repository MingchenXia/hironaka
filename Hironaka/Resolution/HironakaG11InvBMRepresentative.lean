import Hironaka.Resolution.HironakaG11InvBMTowerIso
import Hironaka.Invariant.StepOneRepresentative

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's Step 1 value: independence of the representative (repair (B'), plan module 8, property (7))

Blueprint: `hironaka-g11-inv-bm-max-order.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6c.

For restricted-equivalent `𝔍 ≃ 𝔍'` (same `N`, divisor and mark, ideals equal on `N`), both of maximal order, the canonical
segments of `stepOneInvBM R 𝔍` are those of `stepOneInvBM R 𝔍'` and the values agree on the cosupport, given the independence
of the hypersurface of maximal contact for `𝔍'`.

* `RestrictEquiv.withExcBM`, **`restrictEquiv_lowerIdealWBM`**: the lower ideals of `𝔍` and `𝔍'` formed with the SAME tangent
  function and members are restricted-equivalent (coefficient ideals of restricted-equivalent ideals along `N` are, and from
  the first blowup on the transforms are equal);
* `lowerIdealWBM_N`, **`pullback_val_lowerIdealWBM_congr`**: over an open set of the stage lying over an open `O` of the base,
  the lower ideal depends on the tangent function only through its values on `N ∩ O`;
* **`lowerValueG_representative`** (both levels): restricted equivalence on the mask of `𝔍`, shrunk to where a tangent direction
  `w'` of `𝔍'` agrees with `w` on `N` (`ContactRepresentative.exists_isTangentDirectionAlong_of_restrictLe`), then the anchor for
  `𝔍'`;
* `stepOneInvBM_representative_eq`, **`stepOneInvBM_representative`**, **`representative_field`**.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMRepresentative

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime
  Hironaka.StepOneValue Hironaka.StepOneLowerDomain
  Hironaka.StepOneValueMasked Hironaka.MarkedIdealRestrictOpen
  Hironaka.HomogenizedIdealAlong Hironaka.BlowupTowerIsomorphism
  Hironaka.BlowupTowerIsoTail Hironaka.MarkedIdealBiholomorphism
  Hironaka.HironakaG11InvBMMask Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG11InvBMCanonicalTail Hironaka.HironakaG11InvBMAdmissible
  Hironaka.HironakaG11InvBMTangentIndep Hironaka.HironakaG11InvBMNaturality
  Hironaka.HironakaG11InvBMRestrictOpen
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.CoefficientIdealRestriction (withN)
open Hironaka.HomogenizedGlueingTower (strictAlong N_geoTransformAlong)
open Hironaka.RestrictedIdealWeight (RestrictLe)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv hol_of_isCoherent)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Restricted equivalence of the lower ideals -/

section Lower

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The sum with the `ℰ`-term respects restricted equivalence** (the second ideal coherent, members closed
submanifolds). -/
theorem RestrictEquiv.withExcBM {C C' : MarkedIdeal n M} (h : RestrictEquiv C C') (hC : C.ideal.IsCoherent)
    (hC' : C'.ideal.IsCoherent) {S : List (Set M)} (hS : ∀ H ∈ S, IsClosedSubmanifold n H) :
    RestrictEquiv (withExcBM C S) (withExcBM C' S) := by
  have hX := hol_of_isCoherent (HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hS C.d)
  refine ⟨h.N_eq, h.E_eq, h.d_eq, ?_, ?_⟩
  · show RestrictLe C.N (sumIdeal C.ideal (exceptionalTermBM (n := n) S C.d))
      (sumIdeal C'.ideal (exceptionalTermBM (n := n) S C'.d))
    rw [← h.d_eq]
    exact MarkedIdealOperationsAlong.restrictLe_sumIdeal (hol_of_isCoherent hC') hX h.le
      (DerivativeIdealAlongTransform.restrictLe_refl hX)
  · show RestrictLe C.N (sumIdeal C'.ideal (exceptionalTermBM (n := n) S C'.d))
      (sumIdeal C.ideal (exceptionalTermBM (n := n) S C.d))
    rw [← h.d_eq]
    exact MarkedIdealOperationsAlong.restrictLe_sumIdeal (hol_of_isCoherent hC) hX h.ge
      (DerivativeIdealAlongTransform.restrictLe_refl hX)

variable {X : CMfd.{u} n}

/-- The carrier of the lower ideal: the strict transform of the hypersurface `N ∩ V(w)`. -/
theorem lowerIdealWBM_N (𝔍 : MarkedIdeal n X) (s : ℕ) (w : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (S : List (Set Y₀)) : (lowerIdealWBM 𝔍 s w T₀ S).N = strictAlong T₀ (𝔍.N ∩ {x | w x = 0}) := by
  cases s <;> rfl

/-- **Restricted-equivalent marked ideals have restricted-equivalent lower ideals** for the same tangent function and
members (`T₀` a multiple test blow-up of `J̄`; members closed submanifolds). -/
theorem restrictEquiv_lowerIdealWBM {𝔍 𝔍' : MarkedIdeal n X} (hEq : RestrictEquiv 𝔍 𝔍') (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) (h𝔍' : 𝔍'.ideal.IsCoherent) (s : ℕ) (w : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) (S : List (Set Y₀)) (hS : ∀ H ∈ S, IsClosedSubmanifold n H) :
    RestrictEquiv (lowerIdealWBM 𝔍 s w T₀ S) (lowerIdealWBM 𝔍' s w T₀ S) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have hE0 : RestrictEquiv (emptyBoundary 𝔍) (emptyBoundary 𝔍') := ⟨hEq.N_eq, rfl, hEq.d_eq, hEq.le, hEq.ge⟩
  have hC : RestrictEquiv (coeffEmptyBM 𝔍) (coeffEmptyBM 𝔍') :=
    ContactCanonicalAlong.restrictEquiv_coeffMarkedAlong hE0 (hol_of_isCoherent h𝔍.isCoherent) (hol_of_isCoherent h𝔍')
  have hwfc := HironakaG11InvBMStage.isWellFormed_coeffEmptyBM h𝔍
  have hc' : (coeffEmptyBM 𝔍').ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (𝔪 := emptyBoundary 𝔍') h𝔍' (show IsClosedSubmanifold n 𝔍'.N from hEq.N_eq ▸ hN)
  have hTc := isGeoTestTower_coeffEmptyBM_of_barMarked 𝔍 h𝔍 hd T₀ hT₀
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N hwfc.isCoherent
    T₀ hTc
  have hG : RestrictEquiv (geoTransformAlong (coeffEmptyBM 𝔍) T₀) (geoTransformAlong (coeffEmptyBM 𝔍') T₀) := by
    cases T₀ with
    | refl => exact hC
    | step T C π hπ =>
      have e := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq hC
        hwfc.isClosedSubmanifold_N.1 hwfc.isCoherent hc' T C π hπ
      rw [← e]
      exact ContactCanonicalAlong.restrictEquiv_self _ (hol_of_isCoherent hcT)
  have hNeq : strictAlong T₀ (𝔍'.N ∩ {x | w x = 0}) = strictAlong T₀ (𝔍.N ∩ {x | w x = 0}) := by rw [hEq.N_eq]
  have h0 : RestrictEquiv (contactCoeffBM 𝔍 w T₀) (contactCoeffBM 𝔍' w T₀) := by
    show RestrictEquiv (withN (geoTransformAlong (coeffEmptyBM 𝔍) T₀) (strictAlong T₀ (𝔍.N ∩ {x | w x = 0})))
      (withN (geoTransformAlong (coeffEmptyBM 𝔍') T₀) (strictAlong T₀ (𝔍'.N ∩ {x | w x = 0})))
    rw [hNeq]
    refine ContactCanonicalAlong.restrictEquiv_withN hG ?_
    rw [N_geoTransformAlong]
    exact MemberInterTowerAlong.strictAlong_mono T₀ (fun x hx => hx.1)
  cases s with
  | zero => exact h0
  | succ s =>
    have hTc' : IsGeoTestTower (coeffEmptyBM 𝔍') T₀ :=
      ((MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hC hwfc.isClosedSubmanifold_N.1 hwfc.isCoherent
        hc').2 T₀).1.mp hTc
    obtain ⟨-, hcT'⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      (show IsClosedSubmanifold n (coeffEmptyBM 𝔍').N from hEq.N_eq ▸ hN) hc' T₀ hTc'
    exact RestrictEquiv.withExcBM h0 hcT hcT' hS

/-- **Over an open set of the stage over `O`, the lower ideal depends on the tangent function only through its values on
`N ∩ O`.** -/
theorem pullback_val_lowerIdealWBM_congr (𝔍 : MarkedIdeal n X) {O : Set X} (hO : IsOpen O) {w w' : X → ℂ}
    (hww' : ∀ x ∈ O, x ∈ 𝔍.N → w x = w' x) (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (S : List (Set Y₀))
    (W : Opens Y₀) (hW : (W : Set Y₀) ⊆ T₀.proj ⁻¹' O) :
    MarkedIdeal.pullback (Subtype.val : W → Y₀) (lowerIdealWBM 𝔍 s w T₀ S) =
      MarkedIdeal.pullback (Subtype.val : W → Y₀) (lowerIdealWBM 𝔍 s w' T₀ S) := by
  obtain ⟨hI, hd, hE⟩ := lowerIdealWBM_ideal_eq 𝔍 s w w' T₀ S
  have hloc := ContactEquivalenceStage.strictAlong_inter_preimage_eq hO
    (A := 𝔍.N ∩ {x | w x = 0}) (B := 𝔍.N ∩ {x | w' x = 0}) (by
      ext y
      show (y ∈ 𝔍.N ∧ w y = 0) ∧ y ∈ O ↔ (y ∈ 𝔍.N ∧ w' y = 0) ∧ y ∈ O
      constructor
      · rintro ⟨⟨hyN, hy0⟩, hyO⟩
        exact ⟨⟨hyN, by rw [← hww' y hyO hyN]; exact hy0⟩, hyO⟩
      · rintro ⟨⟨hyN, hy0⟩, hyO⟩
        exact ⟨⟨hyN, by rw [hww' y hyO hyN]; exact hy0⟩, hyO⟩) T₀
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ hd
  · show (Subtype.val : W → Y₀) ⁻¹' (lowerIdealWBM 𝔍 s w T₀ S).N =
      (Subtype.val : W → Y₀) ⁻¹' (lowerIdealWBM 𝔍 s w' T₀ S).N
    rw [lowerIdealWBM_N, lowerIdealWBM_N]
    ext p
    have hp : (p : Y₀) ∈ T₀.proj ⁻¹' O := hW p.2
    constructor
    · intro h
      have h1 : (p : Y₀) ∈ strictAlong T₀ (𝔍.N ∩ {x | w x = 0}) ∩ T₀.proj ⁻¹' O := ⟨h, hp⟩
      rw [hloc] at h1
      exact h1.1
    · intro h
      have h1 : (p : Y₀) ∈ strictAlong T₀ (𝔍.N ∩ {x | w' x = 0}) ∩ T₀.proj ⁻¹' O := ⟨h, hp⟩
      rw [← hloc] at h1
      exact h1.1
  · show (lowerIdealWBM 𝔍 s w T₀ S).E.map _ = (lowerIdealWBM 𝔍 s w' T₀ S).E.map _
    rw [hE]
  · show GermIdeal.pullback (m := n) (Subtype.val : W → Y₀) (lowerIdealWBM 𝔍 s w T₀ S).ideal =
      GermIdeal.pullback (m := n) (Subtype.val : W → Y₀) (lowerIdealWBM 𝔍 s w' T₀ S).ideal
    rw [hI]

end Lower

/-! ### Property (7) -/

section Representative

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n (k - 1) Λ)
  {𝔍 𝔍' : MarkedIdeal n X}

/-- **Property (7) of Bierstone--Milman's Step 1 value, lower values** (both levels): for restricted-equivalent `𝔍 ≃ 𝔍'`
(well formed, `d ≥ 1`), `T₀ T₁` a multiple test blow-up of `J̄(𝔍)` and of `J̄(𝔍')`, and a point `y` with lower data at level
`s` for both at the split `T₀ T₁` (its image at `T₀` in `cosupp J̄(𝔍')_{T₀}`, of level `s`), the two lower values
agree, given the independence of the hypersurface of maximal contact for `𝔍'`. -/
theorem lowerValueG_representative (hEq : RestrictEquiv 𝔍 𝔍') (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (h𝔍' : 𝔍'.IsWellFormed) (hd' : 1 ≤ 𝔍'.d) (hTI' : TangentIndepBM 𝔍' R) {s : ℕ} {Y₀ Z : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Z) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁))
    (hT' : IsGeoTestTower (barMarked 𝔍') (T₀.append T₁)) {y : Z}
    (ha' : T₁.proj y ∈ (geoTransformAlong (barMarked 𝔍') T₀).cosupp) (hl' : level 𝔍' T₀ (T₁.proj y) = s)
    (hD : LowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s T₀ T₁ y) (hD' : LowerDataG R 𝔍' (maskBM 𝔍') (lowerBM 𝔍') s T₀ T₁ y) :
    lowerValueG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s T₀ T₁ y = lowerValueG R 𝔍' (maskBM 𝔍') (lowerBM 𝔍') s T₀ T₁ y := by
  classical
  obtain ⟨hT₀, -⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  obtain ⟨hT₀', -⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT'
  -- the data on the side of `𝔍`
  obtain ⟨h, hdom, hcan, hcos⟩ := hD
  have hw := isTangentDirectionAlong_tangentChoice_of_nonempty 𝔍
    ⟨_, HironakaG11InvBMCanonicalTail.maskBM_subset_tangent 𝔍 s T₀ _ h⟩
  have hS := HironakaG11InvBMLowerTailSucc.isClosedSubmanifold_of_mem_throughMembers 𝔍 h𝔍 hn T₀ hT₀ (T₁.proj y)
  have hcoh := isCoherent_lowerIdealWBM 𝔍 h𝔍 hd hn s (tangentChoice 𝔍 (T₀.proj (T₁.proj y))).2 T₀ hT₀ (T₁.proj y)
  have hLeq : lowerBM 𝔍 s T₀ (T₁.proj y) = MarkedIdeal.pullback (Subtype.val : maskBM 𝔍 s T₀ (T₁.proj y) → Y₀)
      (lowerIdealWBM 𝔍 s (tangentChoice 𝔍 (T₀.proj (T₁.proj y))).2 T₀ (throughMembers 𝔍 T₀ (T₁.proj y))) := by
    rw [lowerBM_eq, lowerIdealBM_eq_lowerIdealWBM]
  rw [hLeq] at hdom hcan hcos
  rw [lowerValueG_eq_of_mem R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) h, hLeq]
  -- the base point and a tangent direction of `𝔍'` agreeing with `w` on `N`
  have hxU : T₀.proj (T₁.proj y) ∈ (tangentChoice 𝔍 (T₀.proj (T₁.proj y))).1 :=
    HironakaG11InvBMCanonicalTail.maskBM_subset_tangent 𝔍 s T₀ _ h
  have hxN : T₀.proj (T₁.proj y) ∈ 𝔍.N := by
    have hJ' := isWellFormed_barMarked 𝔍' h𝔍'
    have h1 := proj_mem_cosupp_of_mem_cosupp hJ'.isClosedSubmanifold_N hJ'.isCoherent T₀ hT₀' ha'
    rw [cosupp_barMarked 𝔍' h𝔍' hd'] at h1
    rw [hEq.N_eq]
    exact h1.1
  obtain ⟨O, hxO, hOU, w', hw', hww'⟩ := ContactRepresentative.exists_isTangentDirectionAlong_of_restrictLe
    (hol_of_isCoherent h𝔍.isCoherent) h𝔍'.isCoherent h𝔍.isClosedSubmanifold_N hEq.le hw hxU hxN
  have hw'' : IsTangentDirectionAlong 𝔍'.N 𝔍'.ideal 𝔍'.d O w' := by
    rw [← hEq.N_eq, ← hEq.d_eq]
    exact hw'
  have hthr : throughMembers 𝔍' T₀ (T₁.proj y) = throughMembers 𝔍 T₀ (T₁.proj y) := by
    unfold throughMembers
    rw [ContactLowerValue.origMembers_restrictEquiv hEq T₀]
  -- (1) shrink the mask to its part over `O`
  have hM₁M : maskBM 𝔍 s T₀ (T₁.proj y) ⊓ openPreimage T₀ O ≤ maskBM 𝔍 s T₀ (T₁.proj y) := inf_le_left
  obtain ⟨hdom₁, hcan₁, hval₁⟩ := MaxLocusLocal.restrict_nestedOpens R hcoh hM₁M hdom T₁ hcan
  have hyM₁ : T₁.proj y ∈ maskBM 𝔍 s T₀ (T₁.proj y) ⊓ openPreimage T₀ O := ⟨h, hxO⟩
  have hcos₁ := (mem_cosupp_nested_iff hcoh hM₁M hdom.isWellFormed T₁ (isGeoTestTower_of_isCanonical R hdom _ hcan)
    ⟨y, hyM₁⟩).mpr hcos
  have v1 := hval₁ ⟨y, hyM₁⟩ hcos₁
  -- (2) restricted equivalence with the lower ideal of `𝔍'` formed with `w'`
  have hM₁O : ((maskBM 𝔍 s T₀ (T₁.proj y) ⊓ openPreimage T₀ O : Opens Y₀) : Set Y₀) ⊆ T₀.proj ⁻¹' (O : Set X) :=
    fun _ hz => hz.2
  have hE₀ := restrictEquiv_lowerIdealWBM hEq h𝔍 hd h𝔍'.isCoherent s (tangentChoice 𝔍 (T₀.proj (T₁.proj y))).2 T₀ hT₀
    _ hS
  have hcoh' := isCoherent_lowerIdealWBM 𝔍' h𝔍' hd' hn s (tangentChoice 𝔍 (T₀.proj (T₁.proj y))).2 T₀ hT₀'
    (T₁.proj y)
  rw [hthr] at hcoh'
  have hE₁ := ContactRepresentative.restrictEquiv_pullback_val (maskBM 𝔍 s T₀ (T₁.proj y) ⊓ openPreimage T₀ O) hE₀
    hcoh hcoh'
  rw [pullback_val_lowerIdealWBM_congr 𝔍' O.isOpen (fun x hxO hxN => (hww' x hxO (hEq.N_eq ▸ hxN)).symm) s T₀ _ _
    hM₁O] at hE₁
  have hcoh'' := GermIdealPullbackCalculus.isCoherent_pullback
    (contMDiff_subtype_val (U := maskBM 𝔍 s T₀ (T₁.proj y) ⊓ openPreimage T₀ O))
    (isCoherent_lowerIdealWBM 𝔍' h𝔍' hd' hn s w' T₀ hT₀' (T₁.proj y))
  rw [hthr] at hcoh''
  have hdom'' := InvDomainRebase.isInvDomain_of_restrictEquiv hdom₁ hE₁ hcoh''
  have hcan'' := InvDomainRebase.isCanonical_of_restrictEquiv R hdom₁ hdom'' hE₁ _ hcan₁
  have v2 := R.representative _ _ hdom₁ hdom'' hE₁ _ hcan₁ ⟨y, hyM₁⟩ hcos₁
  rw [← hthr] at hdom'' hcan''
  -- (3) the anchor for `𝔍'` with `w'` on the shrunk mask
  have key := lowerValueG_eq_of_tangent 𝔍' R hTI' T₀ T₁ hT' ha' hl' hD' hw'' _ hM₁O hyM₁ hdom'' hcan''
  rw [key]
  congr 1
  rw [← v1, v2, hthr]

/-- **The values agree along common canonical segments** (`𝔍 ≃ 𝔍'`, both satisfying the hypotheses of Step 1, given the
independence of the hypersurface of maximal contact for both). -/
theorem stepOneInvBM_representative_eq (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) (h𝔍' : 𝔍'.IsWellFormed) (hd' : 1 ≤ 𝔍'.d)
    (hmax' : IsMaximalOrderAlong 𝔍'.N 𝔍'.ideal 𝔍'.d) (hk' : DimLE n 𝔍'.N k) (hEq : RestrictEquiv 𝔍 𝔍')
    (hTI : TangentIndepBM 𝔍 R) (hTI' : TangentIndepBM 𝔍' R)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T)
    (hcan' : IsCanonical (barMarked 𝔍') (stepOneInvBM R 𝔍') T) {y : Y}
    (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) :
    stepOneInvBM R 𝔍 T y = stepOneInvBM R 𝔍' T y := by
  have hAC : AnchorChangeBM 𝔍 R := anchorChangeBM_of_tangentIndepBM 𝔍 R hTI
  have hAC' : AnchorChangeBM 𝔍' R := anchorChangeBM_of_tangentIndepBM 𝔍' R hTI'
  have hT := isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk T hcan
  have hT' := isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍' R hAC' h𝔍' hd' hn hmax' hk' T hcan'
  obtain ⟨-, hC, -, hpt⟩ := StepOneRepresentative.restrictEquiv_facts h𝔍 h𝔍'.isCoherent hEq T
  obtain ⟨hl, hs, -⟩ := hpt y
  have hy' : y ∈ (geoTransformAlong (barMarked 𝔍') T).cosupp := hC ▸ hy
  have hD := hasLowerDataG_of_isCanonical 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan y hy
  have hD' := hasLowerDataG_of_isCanonical 𝔍' R hAC' h𝔍' hd' hn hmax' hk' T hT' hcan' y hy'
  unfold stepOneInvBM
  by_cases hsp : IsSpecial 𝔍 T y
  · rw [stepOneInvG_of_isSpecial R 𝔍 _ _ T hsp, stepOneInvG_of_isSpecial R 𝔍' _ _ T (hs.mp hsp), hl]
  · have hsp' : ¬ IsSpecial 𝔍' T y := fun h => hsp (hs.mpr h)
    have hreg' := stepRegime_and_mem_cosupp_head 𝔍' h𝔍' T hT' hy' hsp'
    specialize hD hsp
    specialize hD' hsp'
    rw [stepOneInvG_of_not_isSpecial R 𝔍 _ _ T hsp, stepOneInvG_of_not_isSpecial R 𝔍' _ _ T hsp']
    rw [← hl] at hD' hreg' ⊢
    obtain ⟨s, hsdef⟩ : ∃ s, level 𝔍 T y = s := ⟨_, rfl⟩
    rw [hsdef] at hD hD' hreg' ⊢
    have hrun := StepOneRepresentative.regimeRun_congr (stepRegime 𝔍 s) (stepRegime 𝔍' s)
      (fun T' y' => ((StepOneRepresentative.restrictEquiv_facts h𝔍 h𝔍'.isCoherent hEq T').2.2.2 y').2.2 s) T y
    rw [hrun] at hD ⊢
    have hsplit := head_append_tail T (regimeRun (stepRegime 𝔍' s) T y)
    have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((head T (regimeRun (stepRegime 𝔍' s) T y)).append
        (tail T (regimeRun (stepRegime 𝔍' s) T y))) := by rw [hsplit]; exact hT
    have hT₀₁' : IsGeoTestTower (barMarked 𝔍') ((head T (regimeRun (stepRegime 𝔍' s) T y)).append
        (tail T (regimeRun (stepRegime 𝔍' s) T y))) := by rw [hsplit]; exact hT'
    congr 2
    exact lowerValueG_representative R hEq h𝔍 hd hn h𝔍' hd' hTI' _ _ hT₀₁ hT₀₁' hreg'.2 hreg'.1.1 hD hD'

/-- **Property (7) of Bierstone--Milman's Step 1 value** (given the independence of the hypersurface of maximal contact for
`𝔍` and `𝔍'`): for restricted-equivalent `𝔍 ≃ 𝔍'`, both well formed with `d ≥ 1`, of maximal order along `N` with
`dim N ≤ k` (`0 < n`), every canonical segment of `stepOneInvBM R 𝔍` is one of `stepOneInvBM R 𝔍'`, and the two values agree
on the cosupport of `J̄_T`. -/
theorem stepOneInvBM_representative (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) (h𝔍' : 𝔍'.IsWellFormed) (hd' : 1 ≤ 𝔍'.d)
    (hmax' : IsMaximalOrderAlong 𝔍'.N 𝔍'.ideal 𝔍'.d) (hk' : DimLE n 𝔍'.N k) (hEq : RestrictEquiv 𝔍 𝔍')
    (hTI : TangentIndepBM 𝔍 R) (hTI' : TangentIndepBM 𝔍' R) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T →
      IsCanonical (barMarked 𝔍') (stepOneInvBM R 𝔍') T ∧
        ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, stepOneInvBM R 𝔍 T y = stepOneInvBM R 𝔍' T y
  | _, .refl, hcan => ⟨trivial, fun _ hy =>
      stepOneInvBM_representative_eq R h𝔍 hd hn hmax hk h𝔍' hd' hmax' hk' hEq hTI hTI' .refl hcan trivial hy⟩
  | _, .step T C π hπ, hcan => by
      have hcan₀ := hcan
      obtain ⟨hcanT, hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) := hcan
      obtain ⟨hcan'T, hval⟩ := stepOneInvBM_representative h𝔍 hd hn hmax hk h𝔍' hd' hmax' hk' hEq hTI hTI' T hcanT
      have hcosT := (StepOneRepresentative.restrictEquiv_facts h𝔍 h𝔍'.isCoherent hEq T).2.1
      have hcan'S : IsCanonical (barMarked 𝔍') (stepOneInvBM R 𝔍') (.step T C π hπ) := by
        refine (⟨hcan'T, hC.imp id fun h => h.trans ?_⟩ :
          IsCanonical (barMarked 𝔍') (stepOneInvBM R 𝔍') T ∧
            (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍' T) (geoTransformAlong (barMarked 𝔍') T).cosupp))
        rw [← hcosT]
        exact ResolutionInvariantExt.maxLocus_congr hval
      exact ⟨hcan'S, fun _ hy =>
        stepOneInvBM_representative_eq R h𝔍 hd hn hmax hk h𝔍' hd' hmax' hk' hEq hTI hTI' _ hcan₀ hcan'S hy⟩

/-- **Property (7), the field `representative`** of `MaxOrderValue.IsMaxOrderValue` for `stepOneInvBM R` (both marked ideals
of maximal order; given the independence of the hypersurface of maximal contact for both). -/
theorem representative_field (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (h𝔫 : IsInvDomain k 𝔍') (hmax' : IsMaximalOrderAlong 𝔍'.N 𝔍'.ideal 𝔍'.d) (hn : 0 < n) (hEq : RestrictEquiv 𝔍 𝔍')
    (hTI : TangentIndepBM 𝔍 R) (hTI' : TangentIndepBM 𝔍' R) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical 𝔍 (stepOneInvBM R 𝔍) T) (y : Y) (hy : y ∈ (geoTransformAlong 𝔍 T).cosupp) :
    stepOneInvBM R 𝔍 T y = stepOneInvBM R 𝔍' T y := by
  have hAC : AnchorChangeBM 𝔍 R := anchorChangeBM_of_tangentIndepBM 𝔍 R hTI
  rw [← (HironakaG11InvBMBridge.isGeoTestTower_of_isCanonical R 𝔍 hAC h hmax hn T hcan).2.2] at hy
  exact (stepOneInvBM_representative R h.isWellFormed h.one_le_d hn hmax h.dimLE h𝔫.isWellFormed h𝔫.one_le_d hmax'
    h𝔫.dimLE hEq hTI hTI' T ((HironakaG11InvBMBridge.isCanonical_iff R 𝔍 hAC h hmax hn T).mp hcan)).2 y hy

end Representative

end

end Hironaka.HironakaG11InvBMRepresentative
