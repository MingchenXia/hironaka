import Hironaka.Resolution.HironakaG11PresM8EmptyPrefix
import Hironaka.Resolution.HironakaG11InvBMPad
import Hironaka.Resolution.HironakaG11InvBMEmptyMemberStep

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Property (4') of Bierstone--Milman's Step 1 value with padded lower divisors (repair (B'), plan module 8)

Blueprint: `hironaka-g11-pres-m8-empty-prefix.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6d (decision
r7 of lane G11B: padded lower divisors), target sent to lane G11C in inbox I-1368 (comment C-0004).

`GeneralValue.genInv` reads the members of the divisor by their absolute positions, so a lower invariant sees the `|P|` empty
members that the lower ideal of `𝔍` at a stage `P H₀` carries in front of those of the lower ideal of `𝔍_P` at `H₀` (`P` with
only empty centres).  The lower invariant is therefore a FAMILY `Rm : ℕ → ResolutionInvariant` with
`(Rm (m + m')).inv L = (Rm m).inv (padE L m')` (the instance `Rm m L = R (padE L m)`), and the Step 1 value of `𝔍` is
`stepOneInvBM (Rm |𝔍.E|) 𝔍`.  Since `|𝔍_P.E| = |𝔍.E| + |P|`, property (4') compares `Rm m` on the lower ideal `L₁` of `𝔍` with
`Rm (m + |P|)` on the lower ideal `L₃` of `𝔍_P`, i.e. `Rm m` on `L₁` and on `padE L₃ |P|`, and these two are restricted-equivalent
with LITERALLY equal divisors (`HironakaG11PresM8EmptyCore.restrictEquiv_lowerIdealWBM_emptyPrefix`).

* `length_E_pullback_lowerIdealWBM`, **`restrictEquiv_padE_lowerIdealWBM_emptyPrefix`**: `padE L₃ |P| ≃ L₁` on every open over the
  tangent open set;
* **`lowerValueG_emptyPrefix_pad`** (both levels): the lower value of `𝔍_P` for `Rm (m + |P|)` is the value of `Rm m` on the lower
  ideal of `𝔍` (any tangent direction, any open over its open set), given `TangentIndepBM 𝔍_P (Rm (m + |P|))`;
* `lowerValueG_emptyPrefix_inside_pad`, `lowerValueG_emptyPrefix_cover_pad` (the two cases of the run),
  `stepOneInvBM_emptyPrefix_eq_pad`, **`stepOneInvBM_emptyPrefix_pad`**;
* **`emptyPrefix_field`**: the field `emptyPrefix` of `MaxOrderValue.IsMaxOrderValue` for the family value
  `fun 𝔍 T y => stepOneInvBM (Rm 𝔍.E.length) 𝔍 T y`, in lane G11B's announced shape.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11PresM8EmptyPad

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
  Hironaka.HironakaG11PresM8EmptyCore Hironaka.HironakaG11InvBMPad
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)
open Hironaka.HomogenizedGlueingTower (strictAlong)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)
open Hironaka.RestrictEmptyTower (CentresAvoid isEmptyTower_restrict_iff)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant IsEmptyTower
  isGeoTestTower_of_isEmptyTower isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

/-! ### The padded comparison -/

section Pad

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- The divisor of a lower ideal restricted to an open set has one member per blowup of the tower. -/
theorem length_E_pullback_lowerIdealWBM (s : ℕ) (w : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (S : List (Set Y₀)) (O : Opens Y₀) :
    (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s w T₀ S)).E.length = T₀.length := by
  show ((lowerIdealWBM 𝔍 s w T₀ S).E.map ((Subtype.val : O → Y₀) ⁻¹' ·)).length = T₀.length
  rw [List.length_map, lowerIdealWBM_eq_lowF, lowF_E, length_E_geoTransformAlong, coeffEmptyBM_E, List.length_nil,
    zero_add]

/-- **The padded lower ideals across an empty prefix**: in the situation of
`HironakaG11PresM8EmptyCore.restrictEquiv_lowerIdealWBM_emptyPrefix`, the lower ideal `L₃` of `𝔍_P` at `H₀` padded by `|P|` empty
members is restricted-equivalent to the lower ideal `L₁` of `𝔍` at `P H₀` (both restricted to `O`; the divisors are equal). -/
theorem restrictEquiv_padE_lowerIdealWBM_emptyPrefix (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₁ Y₀ : CMfd.{u} n}
    (P : BlowupTower X Y₁) (hP : IsEmptyTower P) (H₀ : BlowupTower Y₁ Y₀)
    (hT : IsGeoTestTower (barMarked 𝔍) (P.append H₀)) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (O : Opens Y₀)
    (hO : (O : Set Y₀) ⊆ (P.append H₀).proj ⁻¹' (U : Set X)) (s : ℕ) (S : List (Set Y₀))
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) :
    RestrictEquiv
      (padE (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ S)) P.length)
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s u (P.append H₀) S)) := by
  obtain ⟨hRE, Zs, hZ, hE⟩ := restrictEquiv_lowerIdealWBM_emptyPrefix 𝔍 h𝔍 hd P hP H₀ hT U hu O hO s S hS
  have hlen : Zs.length = P.length := by
    have h := congrArg List.length hE
    rw [List.length_append, length_E_pullback_lowerIdealWBM, length_E_pullback_lowerIdealWBM,
      BlowupTower.length_append] at h
    omega
  have hZrep : Zs = List.replicate P.length ∅ := List.eq_replicate_iff.mpr ⟨hlen, hZ⟩
  have hpad : ({ MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ S) with
          E := (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s u (P.append H₀) S)).E } :
        MarkedIdeal n O) =
      padE (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ S)) P.length := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
    show (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s u (P.append H₀) S)).E =
      List.replicate P.length ∅ ++ (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ S)).E
    rw [hE, hZrep]
  rw [hpad] at hRE
  exact hRE

end Pad

/-! ### The lower values -/

section Value

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (Rm : ℕ → ResolutionInvariant.{u, v} n (k - 1) Λ)
  (hfam : ∀ (m m' : ℕ) {X : CMfd.{u} n} (L : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y),
    (Rm (m + m')).inv L T y = (Rm m).inv (padE L m') T y)

include hfam in
/-- **The lower value of `𝔍_P` (for `Rm (m + |P|)`) through a lower ideal of `𝔍` (for `Rm m`)** (both levels; `P` with only
empty centres): in the situation of `HironakaG11PresM8EmptyCore.lowerValueG_emptyPrefix_of`, given the independence of the
hypersurface of maximal contact for `𝔍_P` and `Rm (m + |P|)`. -/
theorem lowerValueG_emptyPrefix_pad (m : ℕ) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    {Y₁ Y₀ Z : CMfd.{u} n} (P : BlowupTower X Y₁) (hP : IsEmptyTower P)
    (hTIP : TangentIndepBM (geoTransformAlong 𝔍 P) (Rm (m + P.length))) (H₀ : BlowupTower Y₁ Y₀)
    (T₁ : BlowupTower Y₀ Z) (hT : IsGeoTestTower (barMarked 𝔍) ((P.append H₀).append T₁)) {s : ℕ} {z : Z}
    (ha : T₁.proj z ∈ (geoTransformAlong (barMarked 𝔍) (P.append H₀)).cosupp)
    (hl : level 𝔍 (P.append H₀) (T₁.proj z) = s)
    (hD' : LowerDataG (Rm (m + P.length)) (geoTransformAlong 𝔍 P) (maskBM (geoTransformAlong 𝔍 P))
      (lowerBM (geoTransformAlong 𝔍 P)) s H₀ T₁ z)
    (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (O : Opens Y₀)
    (hO : (O : Set Y₀) ⊆ (P.append H₀).proj ⁻¹' (U : Set X)) (hzO : T₁.proj z ∈ O)
    (hdom : IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM 𝔍 s u (P.append H₀) (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))))
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 s u (P.append H₀) (throughMembers 𝔍 (P.append H₀) (T₁.proj z))))
      ((Rm m).inv (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 s u (P.append H₀) (throughMembers 𝔍 (P.append H₀) (T₁.proj z))))) (restrict O T₁))
    (hcos : (⟨z, hzO⟩ : openPreimage T₁ O) ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 s u (P.append H₀) (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))) (restrict O T₁)).cosupp) :
    lowerValueG (Rm (m + P.length)) (geoTransformAlong 𝔍 P) (maskBM (geoTransformAlong 𝔍 P))
        (lowerBM (geoTransformAlong 𝔍 P)) s H₀ T₁ z =
      (((Rm m).inv (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 s u (P.append H₀) (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))) (restrict O T₁) ⟨z, hzO⟩ :
          Λ) : WithTop Λ) := by
  have hPt : IsGeoTestTower 𝔍 P := isGeoTestTower_of_isEmptyTower 𝔍 P hP
  have hwfP := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔍 P hPt
  have hdP : 1 ≤ (geoTransformAlong 𝔍 P).d := by rw [d_geoTransformAlong]; exact hd
  obtain ⟨hT₀J, -⟩ := (isGeoTestTower_append_iff _ (P.append H₀) T₁).mp hT
  have hT₀ : IsGeoTestTower (barMarked (geoTransformAlong 𝔍 P)) H₀ :=
    (ContactEmptyPrefix.isGeoTestTower_barMarked_geoTransformAlong_iff 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd P
      hP H₀).mpr hT₀J
  have hT' : IsGeoTestTower (barMarked (geoTransformAlong 𝔍 P)) (H₀.append T₁) :=
    (ContactEmptyPrefix.isGeoTestTower_barMarked_geoTransformAlong_iff 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd P
      hP _).mpr (by rw [← BlowupTower.append_assoc]; exact hT)
  have ha' : T₁.proj z ∈ (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) H₀).cosupp := by
    rw [(StepOneEmptyPrefix.restrictEquiv_barMarked_append 𝔍 h𝔍 hd P hP H₀ hT₀J).cosupp_eq]
    exact ha
  have hl' : level (geoTransformAlong 𝔍 P) H₀ (T₁.proj z) = s := by
    rw [StepOneEmptyPrefix.level_emptyPrefix 𝔍 P hP H₀]
    exact hl
  -- the padded comparison on `O`
  have hthr := throughMembers_emptyPrefix 𝔍 P hP H₀ (T₁.proj z)
  have hS := HironakaG11InvBMLowerTailSucc.isClosedSubmanifold_of_mem_throughMembers 𝔍 h𝔍 hn (P.append H₀) hT₀J
    (T₁.proj z)
  have hRE := restrictEquiv_padE_lowerIdealWBM_emptyPrefix 𝔍 h𝔍 hd P hP H₀ hT₀J U hu O hO s _ hS
  have hcoh₃ : (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀
      (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))).ideal.IsCoherent := by
    have h := isCoherent_lowerIdealWBM (geoTransformAlong 𝔍 P) hwfP hdP hn s (u ∘ P.proj) H₀ hT₀ (T₁.proj z)
    rw [hthr] at h
    exact GermIdealPullbackCalculus.isCoherent_pullback (contMDiff_subtype_val (U := O)) h
  have hE₁₂ := InvDomainRebase.restrictEquiv_symm hRE
  have hdom₂ := InvDomainRebase.isInvDomain_of_restrictEquiv hdom hE₁₂ hcoh₃
  have hcan₂ := InvDomainRebase.isCanonical_of_restrictEquiv (Rm m) hdom hdom₂ hE₁₂ _ hcan
  have v₁ := (Rm m).representative _ _ hdom hdom₂ hE₁₂ _ hcan ⟨z, hzO⟩ hcos
  have hdom₃ : IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))) :=
    isInvDomain_withE_of_sublist hdom₂ (List.sublist_append_right _ _)
  have hcan₃ : IsCanonical (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ (throughMembers 𝔍 (P.append H₀) (T₁.proj z))))
      ((Rm (m + P.length)).inv (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))))
      (restrict O T₁) := by
    refine (HironakaG11InvBMEmptyMemberStep.isCanonical_iff_of_eq (X := CMfd.of (n := n) O)
      (fun T y => (Rm m).inv (padE (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ (throughMembers 𝔍 (P.append H₀) (T₁.proj z))))
          P.length) T y)
      (fun T y => (Rm (m + P.length)).inv (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))) T y)
      (fun T => funext fun y => (hfam m P.length (X := CMfd.of (n := n) O) _ T y).symm)
      (fun T => DropMembers.cosupp_geoTransformAlong_withE _ _ T) _).mp hcan₂
  have v₂ := hfam m P.length (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O → Y₀)
    (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ (throughMembers 𝔍 (P.append H₀) (T₁.proj z))))
    (restrict O T₁) ⟨z, hzO⟩
  -- the anchor for `𝔍_P` with the tangent direction `u ∘ p_P`
  have hu' : IsTangentDirectionAlong (geoTransformAlong 𝔍 P).N (geoTransformAlong 𝔍 P).ideal (geoTransformAlong 𝔍 P).d
      (P.proj ⁻¹' (U : Set X)) (u ∘ P.proj) := by
    rw [d_geoTransformAlong]
    exact (ContactEmptyPrefix.isTangentDirectionAlong_geoTransformAlong_of_isEmptyTower 𝔍 h𝔍.isClosedSubmanifold_N
      h𝔍.isCoherent hu P hP).1
  have hOU : (O : Set Y₀) ⊆ H₀.proj ⁻¹' (P.proj ⁻¹' (U : Set X)) := fun p hp => by
    have h := hO hp
    rw [mem_preimage, BlowupTower.proj_append] at h
    exact h
  have hdom₃' : IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀
        (throughMembers (geoTransformAlong 𝔍 P) H₀ (T₁.proj z)))) := by
    rw [hthr]
    exact hdom₃
  have hcan₃' : IsCanonical (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀
        (throughMembers (geoTransformAlong 𝔍 P) H₀ (T₁.proj z))))
      ((Rm (m + P.length)).inv (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀
          (throughMembers (geoTransformAlong 𝔍 P) H₀ (T₁.proj z))))) (restrict O T₁) := by
    rw [hthr]
    exact hcan₃
  have key := lowerValueG_eq_of_tangent (geoTransformAlong 𝔍 P) (Rm (m + P.length)) hTIP H₀ T₁ hT' ha' hl' hD' hu' O
    hOU hzO hdom₃' hcan₃'
  rw [key]
  congr 1
  rw [hthr]
  exact v₂.trans v₁.symm

include hfam in
/-- **The lower values across an empty prefix, the run inside the tail** (family form, both levels). -/
theorem lowerValueG_emptyPrefix_inside_pad (m : ℕ) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    {Y₁ Y₀ Z : CMfd.{u} n} (P : BlowupTower X Y₁) (hP : IsEmptyTower P)
    (hTIP : TangentIndepBM (geoTransformAlong 𝔍 P) (Rm (m + P.length))) (H₀ : BlowupTower Y₁ Y₀)
    (T₁ : BlowupTower Y₀ Z) (hT : IsGeoTestTower (barMarked 𝔍) ((P.append H₀).append T₁)) {s : ℕ} {z : Z}
    (ha : T₁.proj z ∈ (geoTransformAlong (barMarked 𝔍) (P.append H₀)).cosupp)
    (hl : level 𝔍 (P.append H₀) (T₁.proj z) = s)
    (hD : LowerDataG (Rm m) 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s (P.append H₀) T₁ z)
    (hD' : LowerDataG (Rm (m + P.length)) (geoTransformAlong 𝔍 P) (maskBM (geoTransformAlong 𝔍 P))
      (lowerBM (geoTransformAlong 𝔍 P)) s H₀ T₁ z) :
    lowerValueG (Rm m) 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s (P.append H₀) T₁ z =
      lowerValueG (Rm (m + P.length)) (geoTransformAlong 𝔍 P) (maskBM (geoTransformAlong 𝔍 P))
        (lowerBM (geoTransformAlong 𝔍 P)) s H₀ T₁ z := by
  obtain ⟨h, hdom, hcan, hcos⟩ := hD
  rw [lowerValueG_eq_of_mem (Rm m) 𝔍 (maskBM 𝔍) (lowerBM 𝔍) h]
  have hw := isTangentDirectionAlong_tangentChoice_of_nonempty 𝔍
    ⟨_, maskBM_subset_tangent 𝔍 s (P.append H₀) _ h⟩
  have hLeq : lowerBM 𝔍 s (P.append H₀) (T₁.proj z) =
      MarkedIdeal.pullback (Subtype.val : maskBM 𝔍 s (P.append H₀) (T₁.proj z) → Y₀)
        (lowerIdealWBM 𝔍 s (tangentChoice 𝔍 ((P.append H₀).proj (T₁.proj z))).2 (P.append H₀)
          (throughMembers 𝔍 (P.append H₀) (T₁.proj z))) := by
    rw [lowerBM_eq, lowerIdealBM_eq_lowerIdealWBM]
  rw [hLeq] at hdom hcan hcos ⊢
  exact (lowerValueG_emptyPrefix_pad 𝔍 Rm hfam m h𝔍 hd hn P hP hTIP H₀ T₁ hT ha hl hD' ⟨_, hw.isOpen⟩ hw _
    (maskBM_subset_tangent 𝔍 s (P.append H₀) _) h hdom hcan hcos).symm

include hfam in
/-- **The lower values across an empty prefix, the run covering the tail and the prefix** (family form, both levels). -/
theorem lowerValueG_emptyPrefix_cover_pad (m : ℕ) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₁ Y : CMfd.{u} n} (P : BlowupTower X Y₁) (hP : IsEmptyTower P)
    (hTIP : TangentIndepBM (geoTransformAlong 𝔍 P) (Rm (m + P.length))) (T₁ : BlowupTower Y₁ Y)
    (hT : IsGeoTestTower (barMarked 𝔍) (P.append T₁)) {s : ℕ} {z : Y}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) (P.append T₁)).cosupp)
    (hreg₀ : stepRegime 𝔍 s .refl ((P.append T₁).proj z)) (hreg₁ : stepRegime 𝔍 s P (T₁.proj z))
    (hD : LowerDataG (Rm m) 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s .refl (P.append T₁) z)
    (hD' : LowerDataG (Rm (m + P.length)) (geoTransformAlong 𝔍 P) (maskBM (geoTransformAlong 𝔍 P))
      (lowerBM (geoTransformAlong 𝔍 P)) s .refl T₁ z) :
    lowerValueG (Rm m) 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s .refl (P.append T₁) z =
      lowerValueG (Rm (m + P.length)) (geoTransformAlong 𝔍 P) (maskBM (geoTransformAlong 𝔍 P))
        (lowerBM (geoTransformAlong 𝔍 P)) s .refl T₁ z := by
  obtain ⟨h₁, hdom₁, hcan₁, hcos₁⟩ := hD
  rw [lowerValueG_eq_of_mem (Rm m) 𝔍 _ _ h₁]
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨hPJ, hT₁J⟩ := (isGeoTestTower_append_iff _ P T₁).mp hT
  -- (i) the restricted concatenation
  obtain ⟨hcanb, hval⟩ := StepOneCompare.inv_restrict_append (Rm m) (maskBM 𝔍 s .refl ((P.append T₁).proj z)) hdom₁
    P T₁ hcan₁
  have hp₁ : (P.append T₁).proj z = P.proj (T₁.proj z) := by rw [BlowupTower.proj_append]; rfl
  have hq : z ∈ openPreimage T₁ (openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z))) :=
    show P.proj (T₁.proj z) ∈ maskBM 𝔍 s .refl ((P.append T₁).proj z) from hp₁ ▸ h₁
  obtain ⟨hcosb, hvalb⟩ := hval z h₁ hq hcos₁
  rw [← hvalb]
  -- (ii) re-basing along `P`, whose centres are empty
  have hT' : IsGeoTestTower (barMarked 𝔍) ((BlowupTower.refl : BlowupTower X X).append P) := by
    rw [BlowupTower.refl_append]
    exact hPJ
  have hb₀ : (P.append T₁).proj z ∈ (geoTransformAlong (barMarked 𝔍) (BlowupTower.refl : BlowupTower X X)).cosupp :=
    proj_mem_cosupp_of_mem_cosupp hJ.isClosedSubmanifold_N hJ.isCoherent (P.append T₁) hT hz
  have hM : CentresAvoid (maskBM 𝔍 s .refl ((P.append T₁).proj z)) P :=
    ContactLowerValue.centresAvoid_of_isEmptyTower _ P hP
  obtain ⟨hdomS, hcanS, hvalS⟩ := HironakaG11InvBMRebase.inv_rebase_lowerBM 𝔍 (Rm m) h𝔍 hd hn hmax .refl P hT' hb₀
    hreg₀.1 hM ⟨T₁.proj z, hq⟩ hp₁.symm hdom₁
    (restrict (openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z))) T₁) hcanb
  rw [hvalS ⟨z, hq⟩ hcosb]
  have hEqR := HironakaG11InvBMRebase.restrictEquiv_rebase_lowerBM 𝔍 h𝔍 hd hn hmax .refl P hT' hb₀ hreg₀.1 hM
    ⟨T₁.proj z, hq⟩ hp₁.symm
  have he : IsEmptyTower (restrict (maskBM 𝔍 s .refl ((P.append T₁).proj z)) P) :=
    (isEmptyTower_restrict_iff _ P).mpr hM
  have hdom₀ := InvDomainRebase.isInvDomain_geoTransformAlong_of_isEmptyTower hdom₁ _ he
  have hcosS := (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hEqR
    hdom₀.isWellFormed.isClosedSubmanifold_N.1 hdom₀.isWellFormed.isCoherent hdomS.isWellFormed.isCoherent
    (restrict (openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z))) T₁)).1
  have hcos₂ : (⟨z, hq⟩ : openPreimage T₁ (openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z)))) ∈
      (geoTransformAlong (MarkedIdeal.pullback
        (Subtype.val : openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z)) → Y₁)
        (lowerIdealBM 𝔍 s ((BlowupTower.refl : BlowupTower X X).append P) (T₁.proj z)))
        (restrict (openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z))) T₁)).cosupp := by
    rw [← hcosS, ← geoTransformAlong_append]
    exact hcosb
  rw [BlowupTower.refl_append] at hdomS hcanS hcos₂ ⊢
  rw [lowerIdealBM_eq_lowerIdealWBM] at hdomS hcanS hcos₂ ⊢
  -- (iii) the comparison with `H₀ = refl`, through the tangent direction chosen at the base point
  have hU : P.proj (T₁.proj z) ∈ (tangentChoice 𝔍 (P.proj (T₁.proj z))).1 := by
    have h := maskBM_subset_tangent 𝔍 s .refl _ h₁
    rw [hp₁] at h
    exact h
  have hw := isTangentDirectionAlong_tangentChoice_of_nonempty 𝔍 ⟨_, hU⟩
  have hO : ((openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z)) : Opens Y₁) : Set Y₁) ⊆
      (P.append (BlowupTower.refl : BlowupTower Y₁ Y₁)).proj ⁻¹' (tangentChoice 𝔍 (P.proj (T₁.proj z))).1 :=
    fun y hy => by
      have h := maskBM_subset_tangent 𝔍 s .refl ((P.append T₁).proj z) hy
      rw [hp₁] at h
      exact h
  have haP : T₁.proj z ∈ (geoTransformAlong (barMarked 𝔍) (P.append (BlowupTower.refl : BlowupTower Y₁ Y₁))).cosupp := by
    obtain ⟨hNP, hcP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
      P hPJ
    have hz' : z ∈ (geoTransformAlong (geoTransformAlong (barMarked 𝔍) P) T₁).cosupp := by
      rw [← geoTransformAlong_append]
      exact hz
    exact proj_mem_cosupp_of_mem_cosupp hNP hcP T₁ hT₁J hz'
  exact (lowerValueG_emptyPrefix_pad 𝔍 Rm hfam m h𝔍 hd hn P hP hTIP .refl T₁ hT haP hreg₁.1 hD' ⟨_, hw.isOpen⟩ hw _ hO
    hq hdomS hcanS hcos₂).symm

end Value

/-! ### Property (4') for the family value -/

section EmptyPrefix

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (Rm : ℕ → ResolutionInvariant.{u, v} n (k - 1) Λ)
  (hfam : ∀ (m m' : ℕ) {X : CMfd.{u} n} (L : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y),
    (Rm (m + m')).inv L T y = (Rm m).inv (padE L m') T y)

include hfam in
/-- **The values agree along `P T₁` (for `Rm m`) and `T₁` (for `Rm (m + |P|)`)** when both are canonical segments (`P` empty;
given `TangentIndepBM` for `𝔍` with `Rm m` and for `𝔍_P` with `Rm (m + |P|)`). -/
theorem stepOneInvBM_emptyPrefix_eq_pad (m : ℕ) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) (hTI : TangentIndepBM 𝔍 (Rm m))
    {Y₁ : CMfd.{u} n} (P : BlowupTower X Y₁) (hP : IsEmptyTower P)
    (hTIP : TangentIndepBM (geoTransformAlong 𝔍 P) (Rm (m + P.length))) {Y : CMfd.{u} n} (T₁ : BlowupTower Y₁ Y)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM (Rm m) 𝔍) (P.append T₁))
    (hcan' : IsCanonical (barMarked (geoTransformAlong 𝔍 P)) (stepOneInvBM (Rm (m + P.length)) (geoTransformAlong 𝔍 P))
      T₁) {z : Y}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) (P.append T₁)).cosupp) :
    stepOneInvBM (Rm m) 𝔍 (P.append T₁) z = stepOneInvBM (Rm (m + P.length)) (geoTransformAlong 𝔍 P) T₁ z := by
  have hAC : AnchorChangeBM 𝔍 (Rm m) := anchorChangeBM_of_tangentIndepBM 𝔍 (Rm m) hTI
  have hACP : AnchorChangeBM (geoTransformAlong 𝔍 P) (Rm (m + P.length)) :=
    anchorChangeBM_of_tangentIndepBM _ (Rm (m + P.length)) hTIP
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  obtain ⟨h𝔍', hd', hmax', hk'⟩ := StepOneEmptyPrefix.hypotheses_emptyPrefix 𝔍 h𝔍 hd hmax hk P hP
  have hT := isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 (Rm m) hAC h𝔍 hd hn hmax hk _ hcan
  have hT' := isGeoTestTower_of_isCanonical_stepOneInvBM _ (Rm (m + P.length)) hACP h𝔍' hd' hn hmax' hk' _ hcan'
  have hPJ : IsGeoTestTower (barMarked 𝔍) P := ((isGeoTestTower_append_iff _ _ T₁).mp hT).1
  have hEqT := StepOneEmptyPrefix.restrictEquiv_barMarked_append 𝔍 h𝔍 hd P hP T₁ hT
  have hz' : z ∈ (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) T₁).cosupp := by
    rw [hEqT.cosupp_eq]
    exact hz
  have hD := hasLowerDataG_of_isCanonical 𝔍 (Rm m) hAC h𝔍 hd hn hmax hk _ hT hcan z hz
  have hD' := hasLowerDataG_of_isCanonical _ (Rm (m + P.length)) hACP h𝔍' hd' hn hmax' hk' _ hT' hcan' z hz'
  have hG : ∀ {Y₀ Z : CMfd.{u} n} (T : BlowupTower Y₁ Y₀) (C : Set Y₀) (π : Z → Y₀) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower (barMarked 𝔍) (P.append (.step T C π hπ)) → IsGeoTestTower (barMarked 𝔍) (P.append T) :=
    fun _ _ _ _ h => h.1
  have hQ : ∀ (s : ℕ) {Y₀ : CMfd.{u} n} (H₀ : BlowupTower Y₁ Y₀) (y : Y₀),
      IsGeoTestTower (barMarked 𝔍) (P.append H₀) →
        (stepRegime 𝔍 s (P.append H₀) y ↔ stepRegime (geoTransformAlong 𝔍 P) s H₀ y) :=
    fun s _ H₀ y hH => (StepOneEmptyPrefix.stepRegime_emptyPrefix_iff 𝔍 h𝔍 hd P hP H₀ hH s y).symm
  have hl := StepOneEmptyPrefix.level_emptyPrefix 𝔍 P hP T₁ z
  unfold stepOneInvBM
  by_cases hs : IsSpecial 𝔍 (P.append T₁) z
  · have hs' := (StepOneEmptyPrefix.isSpecial_emptyPrefix_iff 𝔍 h𝔍 hd P hP T₁ hT z).mpr hs
    rw [stepOneInvG_of_isSpecial (Rm m) 𝔍 _ _ _ hs, stepOneInvG_of_isSpecial (Rm (m + P.length)) _ _ _ _ hs', hl]
  · have hs' : ¬ IsSpecial (geoTransformAlong 𝔍 P) T₁ z :=
      fun h => hs ((StepOneEmptyPrefix.isSpecial_emptyPrefix_iff 𝔍 h𝔍 hd P hP T₁ hT z).mp h)
    have hregP := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 _ hT hz hs
    specialize hD hs
    specialize hD' hs'
    rw [stepOneInvG_of_not_isSpecial (Rm m) 𝔍 _ _ _ hs, stepOneInvG_of_not_isSpecial (Rm (m + P.length)) _ _ _ _ hs']
    rw [hl] at hD' ⊢
    obtain ⟨s, hsdef⟩ : ∃ s, level 𝔍 (P.append T₁) z = s := ⟨_, rfl⟩
    have hreg' : stepRegime (geoTransformAlong 𝔍 P) s T₁ z := ⟨hl.trans hsdef, hs'⟩
    rw [hsdef] at hD hD' hregP ⊢
    rcases (regimeRun_le_length (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z).lt_or_eq with hlt | heq
    · -- the run stays inside `T₁`
      have hr := StepOneEmptyPrefix.regimeRun_append_of_lt (stepRegime 𝔍 s) (stepRegime (geoTransformAlong 𝔍 P) s) P
        (fun H₀ => IsGeoTestTower (barMarked 𝔍) (P.append H₀)) hG (hQ s) T₁ z hT hlt
      rw [hr] at hD hregP ⊢
      simp only [head, tail] at hD hD' hregP ⊢
      rw [StepOneEmptyPrefix.split_append_of_le P T₁ _ hlt.le] at hD hregP ⊢
      dsimp only at hD hregP ⊢
      have hT₀₁ : IsGeoTestTower (barMarked 𝔍)
          ((P.append (head T₁ (regimeRun (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z))).append
            (tail T₁ (regimeRun (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z))) := by
        rw [BlowupTower.append_assoc, head_append_tail]
        exact hT
      congr 2
      exact lowerValueG_emptyPrefix_inside_pad 𝔍 Rm hfam m h𝔍 hd hn P hP hTIP _ _ hT₀₁ hregP.2 hregP.1.1 hD hD'
    · -- the run covers `T₁`, then all of `P`
      have hbase := StepOneEmptyPrefix.regime_base_of_regimeRun_eq (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z
        hreg' heq
      have hbaseP : stepRegime 𝔍 s P (T₁.proj z) := (hQ s .refl (T₁.proj z) hPJ).mpr hbase
      have hstep : ∀ {Y' Z' : CMfd.{u} n} (T : BlowupTower X Y') (π : Z' → Y') (hπ : IsBlowupAlong n (∅ : Set Y') π),
          IsEmptyTower T → ∀ w : Z', stepRegime 𝔍 s (.step T ∅ π hπ) w → stepRegime 𝔍 s T (π w) := by
        intro Y' Z' T π hπ hTe w hw
        have hTt : IsGeoTestTower (barMarked 𝔍) T := isGeoTestTower_of_isEmptyTower _ T hTe
        have hl' := level_step_of_notMem 𝔍 hE T ∅ π hπ (notMem_empty (π w))
        have hs'' := isSpecial_step_iff_of_notMem 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hE T hTt ∅ π hπ
          (notMem_empty (π w))
        exact ⟨hl'.symm.trans hw.1, fun h => hw.2 (hs''.mpr h)⟩
      have hrP := StepOneEmptyPrefix.regimeRun_eq_length_of_isEmptyTower (stepRegime 𝔍 s) hstep P hP _ hbaseP
      have hr := StepOneEmptyPrefix.regimeRun_append_of_eq (stepRegime 𝔍 s) (stepRegime (geoTransformAlong 𝔍 P) s) P
        (fun H₀ => IsGeoTestTower (barMarked 𝔍) (P.append H₀)) hG (hQ s) T₁ z hT heq
      have hreg₀ : stepRegime 𝔍 s .refl ((P.append T₁).proj z) := by
        have hregT : stepRegime 𝔍 s (P.append T₁) z := ⟨hsdef, hs⟩
        have hrun : regimeRun (stepRegime 𝔍 s) (P.append T₁) z = (P.append T₁).length := by
          rw [hr, hrP, BlowupTower.length_append]
          omega
        exact StepOneEmptyPrefix.regime_base_of_regimeRun_eq (stepRegime 𝔍 s) (P.append T₁) z hregT hrun
      rw [hr, hrP] at hD ⊢
      rw [heq] at hD' ⊢
      simp only [head, tail] at hD hD' ⊢
      rw [StepOneEmptyPrefix.split_of_length_le (P.append T₁) _ (by rw [BlowupTower.length_append]; omega)] at hD ⊢
      rw [StepOneEmptyPrefix.split_of_length_le T₁ _ le_rfl] at hD' ⊢
      dsimp only at hD hD' ⊢
      congr 2
      exact lowerValueG_emptyPrefix_cover_pad 𝔍 Rm hfam m h𝔍 hd hn hmax P hP hTIP T₁ hT hz hreg₀ hbaseP hD hD'

include hfam in
/-- **Property (4') for the family value** (`P` with only empty centres, `m` arbitrary): if `P T₁` is a canonical segment of
`stepOneInvBM (Rm m) 𝔍`, then `T₁` is a canonical segment of `stepOneInvBM (Rm (m + |P|)) 𝔍_P` and the values agree on the
cosupport of `J̄_{P T₁}` (given `TangentIndepBM` for `𝔍` with `Rm m` and for `𝔍_P` with `Rm (m + |P|)`). -/
theorem stepOneInvBM_emptyPrefix_pad (m : ℕ) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) (hTI : TangentIndepBM 𝔍 (Rm m))
    {Y₁ : CMfd.{u} n} (P : BlowupTower X Y₁) (hP : IsEmptyTower P)
    (hTIP : TangentIndepBM (geoTransformAlong 𝔍 P) (Rm (m + P.length))) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₁ Y), IsCanonical (barMarked 𝔍) (stepOneInvBM (Rm m) 𝔍) (P.append T₁) →
      IsCanonical (barMarked (geoTransformAlong 𝔍 P)) (stepOneInvBM (Rm (m + P.length)) (geoTransformAlong 𝔍 P)) T₁ ∧
        ∀ z ∈ (geoTransformAlong (barMarked 𝔍) (P.append T₁)).cosupp,
          stepOneInvBM (Rm m) 𝔍 (P.append T₁) z = stepOneInvBM (Rm (m + P.length)) (geoTransformAlong 𝔍 P) T₁ z
  | _, .refl, hcan => ⟨trivial, fun _ hz =>
      stepOneInvBM_emptyPrefix_eq_pad 𝔍 Rm hfam m h𝔍 hd hn hmax hk hTI P hP hTIP .refl hcan trivial hz⟩
  | _, .step T C π hπ, hcan => by
      have hAC : AnchorChangeBM 𝔍 (Rm m) := anchorChangeBM_of_tangentIndepBM 𝔍 (Rm m) hTI
      have hcan₀ := hcan
      obtain ⟨hcanT, hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvBM (Rm m) 𝔍) (P.append T) ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvBM (Rm m) 𝔍 (P.append T))
            (geoTransformAlong (barMarked 𝔍) (P.append T)).cosupp) := hcan
      obtain ⟨hcan'T, hval⟩ := stepOneInvBM_emptyPrefix_pad m h𝔍 hd hn hmax hk hTI P hP hTIP T hcanT
      have hT := isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 (Rm m) hAC h𝔍 hd hn hmax hk _ hcanT
      have hEqT := StepOneEmptyPrefix.restrictEquiv_barMarked_append 𝔍 h𝔍 hd P hP T hT
      have hcan'S : IsCanonical (barMarked (geoTransformAlong 𝔍 P))
          (stepOneInvBM (Rm (m + P.length)) (geoTransformAlong 𝔍 P)) (.step T C π hπ) := by
        refine (⟨hcan'T, hC.imp id fun h => h.trans ?_⟩ :
          IsCanonical (barMarked (geoTransformAlong 𝔍 P)) (stepOneInvBM (Rm (m + P.length)) (geoTransformAlong 𝔍 P)) T ∧
            (C = ∅ ∨ C = maxLocus (stepOneInvBM (Rm (m + P.length)) (geoTransformAlong 𝔍 P) T)
              (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) T).cosupp))
        rw [hEqT.cosupp_eq]
        exact ResolutionInvariantExt.maxLocus_congr hval
      exact ⟨hcan'S, fun _ hz =>
        stepOneInvBM_emptyPrefix_eq_pad 𝔍 Rm hfam m h𝔍 hd hn hmax hk hTI P hP hTIP _ hcan₀ hcan'S hz⟩

include hfam in
/-- **Property (4'), the field `emptyPrefix`** of `MaxOrderValue.IsMaxOrderValue` for the family value
`fun 𝔍 T y => stepOneInvBM (Rm 𝔍.E.length) 𝔍 T y` (lane G11B's shape, I-1368 C-0004): given the independence of the
hypersurface of maximal contact for `𝔍` with `Rm |𝔍.E|` and for every transform `𝔍_P` along a tower with only empty centres with
`Rm |𝔍_P.E|`. -/
theorem emptyPrefix_field (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    (hTI : TangentIndepBM 𝔍 (Rm 𝔍.E.length))
    (hTIP : ∀ {Y₁ : CMfd.{u} n} (P : BlowupTower X Y₁), IsEmptyTower P →
      TangentIndepBM (geoTransformAlong 𝔍 P) (Rm (geoTransformAlong 𝔍 P).E.length))
    {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (h₀ : IsEmptyTower T₀)
    (hcan : IsCanonical 𝔍 (fun {Y} T y => stepOneInvBM (Rm 𝔍.E.length) 𝔍 (Y := Y) T y) (T₀.append T₁)) :
    ∀ z ∈ (geoTransformAlong 𝔍 (T₀.append T₁)).cosupp,
      stepOneInvBM (Rm 𝔍.E.length) 𝔍 (T₀.append T₁) z =
        stepOneInvBM (Rm (geoTransformAlong 𝔍 T₀).E.length) (geoTransformAlong 𝔍 T₀) T₁ z := by
  intro z hz
  have hAC : AnchorChangeBM 𝔍 (Rm 𝔍.E.length) := anchorChangeBM_of_tangentIndepBM 𝔍 _ hTI
  have hlen : (geoTransformAlong 𝔍 T₀).E.length = 𝔍.E.length + T₀.length := length_E_geoTransformAlong 𝔍 T₀
  have hTIP' : TangentIndepBM (geoTransformAlong 𝔍 T₀) (Rm (geoTransformAlong 𝔍 T₀).E.length) := hTIP T₀ h₀
  rw [hlen] at hTIP' ⊢
  rw [← (HironakaG11InvBMBridge.isGeoTestTower_of_isCanonical (Rm 𝔍.E.length) 𝔍 hAC h hmax hn _ hcan).2.2] at hz
  exact (stepOneInvBM_emptyPrefix_pad 𝔍 Rm hfam 𝔍.E.length h.isWellFormed h.one_le_d hn hmax h.dimLE hTI T₀ h₀ hTIP'
    T₁ ((HironakaG11InvBMBridge.isCanonical_iff (Rm 𝔍.E.length) 𝔍 hAC h hmax hn _).mp hcan)).2 z hz

end EmptyPrefix


end

end Hironaka.HironakaG11PresM8EmptyPad
