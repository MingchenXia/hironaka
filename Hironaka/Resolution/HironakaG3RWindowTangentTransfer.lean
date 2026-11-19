import Hironaka.Resolution.HironakaG3RWindowLowerValue

/-! # O7a′, node N2a: canonicity of Step 1bb's lower tail transfers between tangent directions on a common window

Lane G3 (run 0080, round 2).  Blueprint: `hironaka-g3-r-window-tangent-transfer.tex`.
Plan: `work/hironaka-resume-20261111/G3/O7A-PRIME-PLAN.md` (§4 N2, §6).

The window lower data of `HironakaG3RWindowLowerValue.lowerValueL_zero_restrict_window` asks the lower tail to be a
canonical segment of Step 1bb's lower marked ideal on the trace window, built with the tangent direction chosen for the
GLOBAL marked ideal.  The side of `𝔍|_U` provides canonicity for ITS OWN tangent direction.  This module proves the bridge
on a common window: along a multiple test blow-up of `J̄`, if the restricted tail is canonical for the lower marked ideal
built with one tangent direction `u`, it is canonical for the one built with any other tangent direction `v` (both in the
domain), by induction on the tail -- the two transforms have the same cosupport (the trace of `cosupp J̄`), the values
agree on it along the common canonical prefix (the held tangent-change anchor
`StepOneTangentChange.inv_restrictedCoeffHom_eq_of_opens_disjoint`), so the maximum loci agree.

* `isCanonical_step_of_eq` (generic): one step of a canonical segment passes between two marked ideals with equal
  cosupports and equal values on it along the prefix;
* **`isCanonical_contactMarkedKept_tangent_transfer`** (N2a).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG3RWindowTangentTransfer

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CoefficientIdealRestriction HomogenizedIdealAlong MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  BlowupTowerIsomorphism ResolutionInvariantExt StepOneTangentChange ContactStageKept
  StepOneValue StepOneLowerDomain StepOneValueMasked
open HomogenizedGlueingTower (strictAlong)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### One canonical step between two marked ideals -/

section Generic

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- **One canonical step passes between two marked ideals** whose transforms along the prefix have the same cosupport
and the same values on it. -/
theorem isCanonical_step_of_eq {𝔪 𝔫 : MarkedIdeal n X} {f g : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (hT : IsCanonical 𝔫 g T)
    (hcos : (geoTransformAlong 𝔪 T).cosupp = (geoTransformAlong 𝔫 T).cosupp)
    (hval : ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, f T y = g T y)
    (h : C = ∅ ∨ C = maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp) :
    IsCanonical 𝔫 g T ∧ (C = ∅ ∨ C = maxLocus (g T) (geoTransformAlong 𝔫 T).cosupp) := by
  refine ⟨hT, ?_⟩
  rcases h with hC | hC
  · exact Or.inl hC
  · right
    rw [hC, ← hcos]
    exact maxLocus_congr hval

end Generic

/-! ### N2a: the tangent-direction transfer of canonicity on a common window -/

section Transfer

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Canonicity of Step 1bb's lower tail does not depend on the tangent direction** (O7a′, node N2a): let `𝔍` be well
formed with `d ≥ 1`, `u`, `v` tangent directions of `(𝔍.ideal|_N, d)` along `N` on `U₁`, `U₂`, and `W` an open set of the
last stage of `T₀` over `U₁ ∩ U₂` missing the original members, on which both lower marked ideals
`contactMarkedKept 𝔍 u T₀ W` and `contactMarkedKept 𝔍 v T₀ W` lie in the domain.  For every tail `T₁` with `T₀ T₁` a multiple
test blow-up of `J̄`: if `T₁|_W` is a canonical segment of the first, it is one of the second. -/
theorem isCanonical_contactMarkedKept_tangent_transfer (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X)
    (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {U₁ U₂ : Set X} {u v : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U₁ u) (hv : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U₂ v)
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (W : Opens Y₀)
    (hWU₁ : (W : Set Y₀) ⊆ T₀.proj ⁻¹' U₁) (hWU₂ : (W : Set Y₀) ⊆ T₀.proj ⁻¹' U₂)
    (hWE : ∀ H ∈ origMembers 𝔍 T₀, Disjoint (W : Set Y₀) H)
    (hdomu : IsInvDomain k (contactMarkedKept 𝔍 u T₀ W)) (hdomv : IsInvDomain k (contactMarkedKept 𝔍 v T₀ W)) :
    ∀ {Z : CMfd.{u} n} (T₁ : BlowupTower Y₀ Z), IsGeoTestTower (barMarked 𝔍) (T₀.append T₁) →
      IsCanonical (contactMarkedKept 𝔍 u T₀ W) (R.inv (contactMarkedKept 𝔍 u T₀ W)) (restrict W T₁) →
      IsCanonical (contactMarkedKept 𝔍 v T₀ W) (R.inv (contactMarkedKept 𝔍 v T₀ W)) (restrict W T₁)
  | _, .refl, _, _ => trivial
  | _, .step (Y := Y₁) T₁ C π hπ, hT, hcan => by
      obtain ⟨hT₀, hstep⟩ := (isGeoTestTower_append_iff _ T₀ (.step T₁ C π hπ)).mp hT
      have hT₁ : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁) :=
        (isGeoTestTower_append_iff _ T₀ T₁).mpr ⟨hT₀, hstep.1⟩
      have hcan' : IsCanonical (contactMarkedKept 𝔍 u T₀ W) (R.inv (contactMarkedKept 𝔍 u T₀ W)) (restrict W T₁) ∧
          (((Subtype.val : openPreimage T₁ W → _) ⁻¹' C) = ∅ ∨
            ((Subtype.val : openPreimage T₁ W → _) ⁻¹' C) = maxLocus (R.inv (contactMarkedKept 𝔍 u T₀ W)
              (restrict W T₁)) (geoTransformAlong (contactMarkedKept 𝔍 u T₀ W) (restrict W T₁)).cosupp) := hcan
      have ih := isCanonical_contactMarkedKept_tangent_transfer R 𝔍 h𝔍 hd hu hv T₀ W hWU₁ hWU₂ hWE hdomu hdomv
        T₁ hT₁ hcan'.1
      -- the two cosupports are the trace of `cosupp J̄_{T₀ T₁}`
      have hcu := (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent
        hd ⟨U₁, hu.isOpen⟩ hu T₀ T₁ hT₁ W hWU₁).2
      have hcv := (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent
        hd ⟨U₂, hv.isOpen⟩ hv T₀ T₁ hT₁ W hWU₂).2
      have hcos : (geoTransformAlong (contactMarkedKept 𝔍 u T₀ W) (restrict W T₁)).cosupp =
          (geoTransformAlong (contactMarkedKept 𝔍 v T₀ W) (restrict W T₁)).cosupp := hcu.trans hcv.symm
      -- the values agree on it (the tangent-change anchor at the base point)
      have hval : ∀ p ∈ (geoTransformAlong (contactMarkedKept 𝔍 u T₀ W) (restrict W T₁)).cosupp,
          R.inv (contactMarkedKept 𝔍 u T₀ W) (restrict W T₁) p =
            R.inv (contactMarkedKept 𝔍 v T₀ W) (restrict W T₁) p := by
        intro p hp
        have hpJ : (p : Y₁) ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp := by
          rw [hcu] at hp
          exact hp
        have hx : T₀.proj (T₁.proj (p : _)) ∈ 𝔍.cosupp := by
          have hJ := isWellFormed_barMarked 𝔍 h𝔍
          have h1 := proj_mem_cosupp_of_mem_cosupp hJ.isClosedSubmanifold_N hJ.isCoherent _ hT₁ hpJ
          rw [cosupp_barMarked 𝔍 h𝔍 hd, BlowupTower.proj_append] at h1
          exact h1
        have hpW : T₁.proj (p : _) ∈ W := p.2
        obtain ⟨O, hxO, hO⟩ := inv_restrictedCoeffHom_eq_of_opens_disjoint R 𝔍 h𝔍.isCoherent
          h𝔍.isClosedSubmanifold_N hd hx hu (hWU₁ hpW) hv (hWU₂ hpW)
        exact hO T₀ T₁ hT₁ W W hWU₁ hWU₂ hWE hWE hdomu hcan'.1 hdomv ih p p rfl hxO hpJ
      show IsCanonical (contactMarkedKept 𝔍 v T₀ W) (R.inv (contactMarkedKept 𝔍 v T₀ W)) (restrict W T₁) ∧
        (((Subtype.val : openPreimage T₁ W → _) ⁻¹' C) = ∅ ∨
          ((Subtype.val : openPreimage T₁ W → _) ⁻¹' C) = maxLocus (R.inv (contactMarkedKept 𝔍 v T₀ W)
            (restrict W T₁)) (geoTransformAlong (contactMarkedKept 𝔍 v T₀ W) (restrict W T₁)).cosupp)
      exact isCanonical_step_of_eq (restrict W T₁) _ ih hcos hval hcan'.2

end Transfer

end

end Hironaka.HironakaG3RWindowTangentTransfer
