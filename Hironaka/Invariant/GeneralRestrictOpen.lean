/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.GeneralTowerIso
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerSplitIso
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.CompanionReductionAlong
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.Invariant.ContactMarkedCanonical
import Hironaka.Invariant.GeneralAdmissible
import Hironaka.Invariant.GeneralCanonicalTail
import Hironaka.Invariant.GeneralCompare
import Hironaka.Invariant.GeneralValue
import Hironaka.Invariant.GeneralValueOrderZero
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainCompanion
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.MaxOrderValue
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Invariant.NonmonomialOrderTransport
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneNearby
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.StepOneTowerIso
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The general value under restriction to open sets: property (5)

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`: the resolution commutes with étale
morphisms, in particular with restriction to open sets; Bierstone--Milman 2008, Step II.

Let `𝔪` be a marked ideal of the domain (`0 < n`), `U ⊆ X` open and `T` a canonical segment of the general value
`genInv M 𝔪` (`M` a value function for the marked ideals of maximal order). At a point `p` over `U` of the cosupport
of positive order `o`, the general values of `𝔪|_U` along `T|_U` and of `𝔪` along `T` agree. The orders and runs
agree (`NonmonomialOrderRegime.regimeRun_ordRegime_restrict`); the split of `T|_U` at the run is isomorphic over
`id_U` to the restriction of the split of `T` (`BlowupTowerSplitIso.exists_isTowerIso_split_restrict`), so the
companion value of `p` for `𝔪|_U` is, by `GeneralTowerIso.value_companionOf_isTowerIso`, the value of `M` for the
companion ideal of `(𝔪_{T₀})|_V` (`V = T₀⁻¹U`) on its mask, which is the companion ideal `𝓞` of `𝔪_{T₀}` restricted
first to `V` and then to the trace of the mask `W` of `𝔪_{T₀}`
(`NonmonomialOrderTransport.mem_ordMask_restrict_iff`, `CompanionRebase.pullback_val_companionOf`). Two restrictions
are one (`value_restrict_restrict`: `MaxLocusLocal.isTowerIso_restrict_nestedOpens` and property (6) of `M`), to `W
∩ V`, and the value on `W ∩ V` is that on `W` (`GeneralCompare.value_restrict_nestedOpens`), the companion value of
`p` for `𝔪`. At order `0` this is `GeneralValueOrderZero.restrictOpen_field_of_nmOrd_eq_zero`.

## Main results

* `value_restrict_restrict`: restricting to `V` and then to the trace of `W` is restricting to `W ∩ V`, for a maximal-order value;
* **`genInv_restrict_of_pos`**: property (5) of the general value at positive order;
* **`restrictOpen_field`**: property (5) in the shape of the field `restrictOpen` of `ResolutionInvariantExt.ResolutionInvariant`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralRestrictOpen

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.CompanionRebase Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerIsomorphism Hironaka.StepOneTangentChange Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderTail Hironaka.NonmonomialOrderTransport Hironaka.InvDomainCompanion Hironaka.MaxOrderValue Hironaka.GeneralValue Hironaka.GeneralCompare Hironaka.GeneralCanonicalTail Hironaka.HomogenizedIdealAlong Hironaka.MaxLocusLocal Hironaka.GeneralTowerIso
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Two restrictions are one -/

section Nested

variable {Y₀ : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Restricting to `V` and then to the trace of `W` is restricting to `W ∩ V`**, for a value function of the marked ideals of
maximal order: if `𝓒|_W` lies in the domain, is of maximal order and `T₁|_W` is a canonical segment of it, then
`(𝓒|_V)|_{W ∩ V}` (the open `W ∩ V` seen in `V`) lies in the domain, is of maximal order, `(T₁|_V)|_{W ∩ V}` is a canonical
segment of it, and at the points of its cosupport the values are those of `𝓒|_W` along `T₁|_W`. -/
theorem value_restrict_restrict (hM : IsMaxOrderValue n k M) {𝓒 : MarkedIdeal n Y₀} (hN : IsClosedSubmanifold n 𝓒.N)
    (h𝓒 : 𝓒.ideal.IsCoherent) {V W : Opens Y₀} (hdom : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝓒))
    (hmax : IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝓒).N
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝓒).ideal (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝓒).d)
    {Z : CMfd.{u} n} (T₁ : BlowupTower Y₀ Z)
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝓒)
      (M (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝓒)) (restrict W T₁)) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : nestedOpens V (W ⊓ V) → V)
        (MarkedIdeal.pullback (Subtype.val : V → Y₀) 𝓒)) ∧
      IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : nestedOpens V (W ⊓ V) → V)
          (MarkedIdeal.pullback (Subtype.val : V → Y₀) 𝓒)).N
        (MarkedIdeal.pullback (Subtype.val : nestedOpens V (W ⊓ V) → V)
          (MarkedIdeal.pullback (Subtype.val : V → Y₀) 𝓒)).ideal
        (MarkedIdeal.pullback (Subtype.val : nestedOpens V (W ⊓ V) → V)
          (MarkedIdeal.pullback (Subtype.val : V → Y₀) 𝓒)).d ∧
      IsCanonical (MarkedIdeal.pullback (Subtype.val : nestedOpens V (W ⊓ V) → V)
          (MarkedIdeal.pullback (Subtype.val : V → Y₀) 𝓒))
        (M (MarkedIdeal.pullback (Subtype.val : nestedOpens V (W ⊓ V) → V)
          (MarkedIdeal.pullback (Subtype.val : V → Y₀) 𝓒))) (restrict (nestedOpens V (W ⊓ V)) (restrict V T₁)) ∧
      (∀ (x : openPreimage (restrict V T₁) (nestedOpens V (W ⊓ V)))
        (hxW : ((x : openPreimage T₁ V) : Z) ∈ openPreimage T₁ W),
        x ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : nestedOpens V (W ⊓ V) → V)
          (MarkedIdeal.pullback (Subtype.val : V → Y₀) 𝓒)) (restrict (nestedOpens V (W ⊓ V)) (restrict V T₁))).cosupp ↔
        (⟨((x : openPreimage T₁ V) : Z), hxW⟩ : openPreimage T₁ W) ∈
          (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝓒) (restrict W T₁)).cosupp) ∧
      ∀ (x : openPreimage (restrict V T₁) (nestedOpens V (W ⊓ V))) (hxW : ((x : openPreimage T₁ V) : Z) ∈ openPreimage T₁ W),
        x ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : nestedOpens V (W ⊓ V) → V)
          (MarkedIdeal.pullback (Subtype.val : V → Y₀) 𝓒)) (restrict (nestedOpens V (W ⊓ V)) (restrict V T₁))).cosupp →
        M (MarkedIdeal.pullback (Subtype.val : nestedOpens V (W ⊓ V) → V) (MarkedIdeal.pullback (Subtype.val : V → Y₀) 𝓒))
            (restrict (nestedOpens V (W ⊓ V)) (restrict V T₁)) x =
          M (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝓒) (restrict W T₁) ⟨((x : openPreimage T₁ V) : Z), hxW⟩ := by
  have hW₁W : W ⊓ V ≤ W := inf_le_left
  have hW₁V : W ⊓ V ≤ V := inf_le_right
  obtain ⟨hdom₁, hmax₁, hcan₁, hval₁⟩ := value_restrict_nestedOpens hM h𝓒 hW₁W hdom hmax T₁ hcan
  have hiso := isTowerIso_restrict_nestedOpens (X := Y₀) hW₁V T₁
  have heq : MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW₁V)
        (MarkedIdeal.pullback (Subtype.val : (W ⊓ V : Opens Y₀) → Y₀) 𝓒) =
      MarkedIdeal.pullback (Subtype.val : nestedOpens V (W ⊓ V) → V) (MarkedIdeal.pullback (Subtype.val : V → Y₀) 𝓒) :=
    ContactMarkedCanonical.pullback_pullback_of_comp_eq h𝓒 contMDiff_subtype_val
      (nestedOpensDiffeo (n := n) hW₁V).contMDiff contMDiff_subtype_val contMDiff_subtype_val fun _ => rfl
  have hdomN := InvDomainTowerAlong.isInvDomain_pullback (nestedOpensDiffeo (n := n) hW₁V) hdom₁
  obtain ⟨-, -, hmaxN, -⟩ := StepOneTowerIso.hypotheses_pullback (nestedOpensDiffeo (n := n) hW₁V) _
    hdom₁.isWellFormed hdom₁.one_le_d hmax₁ hdom₁.dimLE
  have hcanN := hM.isCanonical_of_isTowerIso hdom₁ hmax₁ (nestedOpensDiffeo (n := n) hW₁V) hiso hcan₁
  rw [heq] at hdomN hmaxN hcanN
  have hTt := hM.isGeoTestTower_of_isCanonical hdom₁ hmax₁ _ hcan₁
  have hcos := IsTowerIso.cosupp_geoTransformAlong (nestedOpensDiffeo (n := n) hW₁V)
    hdom₁.isWellFormed.isClosedSubmanifold_N hdom₁.isWellFormed.isCoherent hiso hTt
  rw [heq] at hcos
  have hTW := hM.isGeoTestTower_of_isCanonical hdom hmax _ hcan
  refine ⟨hdomN, hmaxN, hcanN, fun x hxW => ?_, fun x hxW hx => ?_⟩
  · rw [hcos, mem_preimage]
    exact StepOneNearby.mem_cosupp_restrict_nested_iff hN h𝓒 hW₁W T₁ hTW _
  have hx' := hx
  rw [hcos] at hx'
  have key := hM.towerIso (nestedOpensDiffeo (n := n) hW₁V) _ hdom₁ hmax₁ _ _ _ hiso hcan₁ x hx'
  rw [heq] at key
  rw [key]
  exact hval₁ _ hx'

end Nested

/-! ### Property (5) of the general value -/

section Restrict

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Property (5) of the general value at positive order**: for `𝔪` in the domain (`0 < n`), `U ⊆ X` open and `T` a canonical
segment of the general value which is a multiple test blow-up, at a point `p` over `U` of the cosupport of positive order, the
general value of `𝔪|_U` along `T|_U` is that of `𝔪` along `T`. -/
theorem genInv_restrict_of_pos (hM : IsMaxOrderValue n k M) (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    (hcan : IsCanonical 𝔪 (genInv M 𝔪) T) (p : openPreimage T U) (hp : (p : Y) ∈ (geoTransformAlong 𝔪 T).cosupp)
    (hpos : 0 < nmOrd (geoTransformAlong 𝔪 T) p) :
    genInv M (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T) p = genInv M 𝔪 T p := by
  obtain ⟨o, ho⟩ : ∃ o, nmOrd (geoTransformAlong 𝔪 T) p = o := ⟨_, rfl⟩
  have ho1 : 1 ≤ o := by omega
  have ho0 : o ≠ 0 := by omega
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hν : nmOrd (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)) p = o := by
    rw [geoTransformAlong_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T hT]
    exact (nmOrd_pullback_val hn hdomT.isWellFormed hdomT.isNonzeroAlongAt (openPreimage T U) p).trans ho
  rw [genInv_of_nmOrd_ne_zero M _ _ hν ho0, genInv_of_nmOrd_ne_zero M 𝔪 T ho ho0,
    regimeRun_ordRegime_restrict hn h o U T hT p]
  -- the lower data at `p`
  obtain ⟨hW, hdom, hmax, hcan₀, hcos₀⟩ := hasGenLowerData_of_isCanonical M hM hn h T hT hcan p hp o ho ho1
  -- the split of `T|_U` is the restriction of the split of `T`, up to isomorphisms over `id_U`
  obtain ⟨χ₀, h₀, h₁⟩ := BlowupTowerSplitIso.exists_isTowerIso_split_restrict U T (regimeRun (OrdRegime 𝔪 o) T p)
  obtain ⟨hT₀, -⟩ := (isGeoTestTower_iff_head_tail 𝔪 T (regimeRun (OrdRegime 𝔪 o) T p)).mp hT
  have hdomT₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h _ hT₀
  have hU : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) :=
    InvDomainTowerAlong.isInvDomain_pullback_val U h
  have hT₀U : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
      (restrict U (head T (regimeRun (OrdRegime 𝔪 o) T p))) :=
    isGeoTestTower_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent _ hT₀
  have hpb : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) = MarkedIdeal.pullback (Subtype.val : U → X) 𝔪 :=
    ContactCanonicalAlong.pullback_id _ hU.isWellFormed.isCoherent
  have hT₀' : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
      (head (restrict U T) (regimeRun (OrdRegime 𝔪 o) T p)) := by
    have h1 := (IsTowerIso.isGeoTestTower_iff (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      hU.isWellFormed.isClosedSubmanifold_N hU.isWellFormed.isCoherent h₀).mpr hT₀U
    rwa [hpb] at h1
  have hdomT₀' := InvDomainTowerAlong.isInvDomain_geoTransformAlong hU _ hT₀'
  -- the masks
  have hWiff : ∀ q, q ∈ ordMask (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
      (head (restrict U T) (regimeRun (OrdRegime 𝔪 o) T p))) o ↔
      χ₀ q ∈ nestedOpens (openPreimage (head T (regimeRun (OrdRegime 𝔪 o) T p)) U)
        (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T p))) o ⊓
          openPreimage (head T (regimeRun (OrdRegime 𝔪 o) T p)) U) := by
    intro q
    have h1 := mem_ordMask_isTowerIso_iff hn (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) hU h₀ hT₀U o q
    rw [hpb] at h1
    rw [h1, mem_ordMask_restrict_iff hn h U _ hT₀ o (χ₀ q)]
    exact ⟨fun h2 => ⟨h2, (χ₀ q).2⟩, fun h2 => h2.1⟩
  have hmem : (restrict (openPreimage (head T (regimeRun (OrdRegime 𝔪 o) T p)) U)
      (tail T (regimeRun (OrdRegime 𝔪 o) T p))).proj (BlowupTowerIsoTail.opensCongr (BlowupTowerSplitIso.openPreimage_head_tail U T
        (regimeRun (OrdRegime 𝔪 o) T p)) p) ∈
      nestedOpens (openPreimage (head T (regimeRun (OrdRegime 𝔪 o) T p)) U)
        (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T p))) o ⊓
          openPreimage (head T (regimeRun (OrdRegime 𝔪 o) T p)) U) := by
    refine ⟨?_, ?_⟩
    · rw [proj_restrict]; exact hW
    · rw [proj_restrict]
      exact (BlowupTowerIsoTail.opensCongr (BlowupTowerSplitIso.openPreimage_head_tail U T (regimeRun (OrdRegime 𝔪 o) T p)) p).2
  have hp' : (tail (restrict U T) (regimeRun (OrdRegime 𝔪 o) T p)).proj p ∈
      ordMask (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
        (head (restrict U T) (regimeRun (OrdRegime 𝔪 o) T p))) o := by
    rw [hWiff, IsTowerIso.proj_comm h₁ p]
    exact hmem
  rw [genLowerValue_eq_of_mem M _ hp', genLowerValue_eq_of_mem M 𝔪 hW]
  rw [compAt_eq_pullback hn o _ hdomT₀] at hdom hmax hcan₀ hcos₀ ⊢
  rw [compAt_eq_pullback hn o _ hdomT₀']
  -- the companion ideal of the restriction
  have hcomp : companionOf n (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
      (restrict U (head T (regimeRun (OrdRegime 𝔪 o) T p)))) o =
      MarkedIdeal.pullback (Subtype.val : openPreimage (head T (regimeRun (OrdRegime 𝔪 o) T p)) U → _)
        (companionOf n (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T p))) o) := by
    rw [geoTransformAlong_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent _ hT₀,
      pullback_val_companionOf hn hdomT₀.isWellFormed hdomT₀.isNonzeroAlongAt]
  have hdomC := isInvDomain_companionAlong hn hdomT₀ ho1
  obtain ⟨-, hmaxN, hcanN, hcosN, hvalN⟩ := value_restrict_restrict hM hdomC.isWellFormed.isClosedSubmanifold_N
    hdomC.isWellFormed.isCoherent (V := openPreimage (head T (regimeRun (OrdRegime 𝔪 o) T p)) U) hdom hmax _ hcan₀
  have hq := (hcosN ⟨_, hmem⟩ hW).mpr hcos₀
  have key := value_companionOf_isTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) hM hn hU
    ho1 h₀ hT₀U hWiff (by rw [hcomp]; exact hmaxN) h₁ (by rw [hcomp]; exact hcanN) ⟨p, hp'⟩ ⟨_, hmem⟩ rfl
    (by rw [hcomp]; exact hq)
  rw [hpb, hcomp] at key
  rw [key, hvalN ⟨_, hmem⟩ hW hq]
  rfl

/-- **Property (5) of the general value in the shape of the field `restrictOpen`** of
`ResolutionInvariantExt.ResolutionInvariant`: along canonical segments of the general value (`M` a value function
for the marked ideals of maximal order, `0 < n`), at every point of the cosupport over `U` (order `0`:
`GeneralValueOrderZero.restrictOpen_field_of_nmOrd_eq_zero`). -/
theorem restrictOpen_field (hM : IsMaxOrderValue n k M) (hn : 0 < n) (𝔪 : MarkedIdeal n X) (h : IsInvDomain k 𝔪)
    (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔪 (genInv M 𝔪) T) (p : openPreimage T U)
    (hp : (p : Y) ∈ (geoTransformAlong 𝔪 T).cosupp) :
    genInv M (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T) p = genInv M 𝔪 T p := by
  rcases Nat.eq_zero_or_pos (nmOrd (geoTransformAlong 𝔪 T) p) with h0 | hpos
  · exact GeneralValueOrderZero.restrictOpen_field_of_nmOrd_eq_zero hM hn 𝔪 h U T hcan p hp h0
  · exact genInv_restrict_of_pos hM hn h U T (GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn h T hcan)
      hcan p hp hpos

end Restrict

end

end Hironaka.GeneralRestrictOpen
