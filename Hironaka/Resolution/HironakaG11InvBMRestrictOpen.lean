import Hironaka.Resolution.HironakaG11InvBMNaturality
import Hironaka.Resolution.HironakaG11InvBMBridge
import Hironaka.Invariant.StepOneRestrictOpen

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's Step 1 value: restriction to open sets (repair (B'), plan module 8, property (5))

Blueprint: `hironaka-g11-inv-bm-max-order.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6c.
Source: Bierstone--Milman 2008, §5 Step I.A (the invariant in the year `q` is computed from the coefficient ideal on a local
hypersurface of maximal contact; by the independence of that hypersurface, restriction to an open set changes nothing).

For `U ⊆ X` open, the values of `stepOneInvBM R 𝔍|_U` along `T|_U` are those of `stepOneInvBM R 𝔍` along `T`, and canonical
segments restrict, given the independence of the hypersurface of maximal contact (`TangentIndepBM`) for `𝔍` and `𝔍|_U`.

* **`lowerValueG_restrict`** (both levels at once): the lower ideal of `𝔍` on the mask of `χ p'` is shrunk to its part over `U`
  (`MaxLocusLocal.restrict_nestedOpens`), transported to the stage of `T|_U` (`HironakaG11InvBMNaturality.inv_transport_opens`,
  `lowerIdealWBM_restrict`, `lowerIdealWBM_isTowerIso` over `id_U`), and the anchor `lowerValueG_eq_of_tangent` for `𝔍|_U`
  changes the tangent function `w ∘ ι` to the one chosen for `𝔍|_U`;
* `stepOneInvBM_restrict_eq`, **`stepOneInvBM_restrict`**, **`restrictOpen_field`** (the field `restrictOpen` of
  `MaxOrderValue.IsMaxOrderValue`).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMRestrictOpen

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
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

open Classical in
/-- Filtering the preimages of members by membership of a point is filtering the members by membership of its image. -/
theorem filter_map_preimage {α β : Type*} (f : α → β) (L : List (Set β)) (a : α) :
    (L.map (f ⁻¹' ·)).filter (fun H => decide (a ∈ H)) = (L.filter fun H => decide (f a ∈ H)).map (f ⁻¹' ·) := by
  rw [List.filter_map]
  rfl

section Restrict

variable {X : CMfd.{u} n} (U : Opens X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ) (𝔍 : MarkedIdeal n X)

/-- **Property (5) of Bierstone--Milman's Step 1 value, lower values** (both levels): let `𝔍` be well formed with `d ≥ 1`,
`U ⊆ X` open, `T₀ T₁` a multiple test blow-up of `J̄`, and `T₀'`, `T₁'` towers over `U` isomorphic over `id_U` to `T₀|_U` and,
over the last-stage map `χ₀`, to `T₁|_{T₀⁻¹U}` (last-stage map `χ`) -- the shape of the split of `T|_U`.  If `p'` has lower data
at level `s` for `𝔍|_U` at the split `T₀' T₁'` (its image at `T₀'` in `cosupp J̄(𝔍|_U)_{T₀'}`, of level `s`) and `χ p'` has lower
data at level `s` for `𝔍` at the split `T₀ T₁` (its image at `T₀` of level `s`), the two lower values agree, given the
independence of the hypersurface of maximal contact for `𝔍|_U`. -/
theorem lowerValueG_restrict (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hTIU : TangentIndepBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) R) {s : ℕ}
    {Y₀ Z Y₀' Z' : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Z}
    {T₀' : BlowupTower (CMfd.of (n := n) U) Y₀'}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₀ U)}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) T₀' (restrict U T₀) χ₀)
    {T₁' : BlowupTower Y₀' Z'}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ U))}
    (hχ : IsTowerIso χ₀ T₁' (restrict (openPreimage T₀ U) T₁) χ) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁))
    (hT' : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (T₀'.append T₁'))
    {p' : Z'}
    (ha' : T₁'.proj p' ∈ (geoTransformAlong (barMarked (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) T₀').cosupp)
    (hl' : level (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) T₀' (T₁'.proj p') = s)
    (hl : level 𝔍 T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)) = s)
    (hD' : LowerDataG R (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
      (maskBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (lowerBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) s T₀' T₁' p')
    (hD : LowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s T₀ T₁ ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)) :
    lowerValueG R (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (maskBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
        (lowerBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) s T₀' T₁' p' =
      lowerValueG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s T₀ T₁ ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) := by
  classical
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔍U : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).IsWellFormed := IsWellFormed.pullback_val h𝔍 U
  have hbarU : barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
      MarkedIdeal.pullback (Subtype.val : U → X) (barMarked 𝔍) :=
    ContactStageKept.barMarked_pullback_val U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd
  obtain ⟨hT₀, -⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  have hT₀U : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T₀) := by
    rw [hbarU]
    exact isGeoTestTower_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  -- the image of `p'` at the stage `T₀` of `𝔍`
  have hψa : ((χ₀ (T₁'.proj p') : openPreimage T₀ U) : Y₀) =
      T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) := by
    rw [hχ.proj_comm p']
    exact proj_restrict _ T₁ (χ p')
  have hqV : T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈ openPreimage T₀ U := (χ p').2
  generalize hqdef : ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) = q at hD hl hψa hqV ⊢
  -- the data on the side of `𝔍`
  obtain ⟨h, hdom, hcan, hcos⟩ := hD
  have hw := isTangentDirectionAlong_tangentChoice_of_nonempty 𝔍
    ⟨_, HironakaG11InvBMCanonicalTail.maskBM_subset_tangent 𝔍 s T₀ _ h⟩
  have hS := HironakaG11InvBMLowerTailSucc.isClosedSubmanifold_of_mem_throughMembers 𝔍 h𝔍 hn T₀ hT₀ (T₁.proj q)
  have hSne : s ≠ 0 → throughMembers 𝔍 T₀ (T₁.proj q) ≠ [] := fun hs => by
    obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
    exact HironakaG11InvBMLowerTailSucc.throughMembers_ne_nil 𝔍 T₀ hl
  have hcoh := isCoherent_lowerIdealWBM 𝔍 h𝔍 hd hn s (tangentChoice 𝔍 (T₀.proj (T₁.proj q))).2 T₀ hT₀ (T₁.proj q)
  have hLeq : lowerBM 𝔍 s T₀ (T₁.proj q) = MarkedIdeal.pullback (Subtype.val : maskBM 𝔍 s T₀ (T₁.proj q) → Y₀)
      (lowerIdealWBM 𝔍 s (tangentChoice 𝔍 (T₀.proj (T₁.proj q))).2 T₀ (throughMembers 𝔍 T₀ (T₁.proj q))) := by
    rw [lowerBM_eq, lowerIdealBM_eq_lowerIdealWBM]
  rw [hLeq] at hdom hcan hcos
  rw [lowerValueG_eq_of_mem R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) h, hLeq]
  -- (1) shrink the mask to its part over `U`
  have hW₁M : maskBM 𝔍 s T₀ (T₁.proj q) ⊓ openPreimage T₀ U ≤ maskBM 𝔍 s T₀ (T₁.proj q) := inf_le_left
  have hW₁V : maskBM 𝔍 s T₀ (T₁.proj q) ⊓ openPreimage T₀ U ≤ openPreimage T₀ U := inf_le_right
  obtain ⟨hdom₁, hcan₁, hval₁⟩ := MaxLocusLocal.restrict_nestedOpens R hcoh hW₁M hdom T₁ hcan
  have hqW₁ : T₁.proj q ∈ maskBM 𝔍 s T₀ (T₁.proj q) ⊓ openPreimage T₀ U := ⟨h, hqV⟩
  have hcos₁ := (mem_cosupp_nested_iff hcoh hW₁M hdom.isWellFormed T₁ (isGeoTestTower_of_isCanonical R hdom _ hcan)
    ⟨q, hqW₁⟩).mpr hcos
  have v1 := hval₁ ⟨q, hqW₁⟩ hcos₁
  -- (2) transport to the stage `T₀'` of `𝔍|_U`
  have hψ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun y' : Y₀' => ((χ₀ y' : openPreimage T₀ U) : Y₀)) := contMDiff_subtype_val.comp χ₀.contMDiff
  set W₂ : Opens (CMfd.of (n := n) (openPreimage T₀ U)) :=
    MaxLocusLocal.nestedOpens (openPreimage T₀ U) (maskBM 𝔍 s T₀ (T₁.proj q) ⊓ openPreimage T₀ U) with hW₂def
  set W' : Opens Y₀' := ⟨χ₀ ⁻¹' (W₂ : Set (CMfd.of (n := n) (openPreimage T₀ U))), W₂.isOpen.preimage χ₀.continuous⟩
    with hW'def
  have hW' : ∀ y', y' ∈ W' ↔ χ₀ y' ∈ W₂ := fun _ => Iff.rfl
  have hiso₁ := (StepOneTangentChange.isTowerIso_restrictOpens hW' hχ
    (StepOneTangentChange.isTowerIso_mem_openPreimage_iff hχ hW')).trans
    (MaxLocusLocal.isTowerIso_restrict_nestedOpens hW₁V T₁)
  obtain ⟨hdom₂, hcan₂, hval₂⟩ := inv_transport_opens R hcoh hψ
    ((StepOneTangentChange.diffeoOpens χ₀ W' W₂ hW').trans (MaxLocusLocal.nestedOpensDiffeo (n := n) hW₁V))
    (fun _ => rfl) hiso₁ hdom₁ hcan₁
  -- (3) the transported lower ideal is the lower ideal of `𝔍|_U` formed with `w ∘ ι`
  have hS' : ∀ H ∈ (throughMembers 𝔍 T₀ (T₁.proj q)).map ((Subtype.val : openPreimage T₀ U → Y₀) ⁻¹' ·),
      IsClosedSubmanifold n H := by
    intro H hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val (hS H₀ hH₀) (openPreimage T₀ U)
  have hSne' : s ≠ 0 → (throughMembers 𝔍 T₀ (T₁.proj q)).map ((Subtype.val : openPreimage T₀ U → Y₀) ⁻¹' ·) ≠ [] :=
    fun hs => by simpa using hSne hs
  have hres := lowerIdealWBM_restrict 𝔍 U h𝔍 hd s (tangentChoice 𝔍 (T₀.proj (T₁.proj q))).2 T₀ hT₀ _ hS hSne
  have hisoL := lowerIdealWBM_isTowerIso (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) h𝔍U hd s
    ((tangentChoice 𝔍 (T₀.proj (T₁.proj q))).2 ∘ (Subtype.val : U → X)) hiso hT₀U _ hS' hSne'
  have hpbU : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) = MarkedIdeal.pullback (Subtype.val : U → X) 𝔍 :=
    ContactCanonicalAlong.pullback_id _ h𝔍U.isCoherent
  rw [hpbU] at hisoL
  have hO := ContactLowerValue.origMembers_isTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
    (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) h𝔍U hd hiso hT₀U
  rw [hpbU, ContactLowerValue.origMembers_restrict U 𝔍 h𝔍 hd hT₀] at hO
  have hthr : throughMembers (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) T₀' (T₁'.proj p') =
      ((throughMembers 𝔍 T₀ (T₁.proj q)).map ((Subtype.val : openPreimage T₀ U → Y₀) ⁻¹' ·)).map (χ₀ ⁻¹' ·) := by
    unfold throughMembers
    rw [hO, filter_map_preimage, filter_map_preimage]
    simp only [hψa]
  have hL' : MarkedIdeal.pullback (fun y' : Y₀' => ((χ₀ y' : openPreimage T₀ U) : Y₀))
      (lowerIdealWBM 𝔍 s (tangentChoice 𝔍 (T₀.proj (T₁.proj q))).2 T₀ (throughMembers 𝔍 T₀ (T₁.proj q))) =
      lowerIdealWBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) s
        ((tangentChoice 𝔍 (T₀.proj (T₁.proj q))).2 ∘ (Subtype.val : U → X)) T₀'
        (throughMembers (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) T₀' (T₁'.proj p')) := by
    rw [hthr, ← StepOneTangentChange.pullback_pullback_of_comp hcoh contMDiff_subtype_val χ₀.contMDiff
      (fun _ => rfl), ← hres]
    exact hisoL.symm
  rw [hL'] at hdom₂ hcan₂ hval₂
  -- (4) the anchor for `𝔍|_U` with `w ∘ ι` on `W'`
  have hu := ContactMarkedCanonical.isTangentDirectionAlong_comp_val U h𝔍.isCoherent hw
  have hW'U : (W' : Set Y₀') ⊆ T₀'.proj ⁻¹'
      ((Subtype.val : U → X) ⁻¹' (tangentChoice 𝔍 (T₀.proj (T₁.proj q))).1) := by
    intro y' hy'
    have h1 : ((χ₀ y' : openPreimage T₀ U) : Y₀) ∈ maskBM 𝔍 s T₀ (T₁.proj q) := hy'.1
    have e : T₀'.proj y' = (restrict U T₀).proj (χ₀ y') := hiso.proj_comm y'
    show (((T₀'.proj y' : CMfd.of (n := n) U) : U) : X) ∈ (tangentChoice 𝔍 (T₀.proj (T₁.proj q))).1
    rw [e, proj_restrict]
    exact HironakaG11InvBMCanonicalTail.maskBM_subset_tangent 𝔍 s T₀ _ h1
  have hpW' : T₁'.proj p' ∈ W' := by
    show ((χ₀ (T₁'.proj p') : openPreimage T₀ U) : Y₀) ∈ maskBM 𝔍 s T₀ (T₁.proj q) ⊓ openPreimage T₀ U
    rw [hψa]
    exact hqW₁
  have key := lowerValueG_eq_of_tangent (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) R
    hTIU T₀' T₁' hT' ha' hl' hD' hu W' hW'U hpW' hdom₂ hcan₂
  rw [key]
  congr 1
  have hξ : ((StepOneTangentChange.diffeoOpens χ (openPreimage T₁' W') (openPreimage (restrict (openPreimage T₀ U) T₁) W₂)
      (StepOneTangentChange.isTowerIso_mem_openPreimage_iff hχ hW')).trans
      (MaxLocusLocal.nestedDiffeo (openPreimage T₁ (openPreimage T₀ U)) (openPreimage (restrict (openPreimage T₀ U) T₁) W₂)
        (openPreimage T₁ (maskBM 𝔍 s T₀ (T₁.proj q) ⊓ openPreimage T₀ U))
        (MaxLocusLocal.mem_openPreimage_restrict_nestedOpens _ _ T₁) (MaxLocusLocal.openPreimage_mono T₁ hW₁V)))
        ⟨p', hpW'⟩ = ⟨q, hqW₁⟩ := Subtype.ext hqdef
  rw [(hval₂ ⟨p', hpW'⟩).2 (by rw [hξ]; exact hcos₁), hξ]
  exact v1

/-- **The values agree along `T` and `T|_U`** when both are canonical segments (given the independence of the hypersurface of
maximal contact for `𝔍` and for `𝔍|_U`). -/
theorem stepOneInvBM_restrict_eq (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) (hTI : TangentIndepBM 𝔍 R)
    (hTIU : TangentIndepBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) R)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T)
    (hcanU : IsCanonical (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (stepOneInvBM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T))
    (p : openPreimage T U) (hp : (p : Y) ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) :
    stepOneInvBM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p =
      stepOneInvBM R 𝔍 T p := by
  obtain ⟨h𝔍U, hdU, hmaxU, hkU⟩ := StepOneRestrictOpen.hypotheses_restrict 𝔍 U h𝔍 hd hmax hk
  have hAC : AnchorChangeBM 𝔍 R := anchorChangeBM_of_tangentIndepBM 𝔍 R hTI
  have hACU : AnchorChangeBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) R :=
    anchorChangeBM_of_tangentIndepBM (X := CMfd.of (n := n) U) _ R hTIU
  have hT := isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk T hcan
  have hTU := isGeoTestTower_of_isCanonical_stepOneInvBM (X := CMfd.of (n := n) U) _ R hACU h𝔍U hdU hn hmaxU hkU _
    hcanU
  obtain ⟨-, hc, hpt⟩ := StepOneRestrictOpen.restrict_facts 𝔍 U h𝔍 hd T hT
  obtain ⟨hl, hs, -⟩ := hpt p
  have hpU : p ∈ (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T)).cosupp := by rw [hc]; exact hp
  have hD := hasLowerDataG_of_isCanonical 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan p hp
  have hDU := hasLowerDataG_of_isCanonical (X := CMfd.of (n := n) U) _ R hACU h𝔍U hdU hn hmaxU hkU _ hTU hcanU p hpU
  unfold stepOneInvBM
  by_cases hsp : IsSpecial 𝔍 T p
  · rw [stepOneInvG_of_isSpecial R _ _ _ _ (hs.mpr hsp), stepOneInvG_of_isSpecial R 𝔍 _ _ T hsp, hl]
  · have hspU : ¬ IsSpecial (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p :=
      fun h => hsp (hs.mp h)
    have hreg := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 T hT hp hsp
    have hregU := stepRegime_and_mem_cosupp_head (X := CMfd.of (n := n) U) _ h𝔍U (restrict U T) hTU hpU hspU
    specialize hD hsp
    specialize hDU hspU
    rw [stepOneInvG_of_not_isSpecial R _ _ _ _ hspU, stepOneInvG_of_not_isSpecial R 𝔍 _ _ T hsp]
    rw [hl] at hDU hregU ⊢
    obtain ⟨s, hsdef⟩ : ∃ s, level 𝔍 T p = s := ⟨_, rfl⟩
    rw [hsdef] at hD hDU hreg hregU ⊢
    have hrun := NonmonomialOrderRegime.regimeRun_restrict_of U (stepRegime 𝔍 s)
      (stepRegime (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) s)
      (fun T' => IsGeoTestTower (barMarked 𝔍) T') (fun _ _ _ _ h => h.1)
      (fun T' hT' q => ((StepOneRestrictOpen.restrict_facts 𝔍 U h𝔍 hd T' hT').2.2 q).2.2 s) T hT p
    rw [hrun] at hDU hregU ⊢
    obtain ⟨χ₀, h₀, h₁⟩ := BlowupTowerSplitIso.exists_isTowerIso_split_restrict U T (regimeRun (stepRegime 𝔍 s) T p)
    have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((head T (regimeRun (stepRegime 𝔍 s) T p)).append
        (tail T (regimeRun (stepRegime 𝔍 s) T p))) := by rw [head_append_tail]; exact hT
    have hT₀₁U : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
        ((head (restrict U T) (regimeRun (stepRegime 𝔍 s) T p)).append
          (tail (restrict U T) (regimeRun (stepRegime 𝔍 s) T p))) := by rw [head_append_tail]; exact hTU
    congr 2
    exact lowerValueG_restrict U R 𝔍 h𝔍 hd hn hTIU h₀ h₁ hT₀₁ hT₀₁U hregU.2 hregU.1.1 hreg.1.1 hDU hD

/-- **Property (5) of Bierstone--Milman's Step 1 value** (given the independence of the hypersurface of maximal contact for
`𝔍` and `𝔍|_U`): for `𝔍` well formed with `d ≥ 1`, of maximal order along `N` with `dim N ≤ k` (`0 < n`), and `U ⊆ X` open, the
restriction `T|_U` of a canonical segment `T` of `stepOneInvBM R 𝔍` is a canonical segment of `stepOneInvBM R 𝔍|_U`, and at the
points of the cosupport over `U` the values agree. -/
theorem stepOneInvBM_restrict (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) (hTI : TangentIndepBM 𝔍 R)
    (hTIU : TangentIndepBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) R) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T →
      IsCanonical (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
        (stepOneInvBM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T) ∧
      ∀ p : openPreimage T U, (p : Y) ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp →
        stepOneInvBM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p =
          stepOneInvBM R 𝔍 T p
  | _, .refl, hcan => ⟨trivial, fun p hp => stepOneInvBM_restrict_eq U R 𝔍 h𝔍 hd hn hmax hk hTI hTIU .refl hcan trivial p hp⟩
  | _, .step T C π hπ, hcan => by
      have hcan₀ := hcan
      obtain ⟨hcanT, hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) := hcan
      obtain ⟨hcanUT, hval⟩ := stepOneInvBM_restrict h𝔍 hd hn hmax hk hTI hTIU T hcanT
      have hAC : AnchorChangeBM 𝔍 R := anchorChangeBM_of_tangentIndepBM 𝔍 R hTI
      have hT := isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk T hcanT
      have hc := (StepOneRestrictOpen.restrict_facts 𝔍 U h𝔍 hd T hT).2.1
      have hcanUS : IsCanonical (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
          (stepOneInvBM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
          (restrict U (.step T C π hπ)) := by
        show IsCanonical (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
            (stepOneInvBM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T) ∧
          (((Subtype.val : openPreimage T U → _) ⁻¹' C) = ∅ ∨
            ((Subtype.val : openPreimage T U → _) ⁻¹' C) = maxLocus
              (stepOneInvBM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T))
              (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
                (restrict U T)).cosupp)
        refine ⟨hcanUT, ?_⟩
        rcases hC with rfl | rfl
        · exact Or.inl preimage_empty
        · by_cases hne : ((Subtype.val : openPreimage T U → _) ⁻¹'
              maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp).Nonempty
          · right
            rw [hc]
            exact (ResolutionInvariantSegments.maxLocus_preimage _ (fun q hq => hval q hq) hne).symm
          · exact Or.inl (not_nonempty_iff_eq_empty.mp hne)
      exact ⟨hcanUS, fun p hp => stepOneInvBM_restrict_eq U R 𝔍 h𝔍 hd hn hmax hk hTI hTIU _ hcan₀ hcanUS p hp⟩

/-- **Property (5), the field `restrictOpen`** of `MaxOrderValue.IsMaxOrderValue` for `stepOneInvBM R` (given the independence
of the hypersurface of maximal contact for `𝔍` and `𝔍|_U`). -/
theorem restrictOpen_field (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    (hTI : TangentIndepBM 𝔍 R)
    (hTIU : TangentIndepBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) R)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (stepOneInvBM R 𝔍) T)
    (p : openPreimage T U) (hp : (p : Y) ∈ (geoTransformAlong 𝔍 T).cosupp) :
    stepOneInvBM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p =
      stepOneInvBM R 𝔍 T p := by
  have hAC : AnchorChangeBM 𝔍 R := anchorChangeBM_of_tangentIndepBM 𝔍 R hTI
  rw [← (HironakaG11InvBMBridge.isGeoTestTower_of_isCanonical R 𝔍 hAC h hmax hn T hcan).2.2] at hp
  exact (stepOneInvBM_restrict U R 𝔍 h.isWellFormed h.one_le_d hn hmax h.dimLE hTI hTIU T
    ((HironakaG11InvBMBridge.isCanonical_iff R 𝔍 hAC h hmax hn T).mp hcan)).2 p hp

end Restrict

end

end Hironaka.HironakaG11InvBMRestrictOpen
