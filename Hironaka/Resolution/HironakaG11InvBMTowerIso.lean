import Hironaka.Resolution.HironakaG11InvBMRestrictOpen
import Hironaka.Invariant.StepOneTowerIso

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's Step 1 value: isomorphisms of towers (repair (B'), plan module 8, property (6))

Blueprint: `hironaka-g11-inv-bm-max-order.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6c.

For a biholomorphism `Φ : X' ≃ X` and an isomorphism of towers `T' ≅ T` over `Φ` (last-stage map `χ`), the values of
`stepOneInvBM R Φ^*𝔍` along `T'` are those of `stepOneInvBM R 𝔍` along `T` (composed with `χ`), and canonical segments
correspond, given the independence of the hypersurface of maximal contact for `𝔍` and `Φ^*𝔍`.

* **`lowerValueG_isTowerIso`** (both levels): the lower ideal of `𝔍` on the mask of `χ p'` is transported to the stage of `T'`
  (`inv_transport_opens`, `lowerIdealWBM_isTowerIso`), where it is the lower ideal of `Φ^*𝔍` formed with `w ∘ Φ`; the anchor
  `lowerValueG_eq_of_tangent` for `Φ^*𝔍` changes `w ∘ Φ` to the direction chosen for `Φ^*𝔍`;
* `stepOneInvBM_isTowerIso_eq`, **`stepOneInvBM_isTowerIso`**, **`towerIso_field`**.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMTowerIso

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
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

section TowerIso

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {k : ℕ} {Λ : Type v}
  [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n (k - 1) Λ) (𝔍 : MarkedIdeal n X)

/-- **Property (6) of Bierstone--Milman's Step 1 value, lower values** (both levels): let `𝔍` be well formed with `d ≥ 1`,
`T₀' ≅ T₀` over `Φ` (last-stage map `χ₀`), `T₁' ≅ T₁` over `χ₀` (last-stage map `χ`), `T₀ T₁` a multiple test blow-up of `J̄`.
If `p'` has lower data at level `s` for `Φ^*𝔍` at the split `T₀' T₁'` (its image at `T₀'` in the cosupport, of level `s`) and
`χ p'` has lower data at level `s` for `𝔍` at the split `T₀ T₁` (its image at `T₀` of level `s`), the lower values agree, given
the independence of the hypersurface of maximal contact for `Φ^*𝔍`. -/
theorem lowerValueG_isTowerIso (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hTI' : TangentIndepBM (MarkedIdeal.pullback Φ 𝔍) R) {s : ℕ} {Y₀ Z Y₀' Z' : CMfd.{u} n}
    {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Z} {T₀' : BlowupTower X' Y₀'}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₀} (hiso : IsTowerIso Φ T₀' T₀ χ₀)
    {T₁' : BlowupTower Y₀' Z'} {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z}
    (hχ : IsTowerIso χ₀ T₁' T₁ χ) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁))
    (hT' : IsGeoTestTower (barMarked (MarkedIdeal.pullback Φ 𝔍)) (T₀'.append T₁')) {p' : Z'}
    (ha' : T₁'.proj p' ∈ (geoTransformAlong (barMarked (MarkedIdeal.pullback Φ 𝔍)) T₀').cosupp)
    (hl' : level (MarkedIdeal.pullback Φ 𝔍) T₀' (T₁'.proj p') = s) (hl : level 𝔍 T₀ (T₁.proj (χ p')) = s)
    (hD' : LowerDataG R (MarkedIdeal.pullback Φ 𝔍) (maskBM (MarkedIdeal.pullback Φ 𝔍))
      (lowerBM (MarkedIdeal.pullback Φ 𝔍)) s T₀' T₁' p')
    (hD : LowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s T₀ T₁ (χ p')) :
    lowerValueG R (MarkedIdeal.pullback Φ 𝔍) (maskBM (MarkedIdeal.pullback Φ 𝔍)) (lowerBM (MarkedIdeal.pullback Φ 𝔍))
        s T₀' T₁' p' =
      lowerValueG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s T₀ T₁ (χ p') := by
  classical
  obtain ⟨hT₀, -⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  have hψa : χ₀ (T₁'.proj p') = T₁.proj (χ p') := hχ.proj_comm p'
  generalize hqdef : χ p' = q at hD hl hψa ⊢
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
  -- transport to the stage `T₀'` of `Φ^*𝔍`
  set W' : Opens Y₀' := ⟨χ₀ ⁻¹' (maskBM 𝔍 s T₀ (T₁.proj q) : Set Y₀),
    (maskBM 𝔍 s T₀ (T₁.proj q)).isOpen.preimage χ₀.continuous⟩ with hW'def
  have hW' : ∀ y', y' ∈ W' ↔ χ₀ y' ∈ maskBM 𝔍 s T₀ (T₁.proj q) := fun _ => Iff.rfl
  have hiso₁ := StepOneTangentChange.isTowerIso_restrictOpens hW' hχ
    (StepOneTangentChange.isTowerIso_mem_openPreimage_iff hχ hW')
  obtain ⟨hdom₂, hcan₂, hval₂⟩ := inv_transport_opens R hcoh χ₀.contMDiff
    (StepOneTangentChange.diffeoOpens χ₀ W' (maskBM 𝔍 s T₀ (T₁.proj q)) hW') (fun _ => rfl) hiso₁ hdom hcan
  -- the transported lower ideal is the lower ideal of `Φ^*𝔍` formed with `w ∘ Φ`
  have hisoL := lowerIdealWBM_isTowerIso 𝔍 Φ h𝔍 hd s (tangentChoice 𝔍 (T₀.proj (T₁.proj q))).2 hiso hT₀ _ hS hSne
  have hO := ContactLowerValue.origMembers_isTowerIso Φ 𝔍 h𝔍 hd hiso hT₀
  have hthr : throughMembers (MarkedIdeal.pullback Φ 𝔍) T₀' (T₁'.proj p') =
      (throughMembers 𝔍 T₀ (T₁.proj q)).map (χ₀ ⁻¹' ·) := by
    unfold throughMembers
    rw [hO, filter_map_preimage]
    simp only [hψa]
  have hL' : MarkedIdeal.pullback χ₀
      (lowerIdealWBM 𝔍 s (tangentChoice 𝔍 (T₀.proj (T₁.proj q))).2 T₀ (throughMembers 𝔍 T₀ (T₁.proj q))) =
      lowerIdealWBM (MarkedIdeal.pullback Φ 𝔍) s ((tangentChoice 𝔍 (T₀.proj (T₁.proj q))).2 ∘ Φ) T₀'
        (throughMembers (MarkedIdeal.pullback Φ 𝔍) T₀' (T₁'.proj p')) := by
    rw [hthr]
    exact hisoL.symm
  rw [hL'] at hdom₂ hcan₂ hval₂
  -- the anchor for `Φ^*𝔍` with `w ∘ Φ` on `W'`
  have hu := ContactMarkedCanonical.isTangentDirectionAlong_comp Φ h𝔍.isCoherent hw
  have hW'U : (W' : Set Y₀') ⊆ T₀'.proj ⁻¹' (Φ ⁻¹' (tangentChoice 𝔍 (T₀.proj (T₁.proj q))).1) := by
    intro y' hy'
    have h1 : χ₀ y' ∈ maskBM 𝔍 s T₀ (T₁.proj q) := hy'
    show Φ (T₀'.proj y') ∈ (tangentChoice 𝔍 (T₀.proj (T₁.proj q))).1
    rw [hiso.proj_comm]
    exact HironakaG11InvBMCanonicalTail.maskBM_subset_tangent 𝔍 s T₀ _ h1
  have hpW' : T₁'.proj p' ∈ W' := by
    show χ₀ (T₁'.proj p') ∈ maskBM 𝔍 s T₀ (T₁.proj q)
    rw [hψa]
    exact h
  have key := lowerValueG_eq_of_tangent (MarkedIdeal.pullback Φ 𝔍) R hTI' T₀' T₁' hT' ha' hl' hD' hu W' hW'U hpW'
    hdom₂ hcan₂
  rw [key]
  congr 1
  have hξ : StepOneTangentChange.diffeoOpens χ (openPreimage T₁' W') (openPreimage T₁ (maskBM 𝔍 s T₀ (T₁.proj q)))
      (StepOneTangentChange.isTowerIso_mem_openPreimage_iff hχ hW') ⟨p', hpW'⟩ = ⟨q, h⟩ := Subtype.ext hqdef
  rw [(hval₂ ⟨p', hpW'⟩).2 (by rw [hξ]; exact hcos), hξ]

/-- **The values agree along isomorphic towers** when both are canonical segments (given the independence of the
hypersurface of maximal contact for `𝔍` and `Φ^*𝔍`). -/
theorem stepOneInvBM_isTowerIso_eq (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) (hTI : TangentIndepBM 𝔍 R)
    (hTI' : TangentIndepBM (MarkedIdeal.pullback Φ 𝔍) R) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T)
    (hcan' : IsCanonical (barMarked (MarkedIdeal.pullback Φ 𝔍)) (stepOneInvBM R (MarkedIdeal.pullback Φ 𝔍)) T')
    (p : Y') (hp : χ p ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) :
    stepOneInvBM R (MarkedIdeal.pullback Φ 𝔍) T' p = stepOneInvBM R 𝔍 T (χ p) := by
  obtain ⟨h𝔍', hd', hmax', hk'⟩ := StepOneTowerIso.hypotheses_pullback Φ 𝔍 h𝔍 hd hmax hk
  have hAC : AnchorChangeBM 𝔍 R := anchorChangeBM_of_tangentIndepBM 𝔍 R hTI
  have hAC' : AnchorChangeBM (MarkedIdeal.pullback Φ 𝔍) R := anchorChangeBM_of_tangentIndepBM _ R hTI'
  have hT := isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk T hcan
  have hT' := isGeoTestTower_of_isCanonical_stepOneInvBM _ R hAC' h𝔍' hd' hn hmax' hk' T' hcan'
  obtain ⟨-, hc, hpt⟩ := StepOneTowerIso.isTowerIso_facts Φ 𝔍 h𝔍 hd hiso hT
  obtain ⟨hl, hs, -⟩ := hpt p
  have hp' : p ∈ (geoTransformAlong (barMarked (MarkedIdeal.pullback Φ 𝔍)) T').cosupp := by rw [hc]; exact hp
  have hD := hasLowerDataG_of_isCanonical 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan (χ p) hp
  have hD' := hasLowerDataG_of_isCanonical _ R hAC' h𝔍' hd' hn hmax' hk' T' hT' hcan' p hp'
  unfold stepOneInvBM
  by_cases hsp : IsSpecial 𝔍 T (χ p)
  · rw [stepOneInvG_of_isSpecial R _ _ _ T' (hs.mpr hsp), stepOneInvG_of_isSpecial R 𝔍 _ _ T hsp, hl]
  · have hsp' : ¬ IsSpecial (MarkedIdeal.pullback Φ 𝔍) T' p := fun h => hsp (hs.mp h)
    have hreg := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 T hT hp hsp
    have hreg' := stepRegime_and_mem_cosupp_head _ h𝔍' T' hT' hp' hsp'
    specialize hD hsp
    specialize hD' hsp'
    rw [stepOneInvG_of_not_isSpecial R _ _ _ T' hsp', stepOneInvG_of_not_isSpecial R 𝔍 _ _ T hsp]
    rw [hl] at hD' hreg' ⊢
    obtain ⟨s, hsdef⟩ : ∃ s, level 𝔍 T (χ p) = s := ⟨_, rfl⟩
    rw [hsdef] at hD hD' hreg hreg' ⊢
    have hrun := NonmonomialOrderRegime.regimeRun_isTowerIso_of (stepRegime 𝔍 s)
      (stepRegime (MarkedIdeal.pullback Φ 𝔍) s) (fun S => IsGeoTestTower (barMarked 𝔍) S) (fun _ _ _ _ h => h.1)
      (fun S' S ψ hψ hS q => ((StepOneTowerIso.isTowerIso_facts Φ 𝔍 h𝔍 hd hψ hS).2.2 q).2.2 s) hiso hT p
    rw [hrun] at hD' hreg' ⊢
    obtain ⟨χ₀, h₀, h₁⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split hiso (regimeRun (stepRegime 𝔍 s) T (χ p))
    have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((head T (regimeRun (stepRegime 𝔍 s) T (χ p))).append
        (tail T (regimeRun (stepRegime 𝔍 s) T (χ p)))) := by rw [head_append_tail]; exact hT
    have hT₀₁' : IsGeoTestTower (barMarked (MarkedIdeal.pullback Φ 𝔍))
        ((head T' (regimeRun (stepRegime 𝔍 s) T (χ p))).append (tail T' (regimeRun (stepRegime 𝔍 s) T (χ p)))) := by
      rw [head_append_tail]; exact hT'
    congr 2
    exact lowerValueG_isTowerIso Φ R 𝔍 h𝔍 hd hn hTI' h₀ h₁ hT₀₁ hT₀₁' hreg'.2 hreg'.1.1 hreg.1.1 hD' hD

/-- **Property (6) of Bierstone--Milman's Step 1 value** (given the independence of the hypersurface of maximal contact for
`𝔍` and `Φ^*𝔍`): for an isomorphism `χ : T' ≅ T` of towers over `Φ` with `T` a canonical segment of `stepOneInvBM R 𝔍`, the
tower `T'` is a canonical segment of `stepOneInvBM R Φ^*𝔍` and the values correspond. -/
theorem stepOneInvBM_isTowerIso (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) (hTI : TangentIndepBM 𝔍 R)
    (hTI' : TangentIndepBM (MarkedIdeal.pullback Φ 𝔍) R) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) :
    IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T →
      IsCanonical (barMarked (MarkedIdeal.pullback Φ 𝔍)) (stepOneInvBM R (MarkedIdeal.pullback Φ 𝔍)) T' ∧
      ∀ p : Y', χ p ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp →
        stepOneInvBM R (MarkedIdeal.pullback Φ 𝔍) T' p = stepOneInvBM R 𝔍 T (χ p) := by
  have hAC : AnchorChangeBM 𝔍 R := anchorChangeBM_of_tangentIndepBM 𝔍 R hTI
  induction hiso with
  | refl =>
    intro hcan
    exact ⟨trivial, fun p hp => stepOneInvBM_isTowerIso_eq Φ R 𝔍 h𝔍 hd hn hmax hk hTI hTI' IsTowerIso.refl hcan
      trivial p hp⟩
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro hcan
    have hcan₀ := hcan
    obtain ⟨hcanT, hCc⟩ : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T ∧
        (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) := hcan
    obtain ⟨hcan'T, hval⟩ := ih hcanT
    have hT := isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk T hcanT
    have hc := (StepOneTowerIso.isTowerIso_facts Φ 𝔍 h𝔍 hd h hT).2.1
    have hcan'S : IsCanonical (barMarked (MarkedIdeal.pullback Φ 𝔍)) (stepOneInvBM R (MarkedIdeal.pullback Φ 𝔍))
        (.step T' C' π' hπ') := by
      show IsCanonical (barMarked (MarkedIdeal.pullback Φ 𝔍)) (stepOneInvBM R (MarkedIdeal.pullback Φ 𝔍)) T' ∧
        (C' = ∅ ∨ C' = maxLocus (stepOneInvBM R (MarkedIdeal.pullback Φ 𝔍) T')
          (geoTransformAlong (barMarked (MarkedIdeal.pullback Φ 𝔍)) T').cosupp)
      refine ⟨hcan'T, ?_⟩
      subst hC
      rcases hCc with rfl | rfl
      · exact Or.inl preimage_empty
      · right
        rw [hc]
        exact (ResolutionInvariantSegments.maxLocus_preimage_of_surjective χ.toEquiv.surjective
          (fun q hq => hval q hq)).symm
    exact ⟨hcan'S, fun p hp => stepOneInvBM_isTowerIso_eq Φ R 𝔍 h𝔍 hd hn hmax hk hTI hTI'
      (IsTowerIso.step h hπ' hπ χ₁ hcomm hC) hcan₀ hcan'S p hp⟩

/-- **Property (6), the field `towerIso`** of `MaxOrderValue.IsMaxOrderValue` for `stepOneInvBM R` (given the independence of
the hypersurface of maximal contact for `𝔍` and `Φ^*𝔍`). -/
theorem towerIso_field (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    (hTI : TangentIndepBM 𝔍 R) (hTI' : TangentIndepBM (MarkedIdeal.pullback Φ 𝔍) R) {Y' Y : CMfd.{u} n}
    (T' : BlowupTower X' Y') (T : BlowupTower X Y) (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (hiso : IsTowerIso Φ T' T χ) (hcan : IsCanonical 𝔍 (stepOneInvBM R 𝔍) T) (p : Y')
    (hp : χ p ∈ (geoTransformAlong 𝔍 T).cosupp) :
    stepOneInvBM R (MarkedIdeal.pullback Φ 𝔍) T' p = stepOneInvBM R 𝔍 T (χ p) := by
  have hAC : AnchorChangeBM 𝔍 R := anchorChangeBM_of_tangentIndepBM 𝔍 R hTI
  rw [← (HironakaG11InvBMBridge.isGeoTestTower_of_isCanonical R 𝔍 hAC h hmax hn T hcan).2.2] at hp
  exact (stepOneInvBM_isTowerIso Φ R 𝔍 h.isWellFormed h.one_le_d hn hmax h.dimLE hTI hTI' hiso
    ((HironakaG11InvBMBridge.isCanonical_iff R 𝔍 hAC h hmax hn T).mp hcan)).2 p hp

end TowerIso

end

end Hironaka.HironakaG11InvBMTowerIso
