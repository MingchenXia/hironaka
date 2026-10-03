/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ContactEmptyPrefix
import Hironaka.Invariant.StepOneCompare
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.Invariant.ContactMarkedCanonical
import Hironaka.Invariant.ContactRepresentative
import Hironaka.Invariant.ContactStageInvDomain
import Hironaka.Invariant.ContactStageKept
import Hironaka.Invariant.ContactStageTail
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneTangentChange
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.StepOneValueMasked
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1bb's lower value of the masked Step 1 value function under biholomorphisms, restrictions and representatives

The Step 1b inputs of properties (1), (4'), (5), (6) and (7) of `hir:centre-function` for masked Step 1 value
function, at the level of its lower values at level `0`. Source: Włodarczyk 2005 (arXiv `hiron.tex`), Step 1bb and
the lemma on the commutativity of the resolution procedure with étale morphisms: the values of Step 1b do not depend
on the hypersurface of maximal contact and commute with étale morphisms.

At level `0` the lower value of a point `p` is computed with the tangent direction chosen at the base point of `p`,
on the mask of `p`. Transporting it along a biholomorphism, a restriction or a change of representative produces the
transported tangent direction on the transported mask, not the one chosen for the new marked ideal on its own mask.
The **anchor lemma** `lowerValueL_zero_eq` absorbs this: given lower data, the lower value is the value of `R` for
*any* tangent direction `u` on *any* open set `W` around the image of `p` missing the original members, on which the
marked ideal of Step 1b lies in the domain with a canonical restricted tail
(`StepOneTangentChange.inv_restrictedCoeffHom_eq_of_opens_disjoint`). The three properties then follow from the
transport lemmas of `ContactStageKept`, with lower data on both sides (which canonical-tail theorem
`StepOneCanonicalTail.hasLowerDataL_of_isCanonical` supplies along canonical segments).

## Main results

* **`lowerValueL_zero_eq`** (the anchor): under lower data at level `0`, the lower value is
  `R(contactMarkedKept 𝔍 u T₀ W)(T₁|_W)(p)` for every tangent direction `u` on `U` and open `W ⊆ T₀⁻¹U` around the image of `p`
  missing the original members, with domain and canonical tail;
* **`lowerValueL_zero_isTowerIso`** (property (6)): along isomorphisms of towers `T₀' ≅ T₀` over `Φ : X' ≅ X` (last-stage map
  `χ₀`) and `T₁' ≅ T₁` over `χ₀` (last-stage map `χ`), with lower data for `Φ^*𝔍` at `p'` and for `𝔍` at `χ p'`, the two
  lower values agree (`origMembers_isTowerIso`: the original members correspond);
* **`lowerValueL_zero_restrict`** (property (5)): for `U ⊆ X` open and towers `T₀' ≅ T₀|_U` over `id_U`, `T₁' ≅ T₁|_{T₀⁻¹U}`
  (the split of `T|_U`, `BlowupTowerSplitIso.exists_isTowerIso_split_restrict`), with lower data for `𝔍|_U` at `p'` and for `𝔍`
  at the corresponding point, the two lower values agree (`origMembers_restrict`: the original members restrict);
* **`lowerValueL_zero_representative`** (property (7)): for restricted-equivalent `𝔍 ≃ 𝔍'` and lower data for both at the same
  point and split, the two lower values agree (`origMembers_restrictEquiv`: the original members do not depend on the
  representative);
* **`isAdmissibleCentre_of_contactMarkedKept`**, `isAdmissibleCentre_of_lowerMarkedM_zero` (the Step 1bb input of
  property (1) at the values `(0, λ)`): on every open `W''` of `T₁⁻¹W`, an admissible centre of the restriction of
  the transform of Step 1b's marked ideal along `T₁|_W` is an admissible centre of the restriction of `J̄_{T₀ T₁}`
  (same cosupport, same divisor);
* **`lowerValueL_zero_emptyPrefix`** (property (4'), the run of the point not reaching into the prefix): for `P`
  with only empty centres, lower data for `𝔍` at the split `(P H₀) T₁` and for `𝔍_P` at the split `H₀ T₁`, the two
  lower values agree (`ContactEmptyPrefix.contactMarkedKept_emptyPrefix` and the anchor on both sides);
  **`lowerValueL_zero_emptyPrefix_rebase`** (the run reaching into the prefix): for `P₁ P₂` with only empty centres,
  lower data for `𝔍` at the split `P₁ (P₂ T₁)` and for `𝔍_{P₁ P₂}` at the split `refl T₁`, the two lower values
  agree (re-basing across `P₂`, `StepOneCompare.lowerValue_eq_zero_rebase`, with `centresAvoid_of_isEmptyTower`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ContactLowerValue

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction HomogenizedIdealAlong MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupTowerIsomorphism ResolutionInvariantExt StepOneTangentChange ContactStageKept StepOneValue StepOneLowerDomain StepOneValueMasked MarkedIdealOperationsAlong.MarkedIdeal
open HomogenizedGlueingTower (strictAlong)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### The anchor: the lower value at level `0` through any tangent direction on any open set -/

section Anchor

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **The lower value at level `0` through any tangent direction** (the anchor): let `𝔍` be well formed with `d ≥ 1`, `T₀ T₁` a
multiple test blow-up of `J̄ = 𝓒_N(𝓗_N(𝔍))`, `p` a point of `cosupp J̄_{T₀ T₁}` with lower data at level `0` at the split
`T₀ T₁`, `u` a tangent direction of `(𝔍.ideal|_N, d)` on `U`, and `W ⊆ T₀⁻¹U` an open set of the stage `T₀` containing the
image of `p` and missing the original members, on which `contactMarkedKept 𝔍 u T₀ W` lies in the domain of `R` with `T₁|_W` a
canonical segment of it.  Then the lower value of `p` is the value of `R` for `contactMarkedKept 𝔍 u T₀ W` along `T₁|_W` at
`p` (the change of tangent direction on the two open sets, `StepOneTangentChange.inv_restrictedCoeffHom_eq_of_opens_disjoint`,
at the base point of `p`). -/
theorem lowerValueL_zero_eq (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) {Y₀ Z : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Z)
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {U : Set X} {u : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (W : Opens Y₀) (hWU : (W : Set Y₀) ⊆ T₀.proj ⁻¹' U)
    (hWE : ∀ H ∈ origMembers 𝔍 T₀, Disjoint (W : Set Y₀) H) (hdom : IsInvDomain k (contactMarkedKept 𝔍 u T₀ W))
    (hcan : IsCanonical (contactMarkedKept 𝔍 u T₀ W) (R.inv (contactMarkedKept 𝔍 u T₀ W)) (restrict W T₁))
    {p : Z} (hpW : T₁.proj p ∈ W) (hp : p ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp)
    (hD : LowerDataL R 𝔍 (lowerMarkedM 𝔍) 0 T₀ T₁ p) :
    lowerValueL R 𝔍 (lowerMarkedM 𝔍) 0 T₀ T₁ p =
      ((R.inv (contactMarkedKept 𝔍 u T₀ W) (restrict W T₁) ⟨p, hpW⟩ : Λ) : WithTop Λ) := by
  obtain ⟨h, hdom₀, hcan₀, -⟩ := hD
  rw [lowerValueL_eq_of_mem R 𝔍 _ h]
  congr 1
  -- the tangent direction chosen at the base point of `p`
  have hxv : T₀.proj (T₁.proj p) ∈ (tangentChoice 𝔍 (T₀.proj (T₁.proj p))).1 := (interior_subset h).1
  have hv := StepOneCompare.tangentChoice_spec_of_mem 𝔍 hxv
  have hxU : T₀.proj (T₁.proj p) ∈ U := hWU hpW
  -- the base point of `p` lies in the cosupport of `𝔍`
  have hx : T₀.proj (T₁.proj p) ∈ 𝔍.cosupp := by
    have hJ := isWellFormed_barMarked 𝔍 h𝔍
    have h1 := proj_mem_cosupp_of_mem_cosupp hJ.isClosedSubmanifold_N hJ.isCoherent _ hT hp
    rw [cosupp_barMarked 𝔍 h𝔍 hd, BlowupTower.proj_append] at h1
    exact h1
  obtain ⟨O, hxO, hO⟩ := inv_restrictedCoeffHom_eq_of_opens_disjoint R 𝔍 h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd hx
    hv hxv hu hxU
  have hmaskU : ((maskB 𝔍 T₀ (T₁.proj p) : Opens Y₀) : Set Y₀) ⊆
      T₀.proj ⁻¹' (tangentChoice 𝔍 (T₀.proj (T₁.proj p))).1 := fun z hz => (interior_subset hz).1
  have hdisj : ∀ H ∈ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).E.take 𝔍.E.length,
      Disjoint ((maskB 𝔍 T₀ (T₁.proj p) : Opens Y₀) : Set Y₀) H := fun H hH =>
    Set.disjoint_left.mpr fun z hz hzH => (interior_subset hz).2.1 H hH hzH
  exact hO T₀ T₁ hT (maskB 𝔍 T₀ (T₁.proj p)) W hmaskU hWU hdisj hWE hdom₀ hcan₀ hdom hcan ⟨p, h⟩ ⟨p, hpW⟩ rfl hxO hp

end Anchor

/-! ### Property (6): isomorphisms of towers -/

section TowerIso

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {k : ℕ} {Λ : Type v}
  [LinearOrder Λ]

/-- **The original members correspond along an isomorphism of multiple test blow-ups**: the original members of `Φ^*𝔍` at
the last stage of `T₀'` are the `χ₀`-preimages of those of `𝔍` at the last stage of `T₀`. -/
theorem origMembers_isTowerIso (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₀' Y₀ : CMfd.{u} n}
    {T₀' : BlowupTower X' Y₀'} {T₀ : BlowupTower X Y₀}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₀} (hiso : IsTowerIso Φ T₀' T₀ χ₀)
    (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) :
    origMembers (MarkedIdeal.pullback Φ 𝔍) T₀' = (origMembers 𝔍 T₀).map (χ₀ ⁻¹' ·) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  unfold origMembers
  rw [show barMarked (MarkedIdeal.pullback Φ 𝔍) = MarkedIdeal.pullback Φ (barMarked 𝔍) from
      barMarked_pullback Φ h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd,
    IsTowerIso.geoTransformAlong_eq Φ hJ.isClosedSubmanifold_N hJ.isCoherent hiso hT₀]
  show ((geoTransformAlong (barMarked 𝔍) T₀).E.map (χ₀ ⁻¹' ·)).take (𝔍.E.map (Φ ⁻¹' ·)).length = _
  rw [List.length_map, List.map_take]

/-- **Property (6) of the masked Step 1 value function at level `0`, lower values**: let `𝔍` be well formed with `d ≥ 1`,
`T₀' ≅ T₀` an isomorphism of towers over `Φ : X' ≅ X` with last-stage map `χ₀`, `T₁' ≅ T₁` one over `χ₀` with last-stage map
`χ` (the split of an isomorphism `T₀' T₁' ≅ T₀ T₁`, `BlowupTowerSplitIso.IsTowerIso.exists_split`), `T₀ T₁` a multiple test
blow-up of `J̄`, and `p'` a point with `χ p'` in `cosupp J̄_{T₀ T₁}`.  If `p'` has lower data at level `0` for `Φ^*𝔍` at the
split `T₀' T₁'` and `χ p'` has lower data at level `0` for `𝔍` at the split `T₀ T₁`, the two lower values agree.  (The marked
ideal of Step 1b on the mask of `χ p'` is transported along the isomorphisms with the tangent direction `w ∘ Φ`,
`ContactStageKept.inv_contactMarkedKept_isTowerIso`, and the anchor `lowerValueL_zero_eq` for `Φ^*𝔍` changes `w ∘ Φ` to the
tangent direction chosen for `Φ^*𝔍`.) -/
theorem lowerValueL_zero_isTowerIso (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) {Y₀' Y₀ Z' Z : CMfd.{u} n} {T₀' : BlowupTower X' Y₀'} {T₀ : BlowupTower X Y₀}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₀} (hiso : IsTowerIso Φ T₀' T₀ χ₀)
    {T₁' : BlowupTower Y₀' Z'} {T₁ : BlowupTower Y₀ Z} {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z}
    (hχ : IsTowerIso χ₀ T₁' T₁ χ) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {p' : Z'}
    (hp : χ p' ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp)
    (hD' : LowerDataL R (MarkedIdeal.pullback Φ 𝔍) (lowerMarkedM (MarkedIdeal.pullback Φ 𝔍)) 0 T₀' T₁' p')
    (hD : LowerDataL R 𝔍 (lowerMarkedM 𝔍) 0 T₀ T₁ (χ p')) :
    lowerValueL R (MarkedIdeal.pullback Φ 𝔍) (lowerMarkedM (MarkedIdeal.pullback Φ 𝔍)) 0 T₀' T₁' p' =
      lowerValueL R 𝔍 (lowerMarkedM 𝔍) 0 T₀ T₁ (χ p') := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔍' : (MarkedIdeal.pullback Φ 𝔍).IsWellFormed := MarkedIdealTowerTransport.IsWellFormed.pullback h𝔍
  have hbar : barMarked (MarkedIdeal.pullback Φ 𝔍) = MarkedIdeal.pullback Φ (barMarked 𝔍) :=
    barMarked_pullback Φ h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd
  have hT₀ : IsGeoTestTower (barMarked 𝔍) T₀ := ((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1
  have hiso' : IsTowerIso Φ (T₀'.append T₁') (T₀.append T₁) χ := hiso.append hχ
  -- the multiple test blow-up and the cosupport for `Φ^*𝔍`
  have hT' : IsGeoTestTower (barMarked (MarkedIdeal.pullback Φ 𝔍)) (T₀'.append T₁') := by
    rw [hbar]
    exact (IsTowerIso.isGeoTestTower_iff Φ hJ.isClosedSubmanifold_N hJ.isCoherent hiso').mpr hT
  have hp' : p' ∈ (geoTransformAlong (barMarked (MarkedIdeal.pullback Φ 𝔍)) (T₀'.append T₁')).cosupp := by
    rw [hbar, IsTowerIso.cosupp_geoTransformAlong Φ hJ.isClosedSubmanifold_N hJ.isCoherent hiso' hT]
    exact hp
  -- the images of `p'` and `χ p'` in the stages `T₀'`, `T₀`, and the base points
  have hy : χ₀ (T₁'.proj p') = T₁.proj (χ p') := hχ.proj_comm p'
  have hx : Φ (T₀'.proj (T₁'.proj p')) = T₀.proj (T₁.proj (χ p')) := by
    rw [hiso.proj_comm, hy]
  -- the data on the side of `𝔍`: the mask `W` of `χ p'` and the tangent direction `w` chosen at its base point
  obtain ⟨h, hdom, hcan, hcos⟩ := hD
  have hxw : T₀.proj (T₁.proj (χ p')) ∈ (tangentChoice 𝔍 (T₀.proj (T₁.proj (χ p')))).1 := (interior_subset h).1
  have hw := StepOneCompare.tangentChoice_spec_of_mem 𝔍 hxw
  set W : Opens Y₀ := maskB 𝔍 T₀ (T₁.proj (χ p')) with hWdef
  set w : X → ℂ := (tangentChoice 𝔍 (T₀.proj (T₁.proj (χ p')))).2 with hwdef
  -- its preimage `W'` in the stage `T₀'`
  set W' : Opens Y₀' := ⟨χ₀ ⁻¹' (W : Set Y₀), W.isOpen.preimage χ₀.continuous⟩ with hW'def
  have hW' : ∀ q, q ∈ W' ↔ χ₀ q ∈ W := fun _ => Iff.rfl
  obtain ⟨hdomA, hcanA, hvalA⟩ := inv_contactMarkedKept_isTowerIso Φ R h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd hiso
    hT₀ w hW' hχ hdom hcan
  have hpW' : T₁'.proj p' ∈ W' := by
    show χ₀ (T₁'.proj p') ∈ W
    rw [hy]
    exact h
  -- the anchor for `Φ^*𝔍` with the tangent direction `w ∘ Φ` on `W'`
  have hwΦ : IsTangentDirectionAlong (MarkedIdeal.pullback Φ 𝔍).N (MarkedIdeal.pullback Φ 𝔍).ideal
      (MarkedIdeal.pullback Φ 𝔍).d (Φ ⁻¹' (tangentChoice 𝔍 (T₀.proj (T₁.proj (χ p')))).1) (w ∘ Φ) :=
    ContactMarkedCanonical.isTangentDirectionAlong_comp Φ h𝔍.isCoherent hw
  have hW'U : (W' : Set Y₀') ⊆ T₀'.proj ⁻¹' (Φ ⁻¹' (tangentChoice 𝔍 (T₀.proj (T₁.proj (χ p')))).1) := by
    intro q hq
    have h1 : χ₀ q ∈ (W : Set Y₀) := hq
    show Φ (T₀'.proj q) ∈ (tangentChoice 𝔍 (T₀.proj (T₁.proj (χ p')))).1
    rw [hiso.proj_comm]
    exact (interior_subset h1).1
  have hW'E : ∀ H ∈ origMembers (MarkedIdeal.pullback Φ 𝔍) T₀', Disjoint (W' : Set Y₀') H := by
    intro H hH
    rw [origMembers_isTowerIso Φ 𝔍 h𝔍 hd hiso hT₀] at hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    refine Set.disjoint_left.mpr fun q hq hqH => ?_
    have h1 : χ₀ q ∈ (W : Set Y₀) := hq
    exact (interior_subset h1).2.1 H₀ hH₀ hqH
  have key := lowerValueL_zero_eq R (MarkedIdeal.pullback Φ 𝔍) h𝔍' hd T₀' T₁' hT' hwΦ W' hW'U hW'E hdomA hcanA hpW' hp'
    hD'
  rw [key, lowerValueL_eq_of_mem R 𝔍 _ h]
  congr 1
  exact hvalA ⟨p', hpW'⟩ ⟨χ p', h⟩ rfl hcos

end TowerIso

/-! ### Property (5): restriction to an open set of the base -/

section Restrict

variable {X : CMfd.{u} n} (U : Opens X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **The original members on a restricted tower**: the original members of `𝔍|_U` at the last stage of `T₀|_U` are the
traces on `T₀⁻¹U` of those of `𝔍` at the last stage of `T₀`. -/
theorem origMembers_restrict (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₀ : CMfd.{u} n}
    {T₀ : BlowupTower X Y₀} (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) :
    origMembers (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T₀) =
      (origMembers 𝔍 T₀).map ((Subtype.val : openPreimage T₀ U → Y₀) ⁻¹' ·) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hbarU : barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
      MarkedIdeal.pullback (Subtype.val : U → X) (barMarked 𝔍) :=
    barMarked_pullback_val U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd
  have hg : geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T₀) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (geoTransformAlong (barMarked 𝔍) T₀) := by
    rw [hbarU]
    exact geoTransformAlong_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  show (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T₀)).E.take
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).E.length = _
  rw [hg]
  show ((geoTransformAlong (barMarked 𝔍) T₀).E.map ((Subtype.val : openPreimage T₀ U → Y₀) ⁻¹' ·)).take
      (𝔍.E.map ((Subtype.val : U → X) ⁻¹' ·)).length = _
  rw [List.length_map, ← List.map_take]
  rfl

/-- **Property (5) of the masked Step 1 value function at level `0`, lower values**: let `𝔍` be well formed with `d ≥ 1`,
`U ⊆ X` open, `T₀ T₁` a multiple test blow-up of `J̄`, and `T₀'`, `T₁'` towers over `U` isomorphic over `id_U` to `T₀|_U` and,
over the last-stage map `χ₀` of the first isomorphism, to `T₁|_{T₀⁻¹U}` (last-stage map `χ`) -- the shape in which the split of
`T|_U` is the restriction of the split of `T`, `BlowupTowerSplitIso.exists_isTowerIso_split_restrict`.  If `p'` has lower data
at level `0` for `𝔍|_U` at the split `T₀' T₁'`, the point `χ p'` (of `T₀ T₁`) lies in `cosupp J̄_{T₀ T₁}` and has lower data at
level `0` for `𝔍` at the split `T₀ T₁`, the two lower values agree.  (The marked ideal of Step 1b on the mask of `χ p'` is shrunk
to its part over `U` (`MaxLocusLocal.restrict_nestedOpens`), restricted to `U` (`ContactStageKept.inv_contactMarkedKept_restrict`),
transported along the isomorphisms over `id_U` (`ContactStageKept.inv_contactMarkedKept_isTowerIso`), and the anchor
`lowerValueL_zero_eq` for `𝔍|_U` changes `w ∘ ι` to the tangent direction chosen for `𝔍|_U`.) -/
theorem lowerValueL_zero_restrict (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) {Y₀ Z Y₀' Z' : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Z}
    {T₀' : BlowupTower (CMfd.of (n := n) U) Y₀'}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₀ U)}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) T₀' (restrict U T₀) χ₀)
    {T₁' : BlowupTower Y₀' Z'}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ U))}
    (hχ : IsTowerIso χ₀ T₁' (restrict (openPreimage T₀ U) T₁) χ) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁))
    {p' : Z'} (hp : ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈
      (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp)
    (hD' : LowerDataL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
      (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) 0 T₀' T₁' p')
    (hD : LowerDataL R 𝔍 (lowerMarkedM 𝔍) 0 T₀ T₁ ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)) :
    lowerValueL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) 0 T₀' T₁' p' =
      lowerValueL R 𝔍 (lowerMarkedM 𝔍) 0 T₀ T₁ ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔍U : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val h𝔍 U
  have hJU := isWellFormed_barMarked (X := CMfd.of (n := n) U) _ h𝔍U
  have hbarU : barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
      MarkedIdeal.pullback (Subtype.val : U → X) (barMarked 𝔍) :=
    barMarked_pullback_val U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  -- the restricted towers
  have hT₀U : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T₀) := by
    rw [hbarU]
    exact isGeoTestTower_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  have hgU : geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T₀) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (geoTransformAlong (barMarked 𝔍) T₀) := by
    rw [hbarU]
    exact geoTransformAlong_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  have hRU : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      ((restrict U T₀).append (restrict (openPreimage T₀ U) T₁)) := by
    refine (isGeoTestTower_append_iff _ _ _).mpr ⟨hT₀U, ?_⟩
    rw [hgU]
    exact isGeoTestTower_restrict (openPreimage T₀ U) hNT hcT T₁ hT₁
  have hcosR : χ p' ∈ (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      ((restrict U T₀).append (restrict (openPreimage T₀ U) T₁))).cosupp := by
    rw [geoTransformAlong_append, hgU,
      ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hNT hcT (openPreimage T₀ U) T₁ hT₁, mem_preimage,
      ← geoTransformAlong_append]
    exact hp
  -- along the isomorphism over `id_U`
  have hiso' := hiso.append hχ
  have hpb : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) =
      barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) :=
    ContactCanonicalAlong.pullback_id _ hJU.isCoherent
  have hT' : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (T₀'.append T₁') := by
    have h1 := (IsTowerIso.isGeoTestTower_iff _ hJU.isClosedSubmanifold_N hJU.isCoherent hiso').mpr hRU
    rwa [hpb] at h1
  have hp' : p' ∈ (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (T₀'.append T₁')).cosupp := by
    have h1 := IsTowerIso.cosupp_geoTransformAlong _ hJU.isClosedSubmanifold_N hJU.isCoherent hiso' hRU
    rw [hpb] at h1
    rw [h1]
    exact hcosR
  -- the images of `p'` and `χ p'`
  have hy : χ₀ (T₁'.proj p') = (restrict (openPreimage T₀ U) T₁).proj (χ p') := hχ.proj_comm p'
  have hy' : (((restrict (openPreimage T₀ U) T₁).proj (χ p') : openPreimage T₀ U) : Y₀) =
      T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) := proj_restrict _ T₁ (χ p')
  -- the data on the side of `𝔍`: the mask `W` of `χ p'` and the tangent direction `w` chosen at its base point
  obtain ⟨h, hdom, hcan, -⟩ := hD
  have hxw : T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)) ∈
      (tangentChoice 𝔍 (T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))).1 :=
    (interior_subset h).1
  have hw := StepOneCompare.tangentChoice_spec_of_mem 𝔍 hxw
  set W : Opens Y₀ := maskB 𝔍 T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)) with hWdef
  set w : X → ℂ := (tangentChoice 𝔍 (T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))).2
    with hwdef
  set Uw : Set X := (tangentChoice 𝔍 (T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))).1
    with hUwdef
  -- (1) shrink the mask to its part over `U`
  set W₁ : Opens Y₀ := W ⊓ openPreimage T₀ U with hW₁def
  have hW₁W : W₁ ≤ W := inf_le_left
  have hW₁U : W₁ ≤ openPreimage T₀ U := inf_le_right
  have hcoh := isCoherent_restrictedCoeff 𝔍 h𝔍.isCoherent h𝔍.isClosedSubmanifold_N w T₀ hT₀
  obtain ⟨hdom₁, hcan₁, hval₁⟩ := MaxLocusLocal.restrict_nestedOpens R hcoh hW₁W hdom T₁ hcan
  have hpW₁ : T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈ W₁ := ⟨h, (χ p').2⟩
  have hcos₁ : (⟨((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z), hpW₁⟩ : openPreimage T₁ W₁) ∈
      (geoTransformAlong (contactMarkedKept 𝔍 w T₀ W₁) (restrict W₁ T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
      ⟨Uw, hw.isOpen⟩ hw T₀ T₁ hT W₁ fun y hy => (interior_subset (hW₁W hy)).1).2]
    exact hp
  have hv1 := hval₁ _ hcos₁
  -- (2) restrict to `U`
  obtain ⟨-, hcan₂, hval₂⟩ := inv_contactMarkedKept_restrict U R h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd T₀ hT₀ w
    hW₁U hdom₁ T₁ hcan₁
  have hdom₂ := (inv_contactMarkedKept_restrict U R h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd T₀ hT₀ w
    hW₁U hdom₁ T₁ hcan₁).1
  set W₂ : Opens (CMfd.of (n := n) (openPreimage T₀ U)) := MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁ with hW₂def
  have hq₂ : χ p' ∈ openPreimage (restrict (openPreimage T₀ U) T₁) W₂ := by
    show (((restrict (openPreimage T₀ U) T₁).proj (χ p') : openPreimage T₀ U) : Y₀) ∈ W₁
    rw [hy']
    exact hpW₁
  obtain ⟨hcosiff, hv2⟩ := hval₂ ⟨χ p', hq₂⟩ ⟨_, hpW₁⟩ rfl
  have hcos₂ := hcosiff.mpr hcos₁
  have hv2' := hv2 hcos₁
  -- (3) along the isomorphism over `id_U`
  set W' : Opens Y₀' := ⟨χ₀ ⁻¹' (W₂ : Set (CMfd.of (n := n) (openPreimage T₀ U))),
    W₂.isOpen.preimage χ₀.continuous⟩ with hW'def
  have hW' : ∀ q, q ∈ W' ↔ χ₀ q ∈ W₂ := fun _ => Iff.rfl
  obtain ⟨hdom₃, hcan₃, hval₃⟩ := inv_contactMarkedKept_isTowerIso
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) R h𝔍U.isCoherent h𝔍U.isClosedSubmanifold_N hd hiso
    hT₀U (w ∘ Subtype.val) hW' hχ hdom₂ hcan₂
  have hpbU : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) = MarkedIdeal.pullback (Subtype.val : U → X) 𝔍 :=
    ContactCanonicalAlong.pullback_id _ h𝔍U.isCoherent
  rw [hpbU] at hdom₃ hcan₃ hval₃
  have hpW' : T₁'.proj p' ∈ W' := by
    show χ₀ (T₁'.proj p') ∈ W₂
    rw [hy]
    exact hq₂
  have hv3 := hval₃ ⟨p', hpW'⟩ ⟨χ p', hq₂⟩ rfl hcos₂
  -- (4) the anchor for `𝔍|_U` with `w ∘ ι` on `W'`
  have hu : IsTangentDirectionAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).N
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).ideal (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).d
      ((Subtype.val : U → X) ⁻¹' Uw) (w ∘ Subtype.val) :=
    ContactMarkedCanonical.isTangentDirectionAlong_comp_val U h𝔍.isCoherent hw
  have hproj : ∀ q, (((T₀'.proj q : CMfd.of (n := n) U) : U) : X) = T₀.proj ((χ₀ q : openPreimage T₀ U) : Y₀) := by
    intro q
    have e : T₀'.proj q = (restrict U T₀).proj (χ₀ q) := hiso.proj_comm q
    rw [e, proj_restrict]
  have hW'U : (W' : Set Y₀') ⊆ T₀'.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' Uw) := by
    intro q hq
    have h1 : ((χ₀ q : openPreimage T₀ U) : Y₀) ∈ W₁ := hq
    show (((T₀'.proj q : CMfd.of (n := n) U) : U) : X) ∈ Uw
    rw [hproj]
    exact (interior_subset (hW₁W h1)).1
  have hW'E : ∀ H ∈ origMembers (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) T₀', Disjoint (W' : Set Y₀') H := by
    intro H hH
    have e := origMembers_isTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) _ h𝔍U hd hiso hT₀U
    rw [hpbU, origMembers_restrict U 𝔍 h𝔍 hd hT₀, List.map_map] at e
    rw [e] at hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    refine Set.disjoint_left.mpr fun q hq hqH => ?_
    have h1 : ((χ₀ q : openPreimage T₀ U) : Y₀) ∈ W₁ := hq
    exact (interior_subset (hW₁W h1)).2.1 H₀ hH₀ hqH
  have key := lowerValueL_zero_eq (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) h𝔍U hd T₀' T₁' hT' hu W' hW'U hW'E
    hdom₃ hcan₃ hpW' hp' hD'
  rw [key, lowerValueL_eq_of_mem R 𝔍 _ h]
  congr 1
  exact hv3.trans (hv2'.trans hv1)

end Restrict

/-! ### Property (7): independence of the representative -/

section Representative

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **The original members do not depend on the representative**: restricted-equivalent marked ideals have the same original
members along every tower (the divisor of a transform depends only on the divisor). -/
theorem origMembers_restrictEquiv {𝔍 𝔍' : MarkedIdeal n X} (hEq : RestrictEquiv 𝔍 𝔍') {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) : origMembers 𝔍' T₀ = origMembers 𝔍 T₀ := by
  unfold origMembers
  rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := barMarked 𝔍') (𝔫 := barMarked 𝔍)
    hEq.E_eq.symm T₀, hEq.E_eq]

/-- **Property (7) of the masked Step 1 value function at level `0`, lower values**: let `𝔍` be well formed with `d ≥ 1` and
`𝔍 ≃ 𝔍'` restricted-equivalent with `𝔍'` coherent, `T₀ T₁` a multiple test blow-up of `J̄ = 𝓒_N(𝓗_N(𝔍))` and `p` a point of
`cosupp J̄_{T₀ T₁}`.  If `p` has lower data at level `0` at the split `T₀ T₁` both for `𝔍` and for `𝔍'`, the two lower values
agree.  (Near the base point the tangent direction chosen for `𝔍` agrees on `N` with a tangent direction of `𝔍'`
(`ContactRepresentative.exists_isTangentDirectionAlong_of_restrictLe`); on the part of the mask of `𝔍` over that neighbourhood
the two marked ideals of Step 1b are restricted-equivalent with the same values (`ContactStageKept.contactMarkedKept_representative`),
and the anchor `lowerValueL_zero_eq` on both sides.) -/
theorem lowerValueL_zero_representative (R : ResolutionInvariant.{u, v} n k Λ) {𝔍 𝔍' : MarkedIdeal n X}
    (h𝔍 : 𝔍.IsWellFormed) (h𝔞' : 𝔍'.ideal.IsCoherent) (hd : 1 ≤ 𝔍.d) (hEq : RestrictEquiv 𝔍 𝔍') {Y₀ Z : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Z) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {p : Z}
    (hp : p ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp)
    (hD : LowerDataL R 𝔍 (lowerMarkedM 𝔍) 0 T₀ T₁ p) (hD' : LowerDataL R 𝔍' (lowerMarkedM 𝔍') 0 T₀ T₁ p) :
    lowerValueL R 𝔍 (lowerMarkedM 𝔍) 0 T₀ T₁ p = lowerValueL R 𝔍' (lowerMarkedM 𝔍') 0 T₀ T₁ p := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔍' : 𝔍'.IsWellFormed := by
    obtain ⟨hN, -, hS, hTr⟩ := h𝔍
    refine ⟨hEq.N_eq ▸ hN, h𝔞', hEq.E_eq ▸ hS, ?_⟩
    rw [← hEq.N_eq, ← hEq.E_eq]
    exact hTr
  have hd' : 1 ≤ 𝔍'.d := hEq.d_eq ▸ hd
  have hJ' := isWellFormed_barMarked 𝔍' h𝔍'
  have hT₀ : IsGeoTestTower (barMarked 𝔍) T₀ := ((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1
  -- `J̄` and `J̄'` are restricted-equivalent: the same multiple test blow-ups and cosupports
  have hJJ : RestrictEquiv (barMarked 𝔍) (barMarked 𝔍') :=
    ContactRepresentative.restrictEquiv_barMarked hEq h𝔍.isClosedSubmanifold_N h𝔍.isCoherent h𝔞'
  have hW := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hJJ hJ.isClosedSubmanifold_N.1 hJ.isCoherent
    hJ'.isCoherent
  have hT' : IsGeoTestTower (barMarked 𝔍') (T₀.append T₁) := ((hW.2 _).1).mp hT
  have hp' : p ∈ (geoTransformAlong (barMarked 𝔍') (T₀.append T₁)).cosupp := by
    rw [← (hW.2 _).2 hT]
    exact hp
  -- the data on the side of `𝔍`: the mask `W` of `p` and the tangent direction `w` chosen at its base point
  obtain ⟨h, hdom, hcan, -⟩ := id hD
  have hxw : T₀.proj (T₁.proj p) ∈ (tangentChoice 𝔍 (T₀.proj (T₁.proj p))).1 := (interior_subset h).1
  have hw := StepOneCompare.tangentChoice_spec_of_mem 𝔍 hxw
  set W : Opens Y₀ := maskB 𝔍 T₀ (T₁.proj p) with hWdef
  set w : X → ℂ := (tangentChoice 𝔍 (T₀.proj (T₁.proj p))).2 with hwdef
  set Uw : Set X := (tangentChoice 𝔍 (T₀.proj (T₁.proj p))).1 with hUwdef
  -- the base point lies in the cosupport, hence on `N`
  have hx : T₀.proj (T₁.proj p) ∈ 𝔍.cosupp := by
    have h1 := proj_mem_cosupp_of_mem_cosupp hJ.isClosedSubmanifold_N hJ.isCoherent _ hT hp
    rw [cosupp_barMarked 𝔍 h𝔍 hd, BlowupTower.proj_append] at h1
    exact h1
  -- a tangent direction `v` of `𝔍'` near the base point, equal to `w` on `N`
  obtain ⟨O, hxO, hOU, v, hv, hvw⟩ := ContactRepresentative.exists_isTangentDirectionAlong_of_restrictLe
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔍.isCoherent hg) h𝔞'
    h𝔍.isClosedSubmanifold_N hEq.le hw hxw (𝔍.cosupp_subset_N hx)
  have hv' : IsTangentDirectionAlong 𝔍'.N 𝔍'.ideal 𝔍'.d O v := by
    rw [← hEq.N_eq, ← hEq.d_eq]
    exact hv
  -- the part `W₁` of the mask over `O`
  set W₁ : Opens Y₀ := W ⊓ openPreimage T₀ O with hW₁def
  have hW₁W : W₁ ≤ W := inf_le_left
  have hW₁O : (W₁ : Set Y₀) ⊆ openPreimage T₀ O := fun _ hy => hy.2
  have hcoh := isCoherent_restrictedCoeff 𝔍 h𝔍.isCoherent h𝔍.isClosedSubmanifold_N w T₀ hT₀
  obtain ⟨hdom₁, hcan₁, -⟩ := MaxLocusLocal.restrict_nestedOpens R hcoh hW₁W hdom T₁ hcan
  have hpW₁ : T₁.proj p ∈ W₁ := ⟨h, hxO⟩
  have hW₁U : (W₁ : Set Y₀) ⊆ T₀.proj ⁻¹' Uw := fun _ hy => (interior_subset (hW₁W hy)).1
  have hW₁E : ∀ H ∈ origMembers 𝔍 T₀, Disjoint (W₁ : Set Y₀) H := fun H hH =>
    Set.disjoint_left.mpr fun _ hy hyH => (interior_subset (hW₁W hy)).2.1 H hH hyH
  have hW₁E' : ∀ H ∈ origMembers 𝔍' T₀, Disjoint (W₁ : Set Y₀) H := by
    rw [origMembers_restrictEquiv hEq T₀]
    exact hW₁E
  have hcos₁ : (⟨p, hpW₁⟩ : openPreimage T₁ W₁) ∈
      (geoTransformAlong (contactMarkedKept 𝔍 w T₀ W₁) (restrict W₁ T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
      ⟨Uw, hw.isOpen⟩ hw T₀ T₁ hT W₁ hW₁U).2]
    exact hp
  -- the two marked ideals of Step 1b on `W₁` are restricted-equivalent, with the same values
  obtain ⟨hdom₁', hrest⟩ := contactMarkedKept_representative R h𝔍.isCoherent h𝔞' h𝔍.isClosedSubmanifold_N hEq O
    (fun y hy hyN => (hvw y hy hyN).symm) T₀ hT₀ W₁ hW₁O hdom₁
  obtain ⟨hcan₁', hval⟩ := hrest (restrict W₁ T₁) hcan₁
  -- the anchor on both sides
  have key₁ := lowerValueL_zero_eq R 𝔍 h𝔍 hd T₀ T₁ hT hw W₁ hW₁U hW₁E hdom₁ hcan₁ hpW₁ hp hD
  have key₂ := lowerValueL_zero_eq R 𝔍' h𝔍' hd' T₀ T₁ hT' hv' W₁ hW₁O hW₁E' hdom₁' hcan₁' hpW₁ hp' hD'
  rw [key₁, key₂]
  congr 1
  exact hval _ hcos₁

end Representative

/-! ### Admissible centres: from the marked ideal of Step 1b to `J̄`, locally -/

section Admissible

variable {X : CMfd.{u} n}

/-- **Admissible centres of Step 1b's marked ideal are admissible for `J̄`, on every open set of the last stage** (the Step 1bb
input of property (1) of the masked Step 1 value function at the values `(0, λ)`; Włodarczyk's `le:S` for one centre): let `𝔍`
be well formed with `d ≥ 1`, `u` a tangent direction of `(𝔍.ideal|_N, d)` along `N` on `U`, `T₀ T₁` a multiple test blow-up of
`J̄ = 𝓒_N(𝓗_N(𝔍))`, and `W ⊆ T₀⁻¹U` open in the stage `T₀`.  On `P = T₁⁻¹W`, the transform of `contactMarkedKept 𝔍 u T₀ W` along
`T₁|_W` and the restriction of `J̄_{T₀ T₁}` have the same cosupport (`ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le`)
and the same divisor (the divisor of Step 1b's marked ideal is kept); so for every open `W''` of `P`, an admissible centre of the
restriction of the first to `W''` is one of the restriction of the second. -/
theorem isAdmissibleCentre_of_contactMarkedKept (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (U : Opens X)
    {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y₀ Z : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Z) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) (W : Opens Y₀)
    (hWU : (W : Set Y₀) ⊆ openPreimage T₀ U) (W'' : Opens (openPreimage T₁ W)) (C'' : Set W'')
    (h : (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ W)
      (geoTransformAlong (contactMarkedKept 𝔍 u T₀ W) (restrict W T₁))).IsAdmissibleCentre C'') :
    (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ W)
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ W → Z)
        (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)))).IsAdmissibleCentre C'' := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  obtain ⟨-, hcTT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent _ hT
  obtain ⟨hTW, hcosW⟩ := ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
    U hu T₀ T₁ hT W hWU
  -- the transform of the marked ideal of Step 1b along `T₁|_W` has a coherent ideal
  have hcohS : (contactMarkedKept 𝔍 u T₀ W).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff 𝔍 h𝔍.isCoherent h𝔍.isClosedSubmanifold_N u T₀ hT₀)
  have hNS : IsClosedSubmanifold n (contactMarkedKept 𝔍 u T₀ W).N :=
    ContactStageInvDomain.isClosedSubmanifold_strictAlong_stage_of_le 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd U hu T₀
      (((HomogenizedIdealAlongTower.coeff_homAlong_wEquiv 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd).2 T₀).1.mp hT₀) W hWU
  obtain ⟨-, hcA⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hNS hcohS _ hTW
  -- the same cosupport and the same divisor on `P = T₁⁻¹W`
  have hcos : (geoTransformAlong (contactMarkedKept 𝔍 u T₀ W) (restrict W T₁)).cosupp =
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ W → Z)
        (geoTransformAlong (barMarked 𝔍) (T₀.append T₁))).cosupp := by
    rw [hcosW, cosupp_pullback_val _
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcTT hg)]
  have hE : (geoTransformAlong (contactMarkedKept 𝔍 u T₀ W) (restrict W T₁)).E =
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ W → Z)
        (geoTransformAlong (barMarked 𝔍) (T₀.append T₁))).E := by
    rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := contactMarkedKept 𝔍 u T₀ W)
      (𝔫 := MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong (barMarked 𝔍) T₀)) rfl (restrict W T₁),
      geoTransformAlong_restrict W hNT hcT T₁ hT₁, geoTransformAlong_append]
  obtain ⟨hcl, hsub, hnc⟩ := h
  refine ⟨hcl, ?_, ?_⟩
  · rw [cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcTT) hg), ← hcos,
      ← cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcA hg)]
    exact hsub
  · show NormalCrossings.HasNormalCrossings n C'' ((MarkedIdeal.pullback (Subtype.val : openPreimage T₁ W → Z)
      (geoTransformAlong (barMarked 𝔍) (T₀.append T₁))).E.map ((Subtype.val : W'' → openPreimage T₁ W) ⁻¹' ·))
    rw [← hE]
    exact hnc

/-- **`isAdmissibleCentre_of_contactMarkedKept` for the masked lower marked ideal of level `0`**: at a point `y₀` of the stage
`T₀` lying in its mask, an admissible centre of the restriction to an open `W''` of `T₁⁻¹(mask)` of the transform of
`lowerMarkedM 𝔍 0 T₀ y₀` along the restricted tail is an admissible centre of the restriction of `J̄_{T₀ T₁}`. -/
theorem isAdmissibleCentre_of_lowerMarkedM_zero (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    {Y₀ Z : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Z)
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀} (hy₀ : y₀ ∈ lowerMask 𝔍 0 T₀ y₀)
    (W'' : Opens (openPreimage T₁ (lowerMask 𝔍 0 T₀ y₀))) (C'' : Set W'')
    (h : (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ (lowerMask 𝔍 0 T₀ y₀))
      (geoTransformAlong (lowerMarkedM 𝔍 0 T₀ y₀) (restrict (lowerMask 𝔍 0 T₀ y₀) T₁))).IsAdmissibleCentre C'') :
    (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ (lowerMask 𝔍 0 T₀ y₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ (lowerMask 𝔍 0 T₀ y₀) → Z)
        (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)))).IsAdmissibleCentre C'' := by
  have hx : T₀.proj y₀ ∈ (tangentChoice 𝔍 (T₀.proj y₀)).1 := (interior_subset hy₀).1
  have hw := StepOneCompare.tangentChoice_spec_of_mem 𝔍 hx
  exact isAdmissibleCentre_of_contactMarkedKept 𝔍 h𝔍 hd ⟨(tangentChoice 𝔍 (T₀.proj y₀)).1, hw.isOpen⟩ hw T₀ T₁ hT
    (maskB 𝔍 T₀ y₀) (fun z hz => (interior_subset hz).1) W'' C'' h

end Admissible

/-! ### Property (4'): an empty prefix of the base -/

section EmptyPrefix

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Property (4') of the masked Step 1 value function at level `0`, lower values, when the run of the point does not reach into
the empty prefix**: let `𝔍` be well formed with `d ≥ 1`, `P` a tower over `X` with only empty centres, `𝔍_P` the transform,
`P H₀ T₁` a multiple test blow-up of `J̄ = 𝓒_N(𝓗_N(𝔍))` and `z` a point of its cosupport.  If `z` has lower data at level `0` for
`𝔍` at the split `(P H₀) T₁` and for `𝔍_P` at the split `H₀ T₁`, the two lower values agree.  (On the part `W₁` of the mask of `𝔍`
lying in the mask of `𝔍_P`, Step 1b's marked ideal of `𝔍` along `P H₀` with the chosen `w` and that of `𝔍_P` along `H₀` with
`w ∘ p_P` have the same values (`ContactEmptyPrefix.contactMarkedKept_emptyPrefix`, after `MaxLocusLocal.restrict_nestedOpens`);
the anchor `lowerValueL_zero_eq` on both sides.) -/
theorem lowerValueL_zero_emptyPrefix (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) {Y Y₀ Z : CMfd.{u} n} (P : BlowupTower X Y) (hP : IsEmptyTower P) (H₀ : BlowupTower Y Y₀)
    (T₁ : BlowupTower Y₀ Z) (hT : IsGeoTestTower (barMarked 𝔍) ((P.append H₀).append T₁)) {z : Z}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) ((P.append H₀).append T₁)).cosupp)
    (hD : LowerDataL R 𝔍 (lowerMarkedM 𝔍) 0 (P.append H₀) T₁ z)
    (hD' : LowerDataL R (geoTransformAlong 𝔍 P) (lowerMarkedM (geoTransformAlong 𝔍 P)) 0 H₀ T₁ z) :
    lowerValueL R 𝔍 (lowerMarkedM 𝔍) 0 (P.append H₀) T₁ z =
      lowerValueL R (geoTransformAlong 𝔍 P) (lowerMarkedM (geoTransformAlong 𝔍 P)) 0 H₀ T₁ z := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hPt : IsGeoTestTower 𝔍 P := isGeoTestTower_of_isEmptyTower 𝔍 P hP
  have h𝔍P : (geoTransformAlong 𝔍 P).IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔍 P hPt
  have hdP : 1 ≤ (geoTransformAlong 𝔍 P).d := by
    rw [d_geoTransformAlong]
    exact hd
  have hJP := isWellFormed_barMarked _ h𝔍P
  have hT₀ : IsGeoTestTower (barMarked 𝔍) (P.append H₀) := ((isGeoTestTower_append_iff _ _ T₁).mp hT).1
  -- the side of `𝔍_P`: the multiple test blow-up and the cosupport
  have hT' : IsGeoTestTower (barMarked (geoTransformAlong 𝔍 P)) (H₀.append T₁) := by
    refine (ContactEmptyPrefix.isGeoTestTower_barMarked_geoTransformAlong_iff 𝔍 hN h𝔞 hd P hP (H₀.append T₁)).mpr ?_
    rw [← BlowupTower.append_assoc]
    exact hT
  have hJJ := ContactEmptyPrefix.restrictEquiv_barMarked_geoTransformAlong_of_isEmptyTower 𝔍 hN h𝔞 hd P hP
  obtain ⟨-, hcJP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent P
    (isGeoTestTower_of_isEmptyTower _ P hP)
  have hW := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hJJ hJP.isClosedSubmanifold_N.1 hJP.isCoherent hcJP
  have hp' : z ∈ (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) (H₀.append T₁)).cosupp := by
    rw [(hW.2 _).2 hT', ← geoTransformAlong_append, ← BlowupTower.append_assoc]
    exact hz
  -- the side of `𝔍`: the mask `W` and the tangent direction `w` chosen at the base point
  obtain ⟨h, hdom, hcan, -⟩ := id hD
  have hxw : (P.append H₀).proj (T₁.proj z) ∈ (tangentChoice 𝔍 ((P.append H₀).proj (T₁.proj z))).1 :=
    (interior_subset h).1
  have hw := StepOneCompare.tangentChoice_spec_of_mem 𝔍 hxw
  set W : Opens Y₀ := maskB 𝔍 (P.append H₀) (T₁.proj z) with hWdef
  set w : X → ℂ := (tangentChoice 𝔍 ((P.append H₀).proj (T₁.proj z))).2 with hwdef
  set Uw : Set X := (tangentChoice 𝔍 ((P.append H₀).proj (T₁.proj z))).1 with hUwdef
  -- the part `W₁` of `W` in the mask of `𝔍_P`
  obtain ⟨h', -⟩ := id hD'
  set W₁ : Opens Y₀ := W ⊓ maskB (geoTransformAlong 𝔍 P) H₀ (T₁.proj z) with hW₁def
  have hW₁W : W₁ ≤ W := inf_le_left
  have hcoh := isCoherent_restrictedCoeff 𝔍 h𝔞 hN w (P.append H₀) hT₀
  obtain ⟨hdom₁, hcan₁, -⟩ := MaxLocusLocal.restrict_nestedOpens R hcoh hW₁W hdom T₁ hcan
  have hpW₁ : T₁.proj z ∈ W₁ := ⟨h, h'⟩
  have hW₁U : (W₁ : Set Y₀) ⊆ (P.append H₀).proj ⁻¹' Uw := fun _ hy => (interior_subset (hW₁W hy)).1
  have hW₁E : ∀ H ∈ origMembers 𝔍 (P.append H₀), Disjoint (W₁ : Set Y₀) H := fun H hH =>
    Set.disjoint_left.mpr fun _ hy hyH => (interior_subset (hW₁W hy)).2.1 H hH hyH
  have hcos₁ : (⟨z, hpW₁⟩ : openPreimage T₁ W₁) ∈
      (geoTransformAlong (contactMarkedKept 𝔍 w (P.append H₀) W₁) (restrict W₁ T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 hN h𝔞 hd ⟨Uw, hw.isOpen⟩ hw (P.append H₀) T₁ hT W₁
      hW₁U).2]
    exact hz
  -- across the empty prefix `P`
  obtain ⟨hdomP, hrest⟩ := ContactEmptyPrefix.contactMarkedKept_emptyPrefix 𝔍 R hN h𝔞 hd ⟨Uw, hw.isOpen⟩ hw P hP H₀ hT₀ W₁
    hW₁U hdom₁
  obtain ⟨hcanP, hvalP⟩ := hrest (restrict W₁ T₁) hcan₁
  -- the anchor on both sides
  have huP : IsTangentDirectionAlong (geoTransformAlong 𝔍 P).N (geoTransformAlong 𝔍 P).ideal (geoTransformAlong 𝔍 P).d
      (P.proj ⁻¹' Uw) (w ∘ P.proj) := by
    rw [d_geoTransformAlong]
    exact (ContactEmptyPrefix.isTangentDirectionAlong_geoTransformAlong_of_isEmptyTower 𝔍 hN h𝔞 hw P hP).1
  have hW₁U' : (W₁ : Set Y₀) ⊆ H₀.proj ⁻¹' (P.proj ⁻¹' Uw) := by
    intro y hy
    have h1 := hW₁U hy
    rw [mem_preimage, BlowupTower.proj_append] at h1
    exact h1
  have hW₁M : W₁ ≤ maskB (geoTransformAlong 𝔍 P) H₀ (T₁.proj z) := inf_le_right
  have hW₁E' : ∀ H ∈ origMembers (geoTransformAlong 𝔍 P) H₀, Disjoint (W₁ : Set Y₀) H := fun H hH =>
    Set.disjoint_left.mpr fun _ hy hyH => (interior_subset (hW₁M hy)).2.1 H hH hyH
  have key₀ := lowerValueL_zero_eq R 𝔍 h𝔍 hd (P.append H₀) T₁ hT hw W₁ hW₁U hW₁E hdom₁ hcan₁ hpW₁ hz hD
  have key₁ := lowerValueL_zero_eq R (geoTransformAlong 𝔍 P) h𝔍P hdP H₀ T₁ hT' huP W₁ hW₁U' hW₁E' hdomP hcanP hpW₁ hp'
    hD'
  rw [key₀, key₁]
  congr 1
  exact hvalP _ hcos₁

/-- **The centres of a tower with only empty centres miss every open set.** -/
theorem centresAvoid_of_isEmptyTower {Y₁ : CMfd.{u} n} (W : Opens Y₁) :
    ∀ {Y : CMfd.{u} n} (M : BlowupTower Y₁ Y), IsEmptyTower M → RestrictEmptyTower.CentresAvoid W M
  | _, .refl, _ => trivial
  | _, .step M C _ _, h => by
      obtain ⟨hM, hC⟩ : IsEmptyTower M ∧ C = ∅ := h
      exact ⟨centresAvoid_of_isEmptyTower W M hM, by rw [hC]; exact Set.empty_disjoint _⟩

/-- **Property (4') of the masked Step 1 value function at level `0`, lower values, when the run of the point reaches
into the empty prefix**: let `𝔍` be well formed with `d ≥ 1`, `P₁ P₂` a tower over `X` with only empty centres, `P₁
P₂ T₁` a multiple test blow-up of `J̄` and `z` a point of its cosupport. If `z` has lower data at level `0` for `𝔍`
at the split `P₁ (P₂ T₁)` and for `𝔍_{P₁ P₂}` at the split `refl T₁`, the two lower values agree. (The value for `𝔍`
is re-based across the empty `P₂` (`StepOneCompare.lowerValue_eq_zero_rebase`), then carried across the empty prefix
`P₁ P₂` as in `lowerValueL_zero_emptyPrefix`.) -/
theorem lowerValueL_zero_emptyPrefix_rebase (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X)
    (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₁ Y Z : CMfd.{u} n} (P₁ : BlowupTower X Y₁) (P₂ : BlowupTower Y₁ Y)
    (hP : IsEmptyTower (P₁.append P₂)) (T₁ : BlowupTower Y Z) (hT : IsGeoTestTower (barMarked 𝔍) ((P₁.append P₂).append T₁))
    {z : Z} (hz : z ∈ (geoTransformAlong (barMarked 𝔍) ((P₁.append P₂).append T₁)).cosupp)
    (hD : LowerDataL R 𝔍 (lowerMarkedM 𝔍) 0 P₁ (P₂.append T₁) z)
    (hD' : LowerDataL R (geoTransformAlong 𝔍 (P₁.append P₂)) (lowerMarkedM (geoTransformAlong 𝔍 (P₁.append P₂))) 0
      BlowupTower.refl T₁ z) :
    lowerValueL R 𝔍 (lowerMarkedM 𝔍) 0 P₁ (P₂.append T₁) z =
      lowerValueL R (geoTransformAlong 𝔍 (P₁.append P₂)) (lowerMarkedM (geoTransformAlong 𝔍 (P₁.append P₂))) 0
        BlowupTower.refl T₁ z := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hP₂ : IsEmptyTower P₂ := ((BlowupTowerSplit.isEmptyTower_append_iff P₁ P₂).mp hP).2
  have hPt : IsGeoTestTower 𝔍 (P₁.append P₂) := isGeoTestTower_of_isEmptyTower 𝔍 _ hP
  have h𝔍P : (geoTransformAlong 𝔍 (P₁.append P₂)).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔍 _ hPt
  have hdP : 1 ≤ (geoTransformAlong 𝔍 (P₁.append P₂)).d := by
    rw [d_geoTransformAlong]
    exact hd
  have hJP := isWellFormed_barMarked _ h𝔍P
  have hT₀ : IsGeoTestTower (barMarked 𝔍) (P₁.append P₂) := ((isGeoTestTower_append_iff _ _ T₁).mp hT).1
  -- the side of `𝔍_{P₁P₂}`: the multiple test blow-up and the cosupport
  have hT' : IsGeoTestTower (barMarked (geoTransformAlong 𝔍 (P₁.append P₂))) (BlowupTower.refl.append T₁) := by
    rw [BlowupTower.refl_append]
    exact (ContactEmptyPrefix.isGeoTestTower_barMarked_geoTransformAlong_iff 𝔍 hN h𝔞 hd _ hP T₁).mpr hT
  have hJJ := ContactEmptyPrefix.restrictEquiv_barMarked_geoTransformAlong_of_isEmptyTower 𝔍 hN h𝔞 hd _ hP
  obtain ⟨-, hcJP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
    (P₁.append P₂) (isGeoTestTower_of_isEmptyTower _ _ hP)
  have hW := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hJJ hJP.isClosedSubmanifold_N.1 hJP.isCoherent hcJP
  have hp' : z ∈ (geoTransformAlong (barMarked (geoTransformAlong 𝔍 (P₁.append P₂)))
      (BlowupTower.refl.append T₁)).cosupp := by
    rw [(hW.2 _).2 hT', BlowupTower.refl_append, ← geoTransformAlong_append]
    exact hz
  -- re-basing the value of `𝔍` across the empty `P₂`
  have hTr : IsGeoTestTower (barMarked 𝔍) ((P₁.append P₂).append T₁) := hT
  obtain ⟨hq, hdomS, hcanS, hval⟩ := StepOneCompare.lowerValue_eq_zero_rebase R 𝔍 h𝔍 hd P₁ P₂ T₁ hTr hD
    (centresAvoid_of_isEmptyTower _ P₂ hP₂)
  obtain ⟨h₁, -⟩ := id hD
  have hxv : P₁.proj ((P₂.append T₁).proj z) ∈ (tangentChoice 𝔍 (P₁.proj ((P₂.append T₁).proj z))).1 :=
    (interior_subset h₁).1
  have hv := StepOneCompare.tangentChoice_spec_of_mem 𝔍 hxv
  set W₂ : Opens Y := openPreimage P₂ (maskB 𝔍 P₁ ((P₂.append T₁).proj z)) with hW₂def
  set v : X → ℂ := (tangentChoice 𝔍 (P₁.proj ((P₂.append T₁).proj z))).2 with hvdef
  set Uv : Set X := (tangentChoice 𝔍 (P₁.proj ((P₂.append T₁).proj z))).1 with hUvdef
  -- the part `W₃` of `W₂` in the mask of `𝔍_{P₁P₂}`
  obtain ⟨h', -⟩ := id hD'
  set W₃ : Opens Y := W₂ ⊓ maskB (geoTransformAlong 𝔍 (P₁.append P₂)) BlowupTower.refl (T₁.proj z) with hW₃def
  have hW₃W : W₃ ≤ W₂ := inf_le_left
  have hW₃M : W₃ ≤ maskB (geoTransformAlong 𝔍 (P₁.append P₂)) BlowupTower.refl (T₁.proj z) := inf_le_right
  have hcoh := isCoherent_restrictedCoeff 𝔍 h𝔞 hN v (P₁.append P₂) hT₀
  obtain ⟨hdom₃, hcan₃, hval₃⟩ := MaxLocusLocal.restrict_nestedOpens R hcoh hW₃W hdomS T₁ hcanS
  have hpW₃ : T₁.proj z ∈ W₃ := ⟨hq, h'⟩
  have hW₃U : (W₃ : Set Y) ⊆ (P₁.append P₂).proj ⁻¹' Uv := by
    intro y hy
    have h1 : P₂.proj y ∈ maskB 𝔍 P₁ ((P₂.append T₁).proj z) := hW₃W hy
    rw [mem_preimage, BlowupTower.proj_append]
    exact (interior_subset h1).1
  have hcos₃ : (⟨z, hpW₃⟩ : openPreimage T₁ W₃) ∈
      (geoTransformAlong (contactMarkedKept 𝔍 v (P₁.append P₂) W₃) (restrict W₃ T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 hN h𝔞 hd ⟨Uv, hv.isOpen⟩ hv (P₁.append P₂) T₁ hT W₃
      hW₃U).2]
    exact hz
  -- across the empty prefix `P₁ P₂`
  obtain ⟨hdomP, hrest⟩ := ContactEmptyPrefix.contactMarkedKept_emptyPrefix 𝔍 R hN h𝔞 hd ⟨Uv, hv.isOpen⟩ hv
    (P₁.append P₂) hP BlowupTower.refl hT₀ W₃ hW₃U hdom₃
  obtain ⟨hcanP, hvalP⟩ := hrest (restrict W₃ T₁) hcan₃
  -- the anchor on the side of `𝔍_{P₁P₂}`
  have huP : IsTangentDirectionAlong (geoTransformAlong 𝔍 (P₁.append P₂)).N (geoTransformAlong 𝔍 (P₁.append P₂)).ideal
      (geoTransformAlong 𝔍 (P₁.append P₂)).d ((P₁.append P₂).proj ⁻¹' Uv) (v ∘ (P₁.append P₂).proj) := by
    rw [d_geoTransformAlong]
    exact (ContactEmptyPrefix.isTangentDirectionAlong_geoTransformAlong_of_isEmptyTower 𝔍 hN h𝔞 hv _ hP).1
  have hW₃U' : (W₃ : Set Y) ⊆ (BlowupTower.refl : BlowupTower Y Y).proj ⁻¹' ((P₁.append P₂).proj ⁻¹' Uv) := hW₃U
  have hW₃E' : ∀ H ∈ origMembers (geoTransformAlong 𝔍 (P₁.append P₂)) BlowupTower.refl, Disjoint (W₃ : Set Y) H :=
    fun H hH => Set.disjoint_left.mpr fun _ hy hyH => (interior_subset (hW₃M hy)).2.1 H hH hyH
  have key₁ := lowerValueL_zero_eq R (geoTransformAlong 𝔍 (P₁.append P₂)) h𝔍P hdP BlowupTower.refl T₁ hT' huP W₃ hW₃U'
    hW₃E' hdomP hcanP hpW₃ hp' hD'
  rw [hval, key₁]
  congr 1
  exact (hval₃ _ hcos₃).symm.trans (hvalP _ hcos₃)

end EmptyPrefix

end

end Hironaka.ContactLowerValue
