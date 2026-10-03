/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.NonmonomialStepAlong
import Hironaka.Invariant.CodimOnePartTowerAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupBiholomorphismLift
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CodimOnePartCanonical
import Hironaka.Invariant.CompanionReduction
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.MonomialBlowupAlongChart
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The domain of a resolution invariant along multiple test blow-ups, open sets and biholomorphisms

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2 of Proposition `pr:resol` (the companion ideal is formed
from the transform at a later stage); Bierstone--Milman 2008 §§4--6.

The invariant of `hir:centre-function` (`ResolutionInvariantSpec.ResolutionInvariant`) is defined on the marked ideals
of `ResolutionInvariantSpec.IsInvDomain k`: well formed, `dim N ≤ k`, `d ≥ 1`, and `𝔞|_N` vanishing identically near no
point of `N`.  The general step forms the companion ideal from the transform `𝔪_T` at a later stage `T` of a canonical
segment, and Step 1 forms its restricted marked ideals there; restriction to open sets and biholomorphisms (properties
(5), (6)) are applied to them.  This module shows that the domain is stable under these three operations.  The one
nontrivial point is that a transform stays nonzero along the strict transform `N'` at the points over the centre, for
every admissible centre (no bound on the order on the centre is needed, unlike
`NonmonomialStepAlong.isNonzeroAlongAt_geoTransform`): off the centre the pullback of a germ nonzero along `N` is one,
and over the centre the coherence of the transform and the density of `N' \ π⁻¹C` in `N'` exclude the vanishing of every
germ on `N'` near the point.

## Main results

* `isNonzeroAlongAt_geoTransform_of_notMem`, `isNonzeroAlongAt_geoTransform_of_isAdmissibleCentre`: one blowup;
* `isNonzeroAlongAt_geoTransformAlong`: along every multiple test blow-up (`N` closed submanifold, coherent ideal);
* `dimLE_geoStrictTransform`, `dimLE_geoTransformAlong`: `dim N_T ≤ k` (pointwise dimension of the strict transform);
* `isInvDomain_geoTransformAlong`: `IsInvDomain k 𝔪 → IsInvDomain k 𝔪_T` along every multiple test blow-up;
* `isInvDomain_pullback`, `isInvDomain_pullback_val`: the domain is invariant under biholomorphisms and restriction to
  open sets.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.InvDomainTowerAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupStrictSubmanifold Hironaka.DivisorExponentAlong Hironaka.ResolutionInvariantSpec Hironaka.GermIdealOrder Hironaka.RelativePrincipalizationSpan Hironaka.InvertibleIdealQuotient Hironaka.MarkedIdealBiholomorphism

noncomputable section

variable {n : ℕ}

/-! ### One blowup -/

section Step

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X}

/-- **Off the centre the transform stays nonzero along the strict transform**: if `π y ∉ C` and the coherent ideal of
`𝔪` is nonzero along `N` at `π y`, the transform is nonzero along `N'` at `y` (the pullback `a ∘ π` of a germ `a`
nonzero along `N` lies in the transform on `N'` near `y`, and does not vanish identically on `N'` near `y`, along the
holomorphic section of `π` over `X \ C`). -/
theorem isNonzeroAlongAt_geoTransform_of_notMem (hπ : IsBlowupAlong n C π) (𝔪 : MarkedIdeal n X)
    (h𝔞 : 𝔪.ideal.IsCoherent) {y : Y} (hyC : π y ∉ C) (hnz : IsNonzeroAlongAt 𝔪.N 𝔪.ideal (π y)) :
    IsNonzeroAlongAt (𝔪.geoTransform C π).N (𝔪.geoTransform C π).ideal y := by
  obtain ⟨a, ha, hfreq⟩ := hnz
  have hmem : (GermIdeal.pullback (m := n) π 𝔪.ideal).mem y (a ∘ π) :=
    CompanionReduction.comp_mem_pullback' hπ h𝔞 ha
  have hahol : HolomorphicAt n (a ∘ π) y :=
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞 _ _ ha).comp_contMDiff
      (Eventually.of_forall fun q => hπ.contMDiff q)
  have hspan : IsInSpanOnAt (n := n) (𝔪.geoTransform C π).N ((𝔪.geoTransform C π).ideal.mem y) y (a ∘ π) :=
    (MonomialBlowupAlongChart.isInSpanOnAt_geoTransform_iff_pullback_of_notMem hπ 𝔪 hyC (a ∘ π)).mpr
      (IsInSpanAt.restrict (isInSpanAt_self hmem hahol))
  refine NonmonomialStepAlong.isNonzeroAlongAt_of_isInSpanOnAt hspan ?_
  obtain ⟨s, hs, hsπ, hsz⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hO : IsOpen Cᶜ := hπ.1.1.isOpen_compl
  have hcont : Tendsto s (𝓝 ⟨π y, hyC⟩) (𝓝 y) := by
    have h := hs.continuous.continuousAt (x := ⟨π y, hyC⟩)
    rwa [ContinuousAt, hsz y hyC] at h
  have hfreq' : ∃ᶠ p : ↥(Cᶜ : Set X) in 𝓝 ⟨π y, hyC⟩, p.1 ∈ 𝔪.N ∧ a p.1 ≠ 0 := by
    rw [nhds_subtype_eq_comap, Filter.frequently_comap]
    exact (hfreq.and_eventually (hO.mem_nhds hyC)).mono fun x ⟨hx, hxC⟩ => ⟨⟨x, hxC⟩, rfl, hx⟩
  refine hcont.frequently (hfreq'.mono fun p hp => ⟨?_, ?_⟩)
  · have hps : π (s p) = p.1 := congrFun hsπ p
    exact subset_closure (show π (s p) ∈ 𝔪.N \ C by rw [hps]; exact ⟨hp.1, p.2⟩)
  · have hps : π (s p) = p.1 := congrFun hsπ p
    simpa [Function.comp_apply, hps] using hp.2

/-- **The transform stays nonzero along the strict transform** (for every admissible centre): if `N` is a closed
submanifold and the coherent ideal of `𝔪` is nonzero along `N` at every point of `N`, then for every admissible centre
`C` the transform is nonzero along `N' = geoStrictTransform π C N` at every point of `N'`.  Over the centre: if every
germ of the (coherent) transform at `y` vanished on `N'` near `y`, every germ at every nearby point would vanish on
`N'` near that point (`CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt`), but points of
`N' \ π⁻¹C = π⁻¹(N \ C)` accumulate at `y` and the transform is nonzero along `N'` there. -/
theorem isNonzeroAlongAt_geoTransform_of_isAdmissibleCentre (hπ : IsBlowupAlong n C π) (𝔪 : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hC : 𝔪.IsAdmissibleCentre C)
    (hnz : ∀ x ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal x) :
    ∀ y ∈ (𝔪.geoTransform C π).N, IsNonzeroAlongAt (𝔪.geoTransform C π).N (𝔪.geoTransform C π).ideal y := by
  have hoff : ∀ y ∈ (𝔪.geoTransform C π).N, π y ∉ C →
      IsNonzeroAlongAt (𝔪.geoTransform C π).N (𝔪.geoTransform C π).ideal y := fun y hy hyC =>
    isNonzeroAlongAt_geoTransform_of_notMem hπ 𝔪 h𝔞 hyC
      (hnz (π y) (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy))
  intro y hy
  by_cases hyC : π y ∈ C
  · by_contra hcon
    have hcoh := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h𝔞 hC hπ
    have hev := CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt hcoh hcon
    have hfreq : ∃ᶠ z in 𝓝 y, z ∈ π ⁻¹' (𝔪.N \ C) := mem_closure_iff_frequently.mp hy
    obtain ⟨z, hz, hzev⟩ := (hfreq.and_eventually hev).exists
    have hzN' : z ∈ (𝔪.geoTransform C π).N := subset_closure hz
    obtain ⟨g, hg, hgfreq⟩ := hoff z hzN' hz.2
    obtain ⟨w, ⟨hwN, hgw⟩, hw⟩ := (hgfreq.and_eventually (hzev g hg)).exists
    exact hgw (hw hwN)
  · exact hoff y hy hyC

/-- **The dimension of the strict transform** (pointwise): if `N` is closed, `C ⊆ N` and `N` is regular of dimension
`≤ k` at each of its points, so is the strict transform `N'` (at `z` of the dimension of `N` at `π z`). -/
theorem dimLE_geoStrictTransform (hπ : IsBlowupAlong n C π) {N : Set X} (hNc : IsClosed N) (hCN : C ⊆ N) {k : ℕ}
    (hN : DimLE n N k) : DimLE n (geoStrictTransform π C N) k := by
  intro z hz
  have hπz : π z ∈ N := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNc hz
  obtain ⟨j, hjk, hj⟩ := hN (π z) hπz
  refine ⟨j, hjk, ?_⟩
  by_cases hzC : π z ∈ C
  · obtain ⟨kC, hkC⟩ := hπ.1.2 (π z) hzC
    exact regularAtDim_geoStrictTransform_of_mem hπ (le_of_regularAtDim_subset hkC hj hCN) hkC hj hCN hz
  · exact regularAtDim_geoStrictTransform_of_notMem hπ hNc hzC hj

end Step

/-! ### Along multiple test blow-ups -/

section Tower

variable {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}

/-- **Along every multiple test blow-up the transform stays nonzero along `N_T`** (`N` a closed submanifold, coherent
ideal nonzero along `N` at every point of `N`). -/
theorem isNonzeroAlongAt_geoTransformAlong (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hnz : ∀ x ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal x) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      ∀ y ∈ (geoTransformAlong 𝔪 T).N, IsNonzeroAlongAt (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal y
  | _, .refl, _ => hnz
  | _, .step T C π hπ, hT => by
      obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT.1
      rw [MarkedIdeal.geoTransformAlong_step]
      exact isNonzeroAlongAt_geoTransform_of_isAdmissibleCentre hπ _ hNT hcT hT.2
        (isNonzeroAlongAt_geoTransformAlong hN h𝔞 hnz T hT.1)

/-- **Along every multiple test blow-up `dim N_T ≤ k`** if `dim N ≤ k` (`N` a closed submanifold, coherent ideal). -/
theorem dimLE_geoTransformAlong (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) {k : ℕ}
    (hk : DimLE n 𝔪.N k) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T → DimLE n (geoTransformAlong 𝔪 T).N k
  | _, .refl, _ => hk
  | _, .step T C π hπ, hT => by
      obtain ⟨hNT, -⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT.1
      rw [MarkedIdeal.geoTransformAlong_step]
      exact dimLE_geoStrictTransform hπ hNT.1 hT.2.subset_N (dimLE_geoTransformAlong hN h𝔞 hk T hT.1)

/-- **The domain of a resolution invariant is stable along multiple test blow-ups** (`hir:centre-function`): if `𝔪` is
in `IsInvDomain k`, so is its transform along every multiple test blow-up -- well formed, `dim N_T ≤ k`, the same mark,
and nonzero along `N_T` at every point of `N_T`. -/
theorem isInvDomain_geoTransformAlong {k : ℕ} (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) : IsInvDomain k (geoTransformAlong 𝔪 T) where
  isWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT
  dimLE := dimLE_geoTransformAlong h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent h.dimLE T hT
  one_le_d := by rw [d_geoTransformAlong]; exact h.one_le_d
  isNonzeroAlongAt := isNonzeroAlongAt_geoTransformAlong h.isWellFormed.isClosedSubmanifold_N
    h.isWellFormed.isCoherent h.isNonzeroAlongAt T hT

end Tower

/-! ### Biholomorphisms and open sets -/

section Invariance

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **The domain is invariant under biholomorphisms**: `IsInvDomain k 𝔪 → IsInvDomain k (Φ^*𝔪)`. -/
theorem isInvDomain_pullback (Φ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M) {𝔪 : MarkedIdeal n M}
    {k : ℕ} (h : IsInvDomain k 𝔪) : IsInvDomain k (MarkedIdeal.pullback Φ 𝔪) where
  isWellFormed := MarkedIdealTowerTransport.IsWellFormed.pullback (Φ := Φ) h.isWellFormed
  dimLE := fun p hp => by
    obtain ⟨j, hjk, hj⟩ := h.dimLE (Φ p) hp
    exact ⟨j, hjk, (CodimOnePartCanonical.regularAtDim_preimage_iff Φ).mpr hj⟩
  one_le_d := h.one_le_d
  isNonzeroAlongAt := fun p hp => by
    obtain ⟨g, hg, hfreq⟩ := h.isNonzeroAlongAt (Φ p) hp
    refine ⟨g ∘ Φ, BlowupBiholomorphismLift.comp_mem_pullback_diffeo Φ h.isWellFormed.isCoherent hg, ?_⟩
    have hm : Filter.map Φ (𝓝 p) = 𝓝 (Φ p) := Φ.toHomeomorph.map_nhds_eq p
    rw [← hm] at hfreq
    exact Filter.frequently_map.mp hfreq

/-- **The domain is invariant under restriction to open sets**: `IsInvDomain k 𝔪 → IsInvDomain k (𝔪|_U)`. -/
theorem isInvDomain_pullback_val (U : Opens M) {𝔪 : MarkedIdeal n M} {k : ℕ} (h : IsInvDomain k 𝔪) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪) where
  isWellFormed := IsWellFormed.pullback_val h.isWellFormed U
  dimLE := fun p hp => by
    obtain ⟨j, hjk, hj⟩ := h.dimLE (p : M) hp
    exact ⟨j, hjk, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj⟩
  one_le_d := h.one_le_d
  isNonzeroAlongAt := fun p hp => by
    obtain ⟨g, hg, hfreq⟩ := h.isNonzeroAlongAt (p : M) hp
    refine ⟨g ∘ Subtype.val, comp_val_mem_pullback_val U h.isWellFormed.isCoherent hg, ?_⟩
    rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p] at hfreq
    exact Filter.frequently_map.mp hfreq

end Invariance

end

end Hironaka.InvDomainTowerAlong
