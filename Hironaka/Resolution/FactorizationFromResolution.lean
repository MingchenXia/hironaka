import Hironaka.Resolution.FactorizationDomain
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.BlowupCodimOne
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Analytic.ComponentComplementConnected
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.Resolution.EmbeddedFromResolution
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Blowup.BlowupConnected

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Relative principalization from given resolutions of marked ideals

Hironaka phase H5a (design I-0981 C-0161): the geometry of `hir:factorization-from-resolution`
(`blueprint/src/hironaka.tex`), with the two resolutions of the proof taken as hypotheses.  Blueprint
`mc:factorization-ambient`, `mc:factorization-thin-centre`, `mc:factorization-tower`, `mc:factorization-second`,
`mc:factorization-assembly` (`blueprint/src/maximal-contact.tex`).  Source: Copy-4
(`transcendental-nakamaye-copy4-20260911`), the proof of `lem:relative-principalization`, identities `eq:rp-induction`.

Let `𝔪 = (X, N, E, 𝔞, 1)` be a marked ideal with mark one, `N` a closed submanifold and `𝔞` coherent, and
`𝔪' = (X, X, E, 𝔞, 1)` the same data with `N` replaced by the whole manifold.  Along a multiple test blow-up `T` of `𝔪`
the ideal of the transform `𝔪_T` is an ideal of `𝒪_{N_T}`, represented by a colon ideal along `N_T`; the transform
`𝔪'_T` carries the ambient controlled transform `𝔞'_T = 𝒪(E_T)·T^*𝔞`.  Copy-4's third identity
`Res_{W_i} 𝔞_i = 𝔟_i` says that the two agree along `N_T`.

## Main results

* `ambient 𝔪`: the marked ideal `(X, X, E, 𝔞, d)`; `cosupp_eq_inter_zeroLocus` (mark one: `cosupp = N ∩ Z(𝔞)`);
* **`isGeoTestTower_and_restrictEquiv`**: every multiple test blow-up `T` of `𝔪` is one of `𝔪'`, and `𝔪_T` is
  restricted-equivalent to `𝔪_T` with its ideal replaced by `𝔞'_T`; `cosupp_geoTransformAlong_eq`: hence
  `cosupp 𝔪_T = N_T ∩ Z(𝔞'_T)`;
* one blowup along a thin centre `C` inside a closed connected submanifold `N` of dimension `k`:
  `lt_of_regularAtDim_of_frequently` (`dim C < k`), `mem_exceptionalLocus_of_regularAtDim` (codimension `≥ 2`: every point
  over `C` is exceptional), `isPreconnected_preimage_of_disjoint`, `mem_geoStrictTransform_iff_of_notMem`,
  **`geoStrictTransform_data`** (`N' = closure (π⁻¹(N \ C))` is the strict transform `closure (π⁻¹N \ Exc π)` and a closed
  connected submanifold of dimension `k`), `pullback_vanishingIdeal_eq_of_disjoint` (`π^*𝓘_A = 𝓘_{π⁻¹A}` for `A ∩ C = ∅`);
* along a multiple test blow-up `T` of `𝔪` in the domain, with mark one and `N` a closed connected submanifold of
  dimension `k < n`: `support_add_subset`, `frequently_mem_N_notMem_of_isInvDomain`, **`tower_data`** -- `N_T` is a closed
  connected submanifold of dimension `k` and the strict transform of `N`; `T` is adapted to `N`;
  `T^*𝓘_N = 𝒪(-E_T)·𝓘_{N_T}` (Copy-4's first identity); the support of `E_T` lies in `Exc T`;
* the second stage, for `(X, X, E, 𝔟, 1)` with `𝔟` coherent and a closed connected submanifold `A` of dimension `k` missing
  `Z(𝔟)`: `disjoint_preimage_of_isAdmissibleCentre` (admissible centres along a test tower `S` miss `S⁻¹A`), **`second_data`**
  (`S⁻¹A` is a closed connected submanifold of dimension `k` and the strict transform of `A`, `E_S` misses it,
  `S^*𝓘_A = 𝓘_{S⁻¹A}`);
* the assembly: `pullDivisor` (`S^*D`, with `pullDivisor_ideal`, `support_pullDivisor`), `idealPow_one_of_isCoherent`,
  `isAdaptedBlowupSequence_comp`, `lt_of_ne_univ`, **`factorizationData_of_isGeoResolution`** (from a resolution `T₁` of
  `(Y, W, ∅, 𝔞, 1)` and a resolution `T₂` of `(Y_t, Y_t, ∅, 𝔞_t, 1)`, `𝔞_t` the ambient controlled transform along `T₁`: the body of
  `RelativePrincipalization.FactorizationData W k 𝔞`, written out, with `f = T₁ ∘ T₂`, `H = T₂^*E_{T₁}`, `H' = E_{T₂}`) and
  **`factorizationData_of_exists_resolution`** (the same from the existence of resolutions of every marked ideal of the domain
  in dimension `≤ j`, `n ≤ j`, on compact manifolds -- the output of a resolution invariant's driver).

`RelativePrincipalization` is not imported: its `FactorizationData` is written out in the conclusions above (checked
definitionally equal by a throwaway probe outside the repository).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.FactorizationFromResolution

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.GermIdealOrder
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.BlowupControlledTransform Hironaka.BlowupExceptionalDivisor
open Hironaka.ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {n : ℕ}

/-! ### The transform along `N` and the ambient transform -/

section Ambient

variable {X : CMfd.{u} n}

/-- The marked ideal `(X, X, E, 𝔞, d)` with the data of `𝔪 = (X, N, E, 𝔞, d)` and `N` replaced by the whole manifold. -/
def ambient (𝔪 : MarkedIdeal n X) : MarkedIdeal n X := { 𝔪 with N := univ }

@[simp] theorem ambient_N (𝔪 : MarkedIdeal n X) : (ambient 𝔪).N = univ := rfl
@[simp] theorem ambient_E (𝔪 : MarkedIdeal n X) : (ambient 𝔪).E = 𝔪.E := rfl
@[simp] theorem ambient_ideal (𝔪 : MarkedIdeal n X) : (ambient 𝔪).ideal = 𝔪.ideal := rfl
@[simp] theorem ambient_d (𝔪 : MarkedIdeal n X) : (ambient 𝔪).d = 𝔪.d := rfl

/-- The cosupport of a marked ideal with mark one and coherent ideal is `N ∩ Z(𝔞)`. -/
theorem cosupp_eq_inter_zeroLocus {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {𝔫 : MarkedIdeal n M} (hd : 𝔫.d = 1) (h : 𝔫.ideal.IsCoherent) :
    𝔫.cosupp = 𝔫.N ∩ 𝔫.ideal.zeroLocus := by
  rw [MarkedIdeal.cosupp, hd]
  exact cosupport_one fun _ _ hg => SubmanifoldRestrictLe.holomorphicAt_of_mem_of_isCoherent h hg

/-- **The transform along `N` agrees with the ambient transform along `N`** (Copy-4, `eq:rp-induction`, third identity):
along every multiple test blow-up `T` of `𝔪 = (X, N, E, 𝔞, 1)` (`N` a closed submanifold, `𝔞` coherent), `T` is a multiple
test blow-up of `(X, X, E, 𝔞, 1)`, and `𝔪_T` is restricted-equivalent to `𝔪_T` with its ideal replaced by the ambient
controlled transform `𝔞'_T`. -/
theorem isGeoTestTower_and_restrictEquiv {𝔪 : MarkedIdeal n X} (hd : 𝔪.d = 1) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      IsGeoTestTower (ambient 𝔪) T ∧
        RestrictEquiv (geoTransformAlong 𝔪 T)
          { geoTransformAlong 𝔪 T with ideal := (geoTransformAlong (ambient 𝔪) T).ideal }
  | _, .refl, _ => ⟨trivial, RestrictEquiv.refl h𝔞⟩
  | _, .step T C π hπ, hT => by
      obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hT', hEq⟩ := isGeoTestTower_and_restrictEquiv hd hN h𝔞 T hTT
      obtain ⟨hNT, hcohT⟩ := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hTT
      obtain ⟨hN'T, hcoh'T, -⟩ :=
        pullback_eq_mul_geoTransformAlong (ambient 𝔪) rfl h𝔞 T hT'
      set 𝔫 := geoTransformAlong 𝔪 T with h𝔫
      set A := (geoTransformAlong (ambient 𝔪) T).ideal with hA
      set 𝔫' : MarkedIdeal n _ := { 𝔫 with ideal := A } with h𝔫'
      have hd𝔫 : 𝔫.d = 1 := by rw [h𝔫, d_geoTransformAlong, hd]
      have hd'T : (geoTransformAlong (ambient 𝔪) T).d = 1 := by rw [d_geoTransformAlong, ambient_d, hd]
      have hE'T : (geoTransformAlong (ambient 𝔪) T).E = 𝔫.E :=
        (MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := ambient 𝔪) (𝔫 := 𝔪) rfl T)
      -- `C` is admissible for `𝔫'` and lies in the zero locus of `A`
      have hC' : 𝔫'.IsAdmissibleCentre C := hEq.isAdmissibleCentre_iff.mp hC
      have hCZ : C ⊆ A.zeroLocus := by
        intro c hc
        have hc' := hC'.2.1 hc
        rw [cosupp_eq_inter_zeroLocus (𝔫 := 𝔫') hd𝔫 hcoh'T] at hc'
        exact hc'.2
      have hCamb : (geoTransformAlong (ambient 𝔪) T).IsAdmissibleCentre C := by
        refine ⟨hC.1, ?_, ?_⟩
        · rw [cosupp_eq_inter_zeroLocus hd'T hcoh'T, hN'T, univ_inter]
          exact hCZ
        · rw [hE'T]
          exact hC.2.2
      have hsub : C ⊆ cosupport n univ A 1 := by
        rw [cosupport_one fun _ _ hg => SubmanifoldRestrictLe.holomorphicAt_of_mem_of_isCoherent hcoh'T hg,
          univ_inter]
        exact hCZ
      have hpb := HadamardBridge.pullback_eq_mul_controlledTransform_of_subset_cosupport hπ hcoh'T hsub
      rw [exceptionalDivisor_ideal] at hpb
      have htr : (geoTransformAlong (ambient 𝔪) (.step T C π hπ)).ideal = controlledTransform hπ A 1 := by
        rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hN'T hcoh'T hπ, hd'T]
      have hpbcoh : (GermIdeal.pullback (m := n) π A).IsCoherent :=
        GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hcoh'T
      refine ⟨(isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hT', hCamb⟩, ?_⟩
      have hstep : geoTransformAlong 𝔪 (.step T C π hπ) = 𝔫'.geoTransform C π := by
        rw [geoTransformAlong_step]
        exact hEq.geoTransform_eq hNT.1 hcohT hcoh'T hπ.contMDiff
      have key := HomogenizedIdealAlongTower.restrictEquiv_geoTransform_of_pullback (𝔫 := 𝔫') hNT hcoh'T hC' hπ
        (Q := controlledTransform hπ A 1) (isCoherent_controlledTransform hπ hcoh'T
          (HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hcoh'T hπ.1 hsub))
        (by rw [show 𝔫'.d = 1 from hd𝔫, ← hpb]; exact RestrictLeCalculus.restrictLe_refl hpbcoh)
        (by rw [show 𝔫'.d = 1 from hd𝔫, ← hpb]; exact RestrictLeCalculus.restrictLe_refl hpbcoh)
      rw [hstep, htr]
      exact key

/-- **The cosupport along `N` is the trace of the zero locus of the ambient transform**: `cosupp 𝔪_T = N_T ∩ Z(𝔞'_T)`
along every multiple test blow-up of `𝔪 = (X, N, E, 𝔞, 1)`. -/
theorem cosupp_geoTransformAlong_eq {𝔪 : MarkedIdeal n X} (hd : 𝔪.d = 1) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    (geoTransformAlong 𝔪 T).cosupp =
      (geoTransformAlong 𝔪 T).N ∩ (geoTransformAlong (ambient 𝔪) T).ideal.zeroLocus := by
  obtain ⟨hT', hEq⟩ := isGeoTestTower_and_restrictEquiv hd hN h𝔞 T hT
  obtain ⟨-, hcoh'T, -⟩ := pullback_eq_mul_geoTransformAlong (ambient 𝔪) rfl h𝔞 T hT'
  rw [hEq.cosupp_eq]
  exact cosupp_eq_inter_zeroLocus (𝔫 := { geoTransformAlong 𝔪 T with ideal := (geoTransformAlong (ambient 𝔪) T).ideal })
    (by show (geoTransformAlong 𝔪 T).d = 1; rw [d_geoTransformAlong, hd]) hcoh'T

end Ambient

/-! ### One blowup along a thin centre inside a connected submanifold -/

section OneStep

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  {C : Set M} {π : M' → M}

/-- **A thin submanifold has smaller dimension**: if `C ⊆ N` are regular at `c` of dimensions `j` and `k` and points of
`N \ C` accumulate at `c`, then `j < k`. -/
theorem lt_of_regularAtDim_of_frequently {N : Set M} (hC : IsComplexAnalyticSubset (n := n) C) (hCN : C ⊆ N)
    {c : M} {j k : ℕ} (hCc : RegularAtDim (n := n) C c j) (hNc : RegularAtDim (n := n) N c k)
    (hfreq : ∃ᶠ y in 𝓝 c, y ∈ N ∧ y ∉ C) : j < k := by
  by_contra hjk
  push Not at hjk
  have hdim : AnalyticDimensionBasics.LocDimGE (n := n) C c k := fun U hU =>
    ⟨c, mem_of_mem_nhds hU, j, hjk, hCc⟩
  have hev := CodimOneSupport.eventually_mem_of_locDimGE hC hNc (Eventually.of_forall fun y hy => hCN hy) hdim
  obtain ⟨y, ⟨hyN, hyC⟩, hy⟩ := (hfreq.and_eventually hev).exists
  exact hyC (hy hyN)

/-- **Over a centre of codimension at least two every point is exceptional.** -/
theorem mem_exceptionalLocus_of_regularAtDim (hπ : IsBlowupAlong n C π) {z : M'} (hz : π z ∈ C) {j : ℕ}
    (hreg : RegularAtDim (n := n) C (π z) j) (hj : j + 2 ≤ n) : z ∈ exceptionalLocus n π := by
  obtain ⟨-, -, Φ, hsrc, -, hflat⟩ := hreg
  exact BlowupCodimOne.mem_exceptionalLocus_of_codim_ge_two hπ hsrc hflat hj
    (BlowupFlatCoordinates.mem_flatDomain_self Φ) hz

/-- **The preimage of the complement of the centre is the image of the section**: for `A` off the centre, `π⁻¹ A` is
the image of `A` under the holomorphic section of `π` over `M \ C`, so it is preconnected when `A` is. -/
theorem isPreconnected_preimage_of_disjoint (hπ : IsBlowupAlong n C π) {A : Set M} (hA : IsPreconnected A)
    (hAC : Disjoint A C) : IsPreconnected (π ⁻¹' A) := by
  obtain ⟨σ, hσ, hσπ, hσsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hAO : A ⊆ range (Subtype.val : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens M) → M) :=
    fun x hx => ⟨⟨x, Set.disjoint_left.mp hAC hx⟩, rfl⟩
  have hpre : IsPreconnected
      ((Subtype.val : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens M) → M) ⁻¹' A) := by
    have h := (Topology.IsInducing.subtypeVal (t := ((⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens M) : Set M))).isPreconnected_image
      (s := (Subtype.val : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens M) → M) ⁻¹' A)
    refine h.mp ?_
    convert hA using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := hAO hx
      exact ⟨y, hx, rfl⟩
  have himg : π ⁻¹' A = σ '' ((Subtype.val : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens M) → M) ⁻¹' A) := by
    ext z
    constructor
    · intro hz
      have hzC : π z ∈ Cᶜ := Set.disjoint_left.mp hAC hz
      exact ⟨⟨π z, hzC⟩, hz, hσsec z hzC⟩
    · rintro ⟨x, hx, rfl⟩
      show π (σ x) ∈ A
      rw [show π (σ x) = x.1 from congrFun hσπ x]
      exact hx
  rw [himg]
  exact hpre.image σ hσ.continuous.continuousOn

/-- Off the centre, the strict transform `N' = closure (π⁻¹ (N \ C))` of a closed `N` is the preimage of `N`. -/
theorem mem_geoStrictTransform_iff_of_notMem (hπ : IsBlowupAlong n C π) {N : Set M} (hN : IsClosed N) {u : M'}
    (hu : π u ∉ C) : u ∈ BlowupStrictSubmanifold.geoStrictTransform π C N ↔ π u ∈ N :=
  ⟨fun h => BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN h,
    fun h => subset_closure ⟨h, hu⟩⟩

/-- **The strict transform of a closed connected submanifold along a thin centre** (Copy-4, the paragraph before
`lem:relative-principalization`: "the strict transform `W'` of `W` is a connected submanifold"): let `N` be a closed
connected submanifold of dimension `k`, and `C ⊆ N` the centre of the blowup `π`, with points of `N \ C` accumulating at
every point of `C`.  Then `N' = closure (π⁻¹ (N \ C))` is the library's strict transform `closure (π⁻¹ N \ Exc π)`, and
it is a closed connected submanifold of dimension `k`. -/
theorem geoStrictTransform_data (hπ : IsBlowupAlong n C π) {N : Set M} {k : ℕ}
    (hN : IsClosedConnectedSubmanifold n N k) (hCN : C ⊆ N) (hfreq : ∀ c ∈ C, ∃ᶠ y in 𝓝 c, y ∈ N ∧ y ∉ C) :
    BlowupStrictSubmanifold.geoStrictTransform π C N = strictTransform n π N ∧
      IsClosedConnectedSubmanifold n (BlowupStrictSubmanifold.geoStrictTransform π C N) k := by
  have hNs := FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hN
  have hNan := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hNs
  have hCan := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
  obtain ⟨c, hcN⟩ := hN.2.1.nonempty
  have hcomp : RegularLocusComponent.component (n := n) N c = N := by
    rw [FactorizationDomain.component_eq_connectedComponentIn hN.2.2 c]
    exact hN.2.1.isPreconnected.connectedComponentIn hcN
  have hK : ¬ RegularLocusComponent.component (n := n) N c ⊆ C := by
    rw [hcomp]
    intro hNC
    obtain ⟨y, hyN, hyC⟩ := (hfreq c (hNC hcN)).exists
    exact hyC (hNC hyN)
  obtain ⟨hpre, hclos⟩ := ComponentComplementConnected.isPreconnected_component_diff_and_subset_closure hNan hCan
    (hN.2.2 c hcN) hK
  rw [hcomp] at hpre hclos
  have hst := BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hclos
  refine ⟨hst, ?_⟩
  set N' := BlowupStrictSubmanifold.geoStrictTransform π C N with hN'
  have hNs' : IsClosedSubmanifold n N' :=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hNs hCN
  -- a point of `N'` off the exceptional divisor, regular of dimension `k`
  obtain ⟨x, hxN, hxC⟩ : (N \ C).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
    exact hK (by rw [hcomp]; exact h)
  obtain ⟨σ, hσ, hσπ, hσsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  set y₀ := σ ⟨x, hxC⟩ with hy₀
  have hπy₀ : π y₀ = x := congrFun hσπ ⟨x, hxC⟩
  have hy₀N' : y₀ ∈ N' := subset_closure (show π y₀ ∈ N \ C by rw [hπy₀]; exact ⟨hxN, hxC⟩)
  have hy₀exc : y₀ ∉ exceptionalLocus n π := fun h =>
    hxC (hπy₀ ▸ BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
  have hOopen : IsOpen (π ⁻¹' Cᶜ) := hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous
  have hreg₀ : RegularAtDim (n := n) N' y₀ k :=
    RegularAtDimTransport.regularAtDim_of_preimage hπ.contMDiff hy₀exc hOopen
      (by show π y₀ ∈ Cᶜ; rw [hπy₀]; exact hxC)
      (fun u hu => mem_geoStrictTransform_iff_of_notMem hπ hN.1 hu)
      (by rw [hπy₀]; exact hN.2.2 x hxN)
  -- connectedness
  have hpreN : IsPreconnected (π ⁻¹' (N \ C)) :=
    isPreconnected_preimage_of_disjoint hπ hpre disjoint_sdiff_left
  have hconn : IsConnected N' :=
    ⟨⟨y₀, hy₀N'⟩, hpreN.closure⟩
  refine ⟨isClosed_closure, hconn, fun z hz => ?_⟩
  have hRP : RegularLocusComponent.regularPoints (n := n) N' = N' :=
    Subset.antisymm (RegularLocusComponent.regularPoints_subset (n := n) N') fun x hx => hNs'.2 x hx
  have hcomp' : RegularLocusComponent.component (n := n) N' y₀ = N' := by
    rw [RegularLocusComponent.component, hRP]
    exact hconn.isPreconnected.connectedComponentIn hy₀N'
  exact RegularLocusComponent.regularAtDim_of_mem_component hreg₀ (hcomp'.symm ▸ hz)

/-- **Pulling back the ideal of a closed set the centre misses**: `π^*𝓘_A = 𝓘_{π⁻¹A}`. -/
theorem pullback_vanishingIdeal_eq_of_disjoint (hπ : IsBlowupAlong n C π) {A : Set M} (hA : IsClosed A)
    (hCA : Disjoint C A) :
    GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) A) = vanishingIdeal (n := n) (π ⁻¹' A) := by
  refine GermIdeal.ext (funext fun z => funext fun g => propext ?_)
  by_cases hz : π z ∈ C
  · have hzA : π z ∉ A := Set.disjoint_left.mp hCA hz
    have h1 : (vanishingIdeal (n := n) A).mem (π z) (fun _ => (1 : ℂ)) :=
      ⟨holomorphicAt_const 1, by
        filter_upwards [hA.isOpen_compl.mem_nhds hzA] with w hw hwA
        exact absurd hwA hw⟩
    constructor
    · intro hg
      exact BlowupStrictIdeal.pullback_vanishingIdeal_le hπ.contMDiff.continuous A z g hg
    · intro hg
      exact isInSpanAt_of_eq_mul (S := fun s => ∃ a, (vanishingIdeal (n := n) A).mem (π z) a ∧ s = a ∘ π)
        (s := (fun _ => (1 : ℂ)) ∘ π) ⟨_, h1, rfl⟩ hg.1 hg.1 (Eventually.of_forall fun w => by simp)
  · exact BlowupStrictIdeal.mem_pullback_vanishingIdeal_iff_of_notMem hπ A hz g

end OneStep

/-! ### Along a multiple test blow-up of `(X, W, E, 𝔞, 1)` -/

section Tower

variable {X : CMfd.{u} n}

/-- The support of the sum of two effective divisors lies in the union of the supports. -/
theorem support_add_subset {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D D' : EffectiveDivisor n M) :
    (GermIdealTotalTransform.EffectiveDivisor.add D D').support ⊆ D.support ∪ D'.support := by
  intro x hx
  by_contra h
  rw [mem_union, not_or] at h
  exact RestrictLeCalculus.notMem_zeroLocus_mul (isCoherent_ideal D) (isCoherent_ideal D') h.1 h.2 hx

/-- **Points of the submanifold off a centre accumulate at the centre**: for `𝔫` in the domain with mark one and an
admissible centre `C`, every point of `C` is a limit of points of `N \ C` (a germ of `𝔞` nonzero along `N` does not vanish
at nearby points of `N`, which therefore lie off the cosupport). -/
theorem frequently_mem_N_notMem_of_isInvDomain {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {𝔫 : MarkedIdeal n M} {k : ℕ} (h : IsInvDomain k 𝔫) (hd : 𝔫.d = 1) {C : Set M}
    (hC : C ⊆ 𝔫.cosupp) : ∀ c ∈ C, ∃ᶠ y in 𝓝 c, y ∈ 𝔫.N ∧ y ∉ C := by
  intro c hc
  have hcoh := h.isWellFormed.isCoherent
  obtain ⟨g, hg, hfr⟩ := h.isNonzeroAlongAt c (𝔫.cosupp_subset_N (hC hc))
  refine (hfr.and_eventually (HadamardBridge.eventually_mem_of_isCoherent hcoh hg)).mono ?_
  rintro y ⟨⟨hyN, hgy⟩, hmem⟩
  refine ⟨hyN, fun hyC => hgy ?_⟩
  have hy := hC hyC
  rw [cosupp_eq_inter_zeroLocus hd hcoh] at hy
  exact hy.2 g hmem

/-- **The strict transform, adaptedness and the first identity along a multiple test blow-up** (Copy-4, the paragraph
before `lem:relative-principalization` and the first identity of `eq:rp-induction`): let `𝔪` be in the domain in dimension
`≤ k`, with mark one and `N = 𝔪.N` a closed connected submanifold of dimension `k < n`.  Along every multiple test blow-up
`T` of `𝔪`:
* `N_T` is a closed connected submanifold of dimension `k`, and it is the strict transform `closure (T⁻¹N \ Exc T)`;
* `T` is a sequence of blowups adapted to `N` (each centre is a proper analytic subset of the current strict transform);
* `T^*𝓘_N = 𝒪(-E_T) · 𝓘_{N_T}`, and the support of `E_T` lies in the exceptional locus of `T` (the centres have
  codimension at least two). -/
theorem tower_data {𝔪 : MarkedIdeal n X} {k : ℕ} (h : IsInvDomain k 𝔪) (hd : 𝔪.d = 1)
    (hN : IsClosedConnectedSubmanifold n 𝔪.N k) (hkn : k < n) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      IsClosedConnectedSubmanifold n (geoTransformAlong 𝔪 T).N k ∧
      (geoTransformAlong 𝔪 T).N = strictTransform n T.proj 𝔪.N ∧
      IsAdaptedBlowupSequence n X 𝔪.N Y T.proj ∧
      GermIdeal.pullback (m := n) T.proj (vanishingIdeal (n := n) 𝔪.N) =
        (BlowupTowerTransforms.exceptionalDivisor T).ideal.mul
          (vanishingIdeal (n := n) (geoTransformAlong 𝔪 T).N) ∧
      (BlowupTowerTransforms.exceptionalDivisor T).support ⊆ exceptionalLocus n T.proj
  | _, .refl, _ => by
      have hNs := FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hN
      refine ⟨hN, ?_, IsAdaptedBlowupSequence.refl, ?_, ?_⟩
      · show 𝔪.N = strictTransform n (id : X → X) 𝔪.N
        simp [strictTransform, exceptionalLocus_id, hN.1.closure_eq]
      · rw [BlowupTowerTransforms.exceptionalDivisor_refl_ideal, BlowupTower.proj_refl, geoTransformAlong_refl,
          unitIdeal_mul (VanishingIdealCoherent.isCoherent_vanishingIdeal hNs)]
        exact pullback_id (VanishingIdealCoherent.isCoherent_vanishingIdeal hNs)
      · intro x hx
        exact absurd (hx (fun _ => (1 : ℂ)) (holomorphicAt_const 1)) one_ne_zero
  | _, .step T C π hπ, hT => by
      obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hconn, hst, hadapt, hpb, hsupp⟩ := tower_data h hd hN hkn T hTT
      have hdom := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hTT
      set 𝔫 := geoTransformAlong 𝔪 T with h𝔫
      have hd𝔫 : 𝔫.d = 1 := by rw [h𝔫, d_geoTransformAlong, hd]
      have hCN : C ⊆ 𝔫.N := hC.subset_N
      have hfreq := frequently_mem_N_notMem_of_isInvDomain hdom hd𝔫 hC.2.1
      obtain ⟨hgs, hconn'⟩ := geoStrictTransform_data hπ hconn hCN hfreq
      have hNs := FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hconn
      have hNs₀ := FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hN
      have hNs' := FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hconn'
      have hN'eq : (geoTransformAlong 𝔪 (.step T C π hπ)).N = BlowupStrictSubmanifold.geoStrictTransform π C 𝔫.N := rfl
      have hCan := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
      have hCne : C ≠ 𝔫.N := by
        intro hCeq
        obtain ⟨c, hc⟩ := hconn.2.1.nonempty
        obtain ⟨y, hyN, hyC⟩ := (hfreq c (hCeq ▸ hc)).exists
        exact hyC (hCeq ▸ hyN)
      -- the centre has codimension at least two
      have hexc : π ⁻¹' C ⊆ exceptionalLocus n π := by
        intro z hz
        obtain ⟨j, hj⟩ := hπ.1.2 (π z) hz
        have hlt := lt_of_regularAtDim_of_frequently hCan hCN hj (hconn.2.2 (π z) (hCN hz)) (hfreq (π z) hz)
        exact mem_exceptionalLocus_of_regularAtDim hπ hz hj (by omega)
      refine ⟨hN'eq ▸ hconn', ?_, ?_, ?_, ?_⟩
      · rw [hN'eq, hgs, hst, BlowupTower.proj_step,
          StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff]
      · exact IsAdaptedBlowupSequence.step T.proj C π hadapt hπ
          (Or.inl ⟨C, hCan, hst ▸ hCN, hst ▸ hCne, subset_rfl⟩)
      · rw [hN'eq]
        exact GermIdealTotalTransform.pullback_comp_eq_mul T.contMDiff_proj hπ.contMDiff
          (interior_exceptionalLocus_eq_empty hπ) (VanishingIdealCoherent.isCoherent_vanishingIdeal hNs₀)
          (VanishingIdealCoherent.isCoherent_vanishingIdeal hNs)
          (VanishingIdealCoherent.isCoherent_vanishingIdeal hNs') (BlowupTowerTransforms.exceptionalDivisor T)
          (BlowupExceptionalDivisor.exceptionalDivisor hπ) hpb
          (BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul hπ hNs hCN)
      · intro z hz
        rw [BlowupTower.proj_step, exceptionalLocus_comp (T.contMDiff_proj.mdifferentiable (by simp))
          (hπ.contMDiff.mdifferentiable (by simp))]
        rcases support_add_subset _ _ hz with h1 | h2
        · rw [support_totalTransform hπ] at h1
          exact Or.inr (hsupp h1)
        · rw [support_exceptionalDivisor hπ] at h2
          exact Or.inl (hexc h2)

end Tower

/-! ### The second stage: a marked ideal on the whole manifold, nonvanishing near a submanifold -/

section Second

variable {X : CMfd.{u} n}

/-- **The centres of the second stage miss the submanifold**: for `𝔪 = (X, X, E, 𝔟, 1)` with `𝔟` coherent and a set `A`
disjoint from `Z(𝔟)`, every admissible centre along a multiple test blow-up `S` of `𝔪` misses `S⁻¹A` (the cosupport is the
zero locus of the controlled transform, which lies in `S⁻¹ Z(𝔟)` since `S^*𝔟 = 𝒪(-E_S)·𝔟_S`). -/
theorem disjoint_preimage_of_isAdmissibleCentre {𝔪 : MarkedIdeal n X} (hN : 𝔪.N = univ) (hd : 𝔪.d = 1)
    (hB : 𝔪.ideal.IsCoherent) {A : Set X} (hAB : Disjoint A 𝔪.ideal.zeroLocus) {Y : CMfd.{u} n}
    (S : BlowupTower X Y) (hS : IsGeoTestTower 𝔪 S) {C : Set Y} (hC : (geoTransformAlong 𝔪 S).IsAdmissibleCentre C) :
    Disjoint C (S.proj ⁻¹' A) := by
  obtain ⟨-, hcohS, hpb⟩ := pullback_eq_mul_geoTransformAlong 𝔪 hN hB S hS
  rw [Set.disjoint_left]
  intro c hcC hcA
  have hc := hC.2.1 hcC
  rw [cosupp_eq_inter_zeroLocus (by rw [d_geoTransformAlong, hd]) hcohS] at hc
  have hz : c ∈ (GermIdeal.pullback (m := n) S.proj 𝔪.ideal).zeroLocus := by
    rw [hpb]
    exact RestrictLeCalculus.zeroLocus_right_subset_mul _ _ hc.2
  rw [zeroLocus_pullback S.contMDiff_proj hB] at hz
  exact Set.disjoint_left.mp hAB hcA hz

/-- **Along the second stage the submanifold is carried isomorphically** (Copy-4: "all its centres lie in the cosupport of
`𝔞_t`, hence are disjoint from the strict transforms of `W_t`"): for `𝔪 = (X, X, E, 𝔟, 1)`, `𝔟` coherent, and a closed connected
submanifold `A` of dimension `k` disjoint from `Z(𝔟)`, along every multiple test blow-up `S` of `𝔪`: `S⁻¹A` is a closed connected
submanifold of dimension `k` and the strict transform of `A`, the exceptional divisor `E_S` misses it, and `S^*𝓘_A = 𝓘_{S⁻¹A}`. -/
theorem second_data {𝔪 : MarkedIdeal n X} (hN : 𝔪.N = univ) (hd : 𝔪.d = 1) (hB : 𝔪.ideal.IsCoherent) {A : Set X}
    {k : ℕ} (hA : IsClosedConnectedSubmanifold n A k) (hAB : Disjoint A 𝔪.ideal.zeroLocus) :
    {Y : CMfd.{u} n} → (S : BlowupTower X Y) → IsGeoTestTower 𝔪 S →
      IsClosedConnectedSubmanifold n (S.proj ⁻¹' A) k ∧
      strictTransform n S.proj A = S.proj ⁻¹' A ∧
      Disjoint (BlowupTowerTransforms.exceptionalDivisor S).support (S.proj ⁻¹' A) ∧
      GermIdeal.pullback (m := n) S.proj (vanishingIdeal (n := n) A) = vanishingIdeal (n := n) (S.proj ⁻¹' A)
  | _, .refl, _ => by
      have hAs := FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hA
      refine ⟨hA, ?_, ?_, ?_⟩
      · show strictTransform n (id : X → X) A = A
        simp [strictTransform, exceptionalLocus_id, hA.1.closure_eq]
      · rw [Set.disjoint_left]
        intro x hx
        exact absurd (hx (fun _ => (1 : ℂ)) (holomorphicAt_const 1)) one_ne_zero
      · exact pullback_id (VanishingIdealCoherent.isCoherent_vanishingIdeal hAs)
  | _, .step S C π hπ, hS => by
      obtain ⟨hSS, hC⟩ := (isGeoTestTower_step_iff 𝔪 S C π hπ).mp hS
      obtain ⟨hconn, hst, hdisj, hpb⟩ := second_data hN hd hB hA hAB S hSS
      have hCA : Disjoint C (S.proj ⁻¹' A) := disjoint_preimage_of_isAdmissibleCentre hN hd hB hAB S hSS hC
      set A' := S.proj ⁻¹' A with hA'
      have hAs' := FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hconn
      have hpre : (BlowupTower.step S C π hπ).proj ⁻¹' A = π ⁻¹' A' := rfl
      have hexc : ∀ z, π z ∈ A' → z ∉ exceptionalLocus n π := fun z hz hzE =>
        Set.disjoint_left.mp hCA (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ hzE) hz
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hpre]
        obtain ⟨σ, -, hσπ, -⟩ := BlowupIsomorphismOff.exists_section_compl hπ
        obtain ⟨x, hx⟩ := hconn.2.1.nonempty
        have hxC : x ∈ Cᶜ := fun h => Set.disjoint_left.mp hCA h hx
        refine ⟨hconn.1.preimage hπ.contMDiff.continuous,
          ⟨⟨σ ⟨x, hxC⟩, show π (σ ⟨x, hxC⟩) ∈ A' by rw [show π (σ ⟨x, hxC⟩) = x from congrFun hσπ _]; exact hx⟩,
            isPreconnected_preimage_of_disjoint hπ hconn.2.1.isPreconnected hCA.symm⟩, fun z hz => ?_⟩
        exact RegularAtDimTransport.regularAtDim_of_preimage hπ.contMDiff (hexc z hz) isOpen_univ (mem_univ z)
          (fun u _ => Iff.rfl) (hconn.2.2 (π z) hz)
      · rw [hpre, BlowupTower.proj_step,
          StrictTransformComposition.strictTransform_comp S.contMDiff_proj hπ.contMDiff, hst]
        show closure (π ⁻¹' A' \ exceptionalLocus n π) = π ⁻¹' A'
        have hsd : π ⁻¹' A' \ exceptionalLocus n π = π ⁻¹' A' :=
          sdiff_eq_left.mpr (Set.disjoint_left.mpr fun z hz hzE => hexc z hz hzE)
        rw [hsd, (hconn.1.preimage hπ.contMDiff.continuous).closure_eq]
      · rw [hpre, Set.disjoint_left]
        intro z hz hzA
        rcases support_add_subset _ _ hz with h1 | h2
        · rw [support_totalTransform hπ] at h1
          exact Set.disjoint_left.mp hdisj h1 hzA
        · rw [support_exceptionalDivisor hπ] at h2
          exact Set.disjoint_left.mp hCA h2 hzA
      · rw [hpre, BlowupTower.proj_step,
          GermIdealTotalTransform.pullback_comp S.contMDiff_proj hπ.contMDiff
            (VanishingIdealCoherent.isCoherent_vanishingIdeal
              (FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hA)), hpb]
        exact pullback_vanishingIdeal_eq_of_disjoint hπ hconn.1 hCA

end Second

/-! ### Pulled-back divisors and the composite sequence -/

section Assembly

/-- **The total transform of a divisor along a tower** (`g^*D`, one blowup at a time). -/
def pullDivisor {X : CMfd.{u} n} : {Y : CMfd.{u} n} → BlowupTower X Y → EffectiveDivisor n X → EffectiveDivisor n Y
  | _, .refl, D => D
  | _, .step S _ _ hπ, D => totalTransform hπ (pullDivisor S D)

/-- The ideal of `S^*D` is the pullback of the ideal of `D`. -/
theorem pullDivisor_ideal {X : CMfd.{u} n} (D : EffectiveDivisor n X) :
    {Y : CMfd.{u} n} → (S : BlowupTower X Y) → (pullDivisor S D).ideal = GermIdeal.pullback (m := n) S.proj D.ideal
  | _, .refl => (pullback_id (isCoherent_ideal D)).symm
  | _, .step S _ π hπ => by
      show GermIdeal.pullback (m := n) π (pullDivisor S D).ideal = _
      rw [pullDivisor_ideal D S, BlowupTower.proj_step,
        GermIdealTotalTransform.pullback_comp S.contMDiff_proj hπ.contMDiff (isCoherent_ideal D)]

/-- The support of `S^*D` is the preimage of the support of `D`. -/
theorem support_pullDivisor {X : CMfd.{u} n} (D : EffectiveDivisor n X) {Y : CMfd.{u} n} (S : BlowupTower X Y) :
    (pullDivisor S D).support = S.proj ⁻¹' D.support := by
  rw [EffectiveDivisor.support, pullDivisor_ideal, zeroLocus_pullback S.contMDiff_proj (isCoherent_ideal D)]
  rfl

/-- `𝔞^1 = 𝔞` for a coherent ideal. -/
theorem idealPow_one_of_isCoherent {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) : IdealWeightPowers.idealPow 𝔞 1 = 𝔞 := by
  rw [IdealWeightPowers.idealPow_succ, IdealWeightPowers.idealPow_zero, unitIdeal_mul h𝔞]

/-- **The second stage keeps the sequence adapted**: if `f₁` is adapted to `W` with strict transform `A`, and `S` is a multiple
test blow-up of `(X, X, E, 𝔟, 1)` with `A ∩ Z(𝔟) = ∅` (`A` a closed connected submanifold), then `f₁ ∘ S` is adapted to `W`: every
centre of `S` misses the current strict transform `S⁻¹A`. -/
theorem isAdaptedBlowupSequence_comp {Y₀ : Type u} [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀]
    [IsComplexManifold n Y₀] {W : Set Y₀} {X : CMfd.{u} n} {f₁ : X → Y₀}
    (hadapt : IsAdaptedBlowupSequence n Y₀ W X f₁) {A : Set X} {k : ℕ} (hA : IsClosedConnectedSubmanifold n A k)
    (hst : strictTransform n f₁ W = A) {𝔪 : MarkedIdeal n X} (hN : 𝔪.N = univ) (hd : 𝔪.d = 1)
    (hB : 𝔪.ideal.IsCoherent) (hAB : Disjoint A 𝔪.ideal.zeroLocus) :
    {Y : CMfd.{u} n} → (S : BlowupTower X Y) → IsGeoTestTower 𝔪 S →
      IsAdaptedBlowupSequence n Y₀ W Y (f₁ ∘ S.proj)
  | _, .refl, _ => hadapt
  | _, .step S C π hπ, hS => by
      obtain ⟨hSS, hC⟩ := (isGeoTestTower_step_iff 𝔪 S C π hπ).mp hS
      have ih := isAdaptedBlowupSequence_comp hadapt hA hst hN hd hB hAB S hSS
      have hst' : strictTransform n (f₁ ∘ S.proj) W = S.proj ⁻¹' A := by
        rw [StrictTransformComposition.strictTransform_comp hadapt.contMDiff S.contMDiff_proj, hst]
        exact (second_data hN hd hB hA hAB S hSS).2.1
      exact IsAdaptedBlowupSequence.step (f₁ ∘ S.proj) C π ih hπ
        (Or.inr (hst' ▸ disjoint_preimage_of_isAdmissibleCentre hN hd hB hAB S hSS hC))

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- A closed connected submanifold different from a connected manifold has smaller dimension. -/
theorem lt_of_ne_univ [ConnectedSpace Y] {W : Set Y} {k : ℕ} (hW : IsClosedConnectedSubmanifold n W k)
    (hWY : W ≠ univ) : k < n := by
  obtain ⟨x, hx⟩ := hW.2.1.nonempty
  have hkn : k ≤ n := (hW.2.2 x hx).1
  by_contra hlt
  have hk : k = n := le_antisymm hkn (not_lt.mp hlt)
  subst hk
  have hopen : IsOpen W := isOpen_iff_mem_nhds.mpr fun y hy =>
    EmbeddedFromResolution.mem_nhds_of_regularAtDim_self (hW.2.2 y hy)
  exact hWY (IsClopen.eq_univ ⟨hW.1, hopen⟩ ⟨x, hx⟩)

/-- **Relative principalization from two given resolutions** (`hir:factorization-from-resolution`; Copy-4, the proof of
`lem:relative-principalization`): for `Y` connected, `W ⊊ Y` a closed connected submanifold of dimension `k`, `𝔞` coherent with
`𝔞 ⊄ 𝓘_W`, a resolution `T₁` of `(Y, W, ∅, 𝔞, 1)` and a resolution `T₂` of `(Y_t, Y_t, ∅, 𝔞_t, 1)`, `𝔞_t` the ambient controlled
transform of `𝔞` along `T₁`, the composite `f = T₁ ∘ T₂` with `H = T₂^* E_{T₁}` and `H' = E_{T₂}` has the factorization data of
`RelativePrincipalization.FactorizationData W k 𝔞` (that file is not imported; its definition is written out). -/
theorem factorizationData_of_isGeoResolution [ConnectedSpace Y] (W : Set Y) (k : ℕ)
    (hW : IsClosedConnectedSubmanifold n W k) (hWY : W ≠ univ) (𝔞 : GermIdeal n Y) (h𝔞 : 𝔞.IsCoherent)
    (hres : ¬ 𝔞.Le (vanishingIdeal (n := n) W)) {Y₁ : CMfd.{u} n} (T₁ : BlowupTower (CMfd.of (n := n) Y) Y₁)
    (h₁ : IsGeoResolution (⟨W, [], 𝔞, 1⟩ : MarkedIdeal n (CMfd.of (n := n) Y)) T₁) {Y₂ : CMfd.{u} n}
    (T₂ : BlowupTower Y₁ Y₂)
    (h₂ : IsGeoResolution (⟨univ, [], (geoTransformAlong (⟨univ, [], 𝔞, 1⟩ : MarkedIdeal n (CMfd.of (n := n) Y)) T₁).ideal, 1⟩ :
      MarkedIdeal n Y₁) T₂) :
    ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y')
      (_ : IsComplexManifold n Y') (f : Y' → Y),
      IsAdaptedBlowupSequence n Y W Y' f ∧
      IsConnected (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W,
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      ∃ H H' : EffectiveDivisor n Y',
        H.support ⊆ exceptionalLocus n f ∧
        Disjoint H'.support (strictTransform n f W) ∧
        GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) W) =
          H.ideal.mul (vanishingIdeal (n := n) (strictTransform n f W)) ∧
        GermIdeal.pullback (m := n) f 𝔞 = H.ideal.mul H'.ideal := by
  set 𝔪 : MarkedIdeal n (CMfd.of (n := n) Y) := ⟨W, [], 𝔞, 1⟩ with h𝔪
  have hkn : k < n := lt_of_ne_univ hW hWY
  have hdom : IsInvDomain k 𝔪 := FactorizationDomain.isInvDomain_of_not_le hW le_rfl h𝔞 hres
  have hWs := FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hW
  obtain ⟨hconn₁, hst₁, hadapt₁, hpb₁, hsupp₁⟩ := tower_data hdom rfl hW hkn T₁ h₁.1
  obtain ⟨hT₁', -⟩ := isGeoTestTower_and_restrictEquiv (𝔪 := 𝔪) rfl hWs h𝔞 T₁ h₁.1
  obtain ⟨-, hcohB, hpbB₁⟩ := pullback_eq_mul_geoTransformAlong (ambient 𝔪) rfl h𝔞 T₁ hT₁'
  set N₁ := (geoTransformAlong 𝔪 T₁).N with hN₁
  set B := (geoTransformAlong (ambient 𝔪) T₁).ideal with hBdef
  have hdisjB : Disjoint N₁ B.zeroLocus := by
    have h := cosupp_geoTransformAlong_eq (𝔪 := 𝔪) rfl hWs h𝔞 T₁ h₁.1
    rw [h₁.2] at h
    exact Set.disjoint_iff_inter_eq_empty.mpr h.symm
  set 𝔪₂ : MarkedIdeal n Y₁ := ⟨univ, [], B, 1⟩ with h𝔪₂
  obtain ⟨hconn₂, hst₂, hdisj₂, hpb₂⟩ := second_data (𝔪 := 𝔪₂) rfl rfl hcohB hconn₁ hdisjB T₂ h₂.1
  have hpbB₂ : GermIdeal.pullback (m := n) T₂.proj B = (BlowupTowerTransforms.exceptionalDivisor T₂).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution 𝔪₂ rfl hcohB rfl T₂ h₂
  set f : Y₂ → Y := T₁.proj ∘ T₂.proj with hf
  have hT₁c := T₁.contMDiff_proj
  have hstf : strictTransform n f W = T₂.proj ⁻¹' N₁ := by
    rw [hf, StrictTransformComposition.strictTransform_comp hT₁c T₂.contMDiff_proj, ← hst₁]
    exact hst₂
  set E₁ := BlowupTowerTransforms.exceptionalDivisor T₁ with hE₁
  refine ⟨Y₂, inferInstance, inferInstance, inferInstance, f, ?_, ?_, ?_, pullDivisor T₂ E₁,
    BlowupTowerTransforms.exceptionalDivisor T₂, ?_, ?_, ?_, ?_⟩
  · exact isAdaptedBlowupSequence_comp hadapt₁ hconn₁ hst₁.symm (𝔪 := 𝔪₂) rfl rfl hcohB hdisjB T₂ h₂.1
  · rw [hstf]
    exact hconn₂.2.1
  · rw [hstf]
    exact hconn₂.2.2
  · rw [support_pullDivisor, hf, exceptionalLocus_comp (hT₁c.mdifferentiable (by simp))
      (T₂.contMDiff_proj.mdifferentiable (by simp))]
    exact fun z hz => Or.inr (hsupp₁ hz)
  · rw [hstf]
    exact hdisj₂
  · have hIW := VanishingIdealCoherent.isCoherent_vanishingIdeal hWs
    have hIN := VanishingIdealCoherent.isCoherent_vanishingIdeal
      (FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hconn₁)
    rw [hstf, pullDivisor_ideal, hf, GermIdealTotalTransform.pullback_comp hT₁c T₂.contMDiff_proj hIW]
    rw [show (𝔪.N : Set Y) = W from rfl] at hpb₁
    rw [hpb₁, GermIdealTotalTransform.pullback_mul T₂.contMDiff_proj (isCoherent_ideal _) hIN, hpb₂]
  · rw [pullDivisor_ideal, hf, GermIdealTotalTransform.pullback_comp hT₁c T₂.contMDiff_proj h𝔞]
    have hpb₁' : GermIdeal.pullback (m := n) T₁.proj 𝔞 = E₁.ideal.mul B := by
      rw [← idealPow_one_of_isCoherent (isCoherent_ideal E₁)]
      exact hpbB₁
    rw [hpb₁', GermIdealTotalTransform.pullback_mul T₂.contMDiff_proj (isCoherent_ideal _) hcohB, hpbB₂]

/-- **Relative principalization from the existence of resolutions** (`hir:factorization-from-resolution`): if every marked ideal
of the domain in dimension `≤ j` on a compact complex manifold of dimension `n ≤ j` has a resolution (a multiple test blow-up
with empty final cosupport; the driver `ResolutionInvariantSeq.exists_isGeoResolution_isCanonical` supplies it from a
resolution invariant), then the factorization data of `RelativePrincipalization.FactorizationData W k 𝔞` exist, written out:
the first resolution is that of `(Y, W, ∅, 𝔞, 1)`, the second that of `(Y_t, Y_t, ∅, 𝔞_t, 1)`; both lie in the domain by
`mc:factorization-domain`. -/
theorem factorizationData_of_exists_resolution {j : ℕ} (hnj : n ≤ j)
    (hR : ∀ {X : CMfd.{u} n} [CompactSpace X] (𝔪 : MarkedIdeal n X), IsInvDomain j 𝔪 →
      ∃ (Z : CMfd.{u} n) (T : BlowupTower X Z), IsGeoResolution 𝔪 T)
    [CompactSpace Y] [ConnectedSpace Y] (W : Set Y) (k : ℕ)
    (hW : IsClosedConnectedSubmanifold n W k) (hWY : W ≠ univ) (𝔞 : GermIdeal n Y) (h𝔞 : 𝔞.IsCoherent)
    (hres : ¬ 𝔞.Le (vanishingIdeal (n := n) W)) :
    ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y')
      (_ : IsComplexManifold n Y') (f : Y' → Y),
      IsAdaptedBlowupSequence n Y W Y' f ∧
      IsConnected (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W,
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      ∃ H H' : EffectiveDivisor n Y',
        H.support ⊆ exceptionalLocus n f ∧
        Disjoint H'.support (strictTransform n f W) ∧
        GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) W) =
          H.ideal.mul (vanishingIdeal (n := n) (strictTransform n f W)) ∧
        GermIdeal.pullback (m := n) f 𝔞 = H.ideal.mul H'.ideal := by
  set 𝔪 : MarkedIdeal n (CMfd.of (n := n) Y) := ⟨W, [], 𝔞, 1⟩ with h𝔪
  have hkn : k < n := lt_of_ne_univ hW hWY
  have : CompactSpace (CMfd.of (n := n) Y) := ‹CompactSpace Y›
  have : ConnectedSpace (CMfd.of (n := n) Y) := ‹ConnectedSpace Y›
  have hdomj : IsInvDomain j 𝔪 := FactorizationDomain.isInvDomain_of_not_le hW (by omega) h𝔞 hres
  have hdom : IsInvDomain k 𝔪 := FactorizationDomain.isInvDomain_of_not_le hW le_rfl h𝔞 hres
  have hWs := FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hW
  obtain ⟨Y₁, T₁, h₁⟩ := hR 𝔪 hdomj
  have : CompactSpace Y₁ := ResolutionDriver.compactSpace_of_tower T₁
  have : ConnectedSpace Y₁ := BlowupConnected.connectedSpace_of_isBlowupSequence T₁.proj T₁.isBlowupSequence
  obtain ⟨hconn₁, -, -, -, -⟩ := tower_data hdom rfl hW hkn T₁ h₁.1
  obtain ⟨hT₁', -⟩ := isGeoTestTower_and_restrictEquiv (𝔪 := 𝔪) rfl hWs h𝔞 T₁ h₁.1
  obtain ⟨-, hcohB, -⟩ := pullback_eq_mul_geoTransformAlong (ambient 𝔪) rfl h𝔞 T₁ hT₁'
  have hdisjB : Disjoint (geoTransformAlong 𝔪 T₁).N (geoTransformAlong (ambient 𝔪) T₁).ideal.zeroLocus := by
    have h := cosupp_geoTransformAlong_eq (𝔪 := 𝔪) rfl hWs h𝔞 T₁ h₁.1
    rw [h₁.2] at h
    exact Set.disjoint_iff_inter_eq_empty.mpr h.symm
  have hres₂ : ¬ (geoTransformAlong (ambient 𝔪) T₁).ideal.Le (vanishingIdeal (n := n) (univ : Set Y₁)) := by
    intro hle
    obtain ⟨x, hx⟩ := hconn₁.2.1.nonempty
    have hxZ : x ∉ (geoTransformAlong (ambient 𝔪) T₁).ideal.zeroLocus := Set.disjoint_left.mp hdisjB hx
    obtain ⟨g, hg, hgx⟩ : ∃ g, (geoTransformAlong (ambient 𝔪) T₁).ideal.mem x g ∧ g x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hxZ hcon
    exact hgx ((hle x g hg).2.self_of_nhds (mem_univ x))
  obtain ⟨Y₂, T₂, h₂⟩ := hR (X := Y₁) (⟨univ, [], (geoTransformAlong (ambient 𝔪) T₁).ideal, 1⟩ : MarkedIdeal n Y₁)
    (FactorizationDomain.isInvDomain_univ_of_not_le hnj hcohB hres₂)
  exact factorizationData_of_isGeoResolution W k hW hWY 𝔞 h𝔞 hres T₁ h₁ T₂ h₂

end Assembly

end

end Hironaka.FactorizationFromResolution
