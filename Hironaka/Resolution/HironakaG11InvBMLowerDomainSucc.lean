import Hironaka.Resolution.HironakaG11InvBMLowerDomain
import Hironaka.Coherence.VanishingIdealCoherent
import Hironaka.MarkedIdeal.CodimOneSupport
import Hironaka.Invariant.MonomialPart

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's lower marked ideals of the levels `s + 1` lie in the domain (repair (B'), plan module 4)

Blueprint: `hironaka-g11-inv-bm-lower.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` (module 4, §6 item 4b).
Source: Bierstone--Milman 2008, §5 Step I, Case B (the marked ideal `𝒞_{q_k} + ℰ` on the hypersurface of maximal contact
`P`, with `ℰ = ∏_{Λ} Σ_{H ∈ Λ} 𝓘_H^{d_𝒞}` built from the original members); Włodarczyk 2005, Step 1a (the points of the
intersections of `s` original members contained in the support are blown up first).

At a point `y₀` of the cosupport of `J̄_{T₀}` in the regime of a level `s + 1 ≥ 1`, the lower marked ideal of
Bierstone--Milman's family is `(P_{T₀}, E_{born}, 𝒞 + ℰ_S, d_𝒞)` on the mask `W = maskA ⊓ tangentOpen` (`S` the original
members through `y₀`).  Its carrier, divisor and mark are those of level `0` (`HironakaG11InvBMLowerDomain`), but the
hypothesis "off the codimension-one part `Z₁`" of level `0` is not available on `maskA`.  The new point is the
nonvanishing of `𝒞 + ℰ_S` along `P_{T₀}` at the points `z ∈ W ∩ P_{T₀} ∩ Z₁`:

* if `𝒞 + ℰ_S` vanished on `P_{T₀}` near `z`, then (`ℰ_S ∋ 1` off the members of `S`) every point of `P_{T₀}` near `z`
  lies on all members of `S`, so the cosupport (inside `P_{T₀}` near `z`, Giraud) lies in `N_{T₀} ∩ H_S`; this
  intersection is regular at `z` of dimension `< dim N_{T₀}` (members transverse to `N_{T₀}`), while the cosupport has
  dimension `dim N_{T₀} - 1` at `z ∈ Z₁`, so by the filling lemma `N_{T₀} ∩ H_S` lies in the cosupport near `z`: `z` is in
  the member locus of its level `s + 1` (the members through `z` are those through `y₀` on `maskA`), i.e. special of the
  level of `y₀` -- which `maskA` excludes.

Main results:
* `isWellFormed_dimLE_contactCoeffBM_of_le`, `isNonzeroAlongAt_contactCoeffBM_of_notMem` (level-`0` ingredients on every
  open `W ⊆ T₀⁻¹U`, resp. pointwise off `Z₁`, without the hypothesis on all of `W`);
* `isCoherent_exceptionalTermBM`, `one_mem_exceptionalTermBM` (the `ℰ`-term is coherent and contains `1` off a member);
* **`isNonzeroAlongAt_lowerIdealBM_succ`**: on the mask of level `s + 1`, `𝒞 + ℰ_S` is nonzero along `P_{T₀}`;
* **`mem_maskBM_and_isInvDomain_lowerBM_succ`**: at a point `y₀` of the cosupport in the regime of level `s + 1`, `y₀` lies in
  its mask and `lowerBM 𝔍 (s + 1) T₀ y₀` lies in `IsInvDomain (k - 1)`;
* `mem_maskBM_and_isInvDomain_lowerBM`: both levels together.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11InvBMLowerDomainSucc

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.MarkedIdealEquivalence Hironaka.MarkedIdealEquivalence.MarkedIdeal
  Hironaka.HomogenizedIdealAlong Hironaka.HomogenizedIdealAlongTower
  Hironaka.CoefficientIdealRestriction Hironaka.CodimOneSupportAlong
  Hironaka.ContactEquivalenceAlong Hironaka.TangentDirectionAlong
  Hironaka.ContactEquivalenceStage Hironaka.ContactStageInvDomain
  Hironaka.MaximalContactAlongTower Hironaka.NormalCrossings
  Hironaka.StepOneValue Hironaka.HironakaG11InvBMMask
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMStage
  Hironaka.HironakaG11InvBMLowerDomain Hironaka.BoundaryCount
  Hironaka.MemberInterLocusAlong Hironaka.InvDomainMemberRestriction
  Hironaka.IdealWeightPowers Hironaka.DivisorExponentAlong
open Hironaka.HomogenizedGlueingTower (strictAlong N_geoTransformAlong)
open Hironaka.HomogenizedGlueing (finSumIdeal)
open Hironaka.RestrictedIdealExtension (sumIdeal le_sumIdeal_left le_sumIdeal_right
  isCoherent_sumIdeal)
open Hironaka.ResolutionInvariantSpec (DimLE IsInvDomain)
open Hironaka.ContactIndependenceAlong (one_le_coeffMarkedAlong_d)

noncomputable section

variable {n : ℕ}

/-! ### Two elementary facts -/

section Elementary

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Nonvanishing along a set is monotone in the ideal. -/
theorem isNonzeroAlongAt_mono {A : Set M} {𝔞 𝔟 : GermIdeal n M} (h : 𝔞.Le 𝔟) {x : M}
    (hx : IsNonzeroAlongAt A 𝔞 x) : IsNonzeroAlongAt A 𝔟 x := by
  obtain ⟨g, hg, hfreq⟩ := hx
  exact ⟨g, h x g hg, hfreq⟩

/-- **The `ℰ`-term contains `1` off a closed member**: if `z ∉ H` for a closed member `H` of `S`, then `1` is a germ of
`Σ_{H ∈ S} 𝓘_H^e` at `z`. -/
theorem one_mem_exceptionalTermBM {S : List (Set M)} {H : Set M} (hH : H ∈ S) (hHc : IsClosed H) {z : M}
    (hz : z ∉ H) (e : ℕ) : (exceptionalTermBM (n := n) S e).mem z fun _ => 1 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hH
  have h1 : (vanishingIdeal (n := n) (S.getD i ∅)).mem z fun _ => 1 := by
    rw [List.getD_eq_getElem _ _ hi]
    exact ⟨holomorphicAt_const 1, eventually_of_mem (hHc.isOpen_compl.mem_nhds hz) fun _ hy hyA => absurd hyA hy⟩
  exact InvertibleIdealQuotient.isInSpanAt_self
    (S := fun s => ∃ j, j < S.length ∧ (idealPow (vanishingIdeal (n := n) (S.getD j ∅)) e).mem z s)
    ⟨i, hi, one_mem_idealPow h1 e⟩ (holomorphicAt_const 1)

/-- **The `ℰ`-term of closed submanifolds is coherent.** -/
theorem isCoherent_exceptionalTermBM {S : List (Set M)} (hS : ∀ H ∈ S, IsClosedSubmanifold n H) (e : ℕ) :
    (exceptionalTermBM (n := n) S e).IsCoherent := by
  refine CoefficientIdeal.isCoherent_finSumIdeal_of_lt fun i hi => ?_
  refine GermIdealPullbackCalculus.isCoherent_idealPow (VanishingIdealCoherent.isCoherent_vanishingIdeal ?_) e
  rw [List.getD_eq_getElem _ _ hi]
  exact hS _ (List.getElem_mem hi)

end Elementary

/-! ### The level-`0` ingredients, on every open set over the tangent open set -/

section Contact

variable {X : CMfd.{u} n} {𝔍 : MarkedIdeal n X} (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (U : Opens X) {u : X → ℂ}
  (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)

include h𝔍 hd hu in
/-- **Giraud at the stage `T₀`**: over `U`, the cosupport of `J̄_{T₀}` lies in the strict transform of the hypersurface of
maximal contact. -/
theorem mem_strictAlong_of_mem_cosupp (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {z : Y₀}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) (hzU : T₀.proj z ∈ U) :
    z ∈ strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hWJ := coeff_homAlong_wEquiv 𝔍 hN h𝔞 hd
  have hT₀a : IsGeoTestTower 𝔍 T₀ := (hWJ.2 T₀).1.mp hT₀
  rw [(hWJ.2 T₀).2 hT₀] at hz
  exact MemberInterTowerAlong.strictAlong_mono T₀ (fun x hx => hx.1)
    (cosupp_subset_strictAlong_along 𝔍 hN h𝔞 hd hu T₀ hT₀a ⟨hz, hzU⟩)

include h𝔍 hd hu in
/-- **The carrier, divisor and mark of `contactCoeffBM` on every open `W ⊆ T₀⁻¹U`**: the restriction of
`contactCoeffBM 𝔍 u T₀` to `W` is well formed of dimension `≤ k - 1` (the part of `isInvDomain_contactCoeffBM_of_le` that does
not use the hypothesis off `Z₁`). -/
theorem isWellFormed_dimLE_contactCoeffBM_of_le {k : ℕ} (hk : DimLE n 𝔍.N k)
    (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) (W : Opens Y₀) (hWU : (W : Set Y₀) ⊆ openPreimage T₀ U) :
    (MarkedIdeal.pullback (Subtype.val : W → Y₀) (contactCoeffBM 𝔍 u T₀)).IsWellFormed ∧
      DimLE n (MarkedIdeal.pullback (Subtype.val : W → Y₀) (contactCoeffBM 𝔍 u T₀)).N (k - 1) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hhol𝔍 := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  have hWJ := coeff_homAlong_wEquiv 𝔍 hN h𝔞 hd
  have hT₀a : IsGeoTestTower 𝔍 T₀ := (hWJ.2 T₀).1.mp hT₀
  have hT₀e := isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀a
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ hT₀e
  obtain ⟨-, hcTc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  refine ⟨⟨isClosedSubmanifold_strictAlong_stage_of_le 𝔍 hN h𝔞 hd U hu T₀ hT₀a W hWU,
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcTc,
    (IsWellFormed.pullback_val (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfc T₀ hT₀c) W).isSNCDivisor,
    ?_⟩, fun y hy => ?_⟩
  · -- transversality: all members of the divisor are born along `T₀`, from centres in the strict transforms of `N ∩ V(u)`
    have hA : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {x | u x = 0})) := by
      have h1 := isClosedSubmanifold_contact_along (X := CMfd.of (n := n) U)
        (𝔪 := MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U)
        (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔞)
        (isTangentDirectionAlong_pullback_val U hhol𝔍 hu)
      have hset : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).N ∩ {x : U | (u ∘ Subtype.val) x = 0} ∩ univ =
          (Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {x | u x = 0}) := by
        ext y
        simp [MarkedIdeal.pullback]
      rw [hset] at h1
      exact h1
    have hcent : ∀ {Z : CMfd.{u} n} (T : BlowupTower X Z) (C : Set Z),
        IsGeoTestTower (coeffEmptyBM 𝔍) T →
        (geoTransformAlong (coeffEmptyBM 𝔍) T).IsAdmissibleCentre C →
        C ∩ T.proj ⁻¹' (U : Set X) ⊆ strictAlong T (𝔍.N ∩ {x | u x = 0}) := by
      intro Z T C hT hC z hz
      have hTe : IsGeoTestTower (emptyBoundary 𝔍) T :=
        (coeffAlong_tower (emptyBoundary 𝔍) hN h𝔞 hd T).1.mp hT
      have hzc : z ∈ (geoTransformAlong (emptyBoundary 𝔍) T).cosupp := by
        rw [cosupp_geoTransformAlong_emptyBoundary, ← cosupp_geoTransformAlong_coeffEmptyBM h𝔍 hd T hTe]
        exact hC.2.1 hz.1
      exact MemberInterTowerAlong.strictAlong_mono T (fun x hx => hx.1)
        (cosupp_subset_strictAlong_along (emptyBoundary 𝔍) hN h𝔞 hd hu T hTe ⟨hzc, hz.2⟩)
    have hD := CodimOneAdmissibleAlong.isTransverse_drop_E_inter_preimage _ hwfc U hA hcent T₀ hT₀c
    have hlen : (coeffEmptyBM 𝔍).E.length = 0 := rfl
    rw [hlen, List.drop_zero] at hD
    have hD' : IsTransverse n (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ∩ (W : Set Y₀))
        (geoTransformAlong (coeffEmptyBM 𝔍) T₀).E := by
      refine CodimOneAdmissibleAlong.isTransverse_of_forall_eventually fun x hx => ?_
      refine ⟨strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ∩ T₀.proj ⁻¹' (U : Set X), ⟨hx.1, hWU hx.2⟩, ?_, hD⟩
      filter_upwards [W.isOpen.mem_nhds hx.2] with y hyW
      exact ⟨fun h => ⟨h.1, hWU h.2⟩, fun h => ⟨h.1, hyW⟩⟩
    have h2 := NormalCrossingsInvariance.isTransverse_preimage (NormalCrossingsInvariance.pullsBackCoordinates_val W) hD'
    have hset : (Subtype.val : W → Y₀) ⁻¹' (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ∩ (W : Set Y₀)) =
        (Subtype.val : W → Y₀) ⁻¹' strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) := by
      ext p
      exact ⟨fun h => h.1, fun h => ⟨h, p.2⟩⟩
    rw [hset] at h2
    exact h2
  · -- dimension
    obtain ⟨j, hj1, hj⟩ := exists_regularAtDim_strictAlong_stage 𝔍 hN h𝔞 hd U hu T₀ hT₀a (hWU y.2) hy
    obtain ⟨j', hj'k, hj'⟩ := InvDomainTowerAlong.dimLE_geoTransformAlong hN h𝔞 hk T₀ hT₀a y hj1.2.1
    have hjj := RegularPointDimension.eq_of_regularAtDim hj1 hj'
    exact ⟨j, by omega, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj⟩

include h𝔍 hd hu in
/-- **Pointwise nonvanishing off `Z₁`**: at a point `y` of the strict transform `P_{T₀}` of the hypersurface of maximal
contact over `U` and off the codimension-one part `Z₁(J̄_{T₀})`, the transform of `𝓒_N(𝔍_∅)` is nonzero along `P_{T₀}`. -/
theorem isNonzeroAlongAt_contactCoeffBM_of_notMem (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y : Y₀}
    (hyU : T₀.proj y ∈ U) (hyP : y ∈ strictAlong T₀ (𝔍.N ∩ {x | u x = 0}))
    (hZ : y ∉ codimOnePartAlong (geoTransformAlong (barMarked 𝔍) T₀).N (geoTransformAlong (barMarked 𝔍) T₀).ideal
      (geoTransformAlong (barMarked 𝔍) T₀).d) :
    IsNonzeroAlongAt (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})) (geoTransformAlong (coeffEmptyBM 𝔍) T₀).ideal y := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hWJ := coeff_homAlong_wEquiv 𝔍 hN h𝔞 hd
  have hT₀a : IsGeoTestTower 𝔍 T₀ := (hWJ.2 T₀).1.mp hT₀
  have hT₀e := isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀a
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ hT₀e
  obtain ⟨-, hcTc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  have hN𝔍J : (geoTransformAlong 𝔍 T₀).N = (geoTransformAlong (barMarked 𝔍) T₀).N := by
    rw [N_geoTransformAlong, N_geoTransformAlong]
    rfl
  obtain ⟨j, hj1, hj⟩ := exists_regularAtDim_strictAlong_stage 𝔍 hN h𝔞 hd U hu T₀ hT₀a hyU hyP
  rw [hN𝔍J] at hj1
  have hV : (openPreimage T₀ U : Set Y₀) ∈ 𝓝 y := (openPreimage T₀ U).isOpen.mem_nhds hyU
  refine CodimOnePartTowerAlong.isNonzeroAlongAt_of_notMem_codimOnePartAlong
    (μ := (geoTransformAlong (barMarked 𝔍) T₀).d) (ν := (geoTransformAlong (coeffEmptyBM 𝔍) T₀).d)
    hcTc hj1 hj ?_ ?_ hZ
  · filter_upwards [hV] with z hzU hz
    exact mem_strictAlong_of_mem_cosupp h𝔍 hd U hu T₀ hT₀ hz hzU
  · filter_upwards [hV] with z hzU hz
    have hz' : z ∈ (contactCoeffBM 𝔍 u T₀).cosupp := hz
    have h1 := (cosupp_contactCoeffBM_iff h𝔍 hd U hu T₀ hT₀a hzU).mp hz'
    rw [← (hWJ.2 T₀).2 hT₀] at h1
    exact h1

end Contact

/-! ### Level `s + 1` -/

section Succ

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **Bierstone--Milman's lower ideal of level `s + 1` is nonzero along its carrier on its mask**: for `𝔍` well formed with
`d ≥ 1`, of maximal order (`0 < n`), along a multiple test blow-up `T₀` of `J̄`, at a point `y₀` of the cosupport of level
`s + 1`, the ideal `𝒞 + ℰ_S` is nonzero along `P_{T₀}` at every point of `P_{T₀}` in the mask `maskA ⊓ tangentOpen`. -/
theorem isNonzeroAlongAt_lowerIdealBM_succ (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀} (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp)
    {s : ℕ} (hl : level 𝔍 T₀ y₀ = s + 1) {z : Y₀} (hzW : z ∈ maskBM 𝔍 (s + 1) T₀ y₀)
    (hzP : z ∈ (lowerIdealBM 𝔍 (s + 1) T₀ y₀).N) :
    IsNonzeroAlongAt (lowerIdealBM 𝔍 (s + 1) T₀ y₀).N (lowerIdealBM 𝔍 (s + 1) T₀ y₀).ideal z := by
  classical
  obtain ⟨hxU, hU⟩ := StepOneLowerDomain.tangentChoice_spec 𝔍
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp 𝔍 h𝔍 hd hmax T₀ hT₀ hy₀)
  set U : Opens X := ⟨(tangentChoice 𝔍 (T₀.proj y₀)).1, hU.isOpen⟩ with hUdef
  set w := (tangentChoice 𝔍 (T₀.proj y₀)).2 with hwdef
  set P := strictAlong T₀ (𝔍.N ∩ {x | w x = 0}) with hPdef
  set 𝔪 := geoTransformAlong (barMarked 𝔍) T₀ with h𝔪def
  set E₀ := origMembers 𝔍 T₀ with hE₀def
  set S := throughMembers 𝔍 T₀ y₀ with hSdef
  have hN : (lowerIdealBM 𝔍 (s + 1) T₀ y₀).N = P := lowerIdealBM_N 𝔍 T₀ y₀ (s + 1)
  have hI : (lowerIdealBM 𝔍 (s + 1) T₀ y₀).ideal =
      sumIdeal (geoTransformAlong (coeffEmptyBM 𝔍) T₀).ideal (exceptionalTermBM S (coeffEmptyBM 𝔍).d) :=
    lowerIdealBM_succ_ideal 𝔍 T₀ y₀ s
  rw [hN] at hzP ⊢
  rw [hI]
  -- the data at the stage `T₀`
  have hJ := StepOneLowerDomain.isWellFormed_barMarked 𝔍 h𝔍
  have h𝔪 : 𝔪.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hd𝔪 : 1 ≤ 𝔪.d := by
    rw [h𝔪def, d_geoTransformAlong]
    exact one_le_coeffMarkedAlong_d _
  have hWJ := coeff_homAlong_wEquiv 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
  have hT₀a : IsGeoTestTower 𝔍 T₀ := (hWJ.2 T₀).1.mp hT₀
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ (isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀a)
  obtain ⟨-, hC⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  have hE₀ : ∀ H ∈ E₀, H ∈ 𝔪.E := fun H hH => List.mem_of_mem_take hH
  have hE₀c : ∀ H ∈ E₀, IsClosed H :=
    StepOneLowerDomain.isClosed_of_mem_origMembers 𝔍 (fun H hH => h𝔍.isSNCDivisor.1 H hH) T₀
  have hSsub : ∀ H ∈ S, H ∈ E₀ := fun H hH => (mem_throughMembers.mp hH).1
  have hSm : ∀ H ∈ S, IsClosedSubmanifold n H := fun H hH => by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (hE₀ H (hSsub H hH))
    exact MonomialPart.isClosedSubmanifold_get hn h𝔪.isSNCDivisor i
  have hEc : (exceptionalTermBM (n := n) S (coeffEmptyBM 𝔍).d).IsCoherent := isCoherent_exceptionalTermBM hSm _
  have hzU : T₀.proj z ∈ U :=
    (interior_subset (s := T₀.proj ⁻¹' (tangentChoice 𝔍 (T₀.proj y₀)).1) hzW.2 : _)
  have hzA : z ∈ maskA 𝔍 T₀ y₀ := hzW.1
  by_contra hne
  -- `𝒞` vanishes on `P` near `z`, so `z ∈ Z₁`
  have hZ : z ∈ codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d := by
    by_contra hZ
    exact hne (isNonzeroAlongAt_mono (le_sumIdeal_left hC)
      (isNonzeroAlongAt_contactCoeffBM_of_notMem h𝔍 hd U hU T₀ hT₀ hzU hzP hZ))
  -- `ℰ_S` vanishes on `P` near `z`, so the points of `P` near `z` lie on all members of `S`
  have hneE : ¬ IsNonzeroAlongAt P (exceptionalTermBM (n := n) S (coeffEmptyBM 𝔍).d) z := fun h =>
    hne (isNonzeroAlongAt_mono (le_sumIdeal_right hEc) h)
  have hPS : ∀ᶠ z' in 𝓝 z, z' ∈ P → ∀ H ∈ S, z' ∈ H := by
    filter_upwards [CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt hEc hneE] with z' hz'
      hz'P H hH
    by_contra hz'H
    have h1 := hz' _ (one_mem_exceptionalTermBM hH (hSm H hH).1 hz'H _)
    exact one_ne_zero (h1.self_of_nhds hz'P)
  have hzS : ∀ H ∈ S, z ∈ H := hPS.self_of_nhds hzP
  -- the original members through `z` are those through `y₀`
  have hiff : ∀ H ∈ E₀, y₀ ∈ H ↔ z ∈ H := fun H hH =>
    ⟨fun hy => hzS H (mem_throughMembers.mpr ⟨hH, hy⟩), fun hz => (interior_subset hzA).1 H hH hz⟩
  have hlev : level 𝔍 T₀ z = level 𝔍 T₀ y₀ := (boundaryCount_eq_of_forall_iff hiff).symm
  -- the regular data at `z ∈ Z₁`
  obtain ⟨k', hNk', hSk'⟩ := hZ
  have hy1 : 1 ≤ boundaryCount E₀ y₀ := by
    have : boundaryCount E₀ y₀ = s + 1 := hl
    omega
  have hSne := membersThrough_nonempty hE₀ hy1
  have hHS : memberInter 𝔪.E (membersThrough 𝔪.E E₀ y₀) = {v | ∀ H ∈ E₀, y₀ ∈ H → v ∈ H} :=
    memberInter_membersThrough hE₀ y₀
  have hzI : z ∈ 𝔪.N ∩ memberInter 𝔪.E (membersThrough 𝔪.E E₀ y₀) := by
    refine ⟨hNk'.2.1, ?_⟩
    rw [hHS]
    exact fun H hH hyH => (hiff H hH).mp hyH
  obtain ⟨j', hj'lt, hj'⟩ := exists_regularAtDim_inter_memberInter_lt hn h𝔪.isSNCDivisor h𝔪.isTransverse hSne hzI hNk'
  -- near `z` the cosupport lies in `N_{T₀} ∩ H_S`
  have hsub : ∀ᶠ z' in 𝓝 z, z' ∈ 𝔪.cosupp → z' ∈ 𝔪.N ∩ memberInter 𝔪.E (membersThrough 𝔪.E E₀ y₀) := by
    filter_upwards [hPS, (openPreimage T₀ U).isOpen.mem_nhds hzU] with z' h1 hz'U hz'c
    have hz'P : z' ∈ P := mem_strictAlong_of_mem_cosupp h𝔍 hd U hU T₀ hT₀ hz'c hz'U
    refine ⟨𝔪.cosupp_subset_N hz'c, ?_⟩
    rw [hHS]
    exact fun H hH hyH => h1 hz'P H (mem_throughMembers.mpr ⟨hH, hyH⟩)
  -- the filling lemma: `N_{T₀} ∩ H_S` lies in the cosupport near `z`
  have hdim : AnalyticDimensionBasics.LocDimGE (n := n) 𝔪.cosupp z j' := fun V hV => by
    obtain ⟨v, hv, k, hk, hvk⟩ := AnalyticDimensionBasics.locDimGE_of_regularAtDim hSk' V hV
    exact ⟨v, hv, k, by omega, hvk⟩
  have hfill := CodimOneSupport.eventually_mem_of_locDimGE
    (isComplexAnalyticSubset_cosupport_along h𝔪.isCoherent h𝔪.isClosedSubmanifold_N hd𝔪) hj' hsub hdim
  -- so `z` is special of the level of `y₀`, which the mask excludes
  have hspec : IsSpecial 𝔍 T₀ z := by
    refine Or.inr ⟨by rw [hlev, hl]; omega, codimOnePartAlong_subset ⟨k', hNk', hSk'⟩, ?_⟩
    filter_upwards [hfill] with z' hz' hz'N hz'S
    refine hz' ⟨hz'N, ?_⟩
    rw [hHS]
    intro H hH hyH
    exact (forall_get_iff (P := fun H => z ∈ H → z' ∈ H)).mp hz'S H hH ((hiff H hH).mp hyH)
  exact (interior_subset hzA).2 ⟨hlev, hspec⟩

/-- **Bierstone--Milman's lower marked ideal of level `s + 1` lies in the domain**: for `𝔍` well formed with `d ≥ 1`, of
maximal order along `N` with `dim N ≤ k` (`0 < n`), along a multiple test blow-up `T₀` of `J̄`, at a point `y₀` of the
cosupport in the regime of level `s + 1`, `y₀` lies in its mask `maskBM 𝔍 (s + 1) T₀ y₀ = maskA ⊓ tangentOpen` and
`lowerBM 𝔍 (s + 1) T₀ y₀` lies in `IsInvDomain (k - 1)`. -/
theorem mem_maskBM_and_isInvDomain_lowerBM_succ (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {k : ℕ} (hk : DimLE n 𝔍.N k) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) {s : ℕ} (hreg : stepRegime 𝔍 (s + 1) T₀ y₀) :
    y₀ ∈ maskBM 𝔍 (s + 1) T₀ y₀ ∧ IsInvDomain (k - 1) (lowerBM 𝔍 (s + 1) T₀ y₀) := by
  refine ⟨mem_maskBM_of_stepRegime 𝔍 h𝔍 hd hn hmax T₀ hT₀ hy₀ hreg, ?_⟩
  obtain ⟨hxU, hU⟩ := StepOneLowerDomain.tangentChoice_spec 𝔍
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp 𝔍 h𝔍 hd hmax T₀ hT₀ hy₀)
  set W := maskBM 𝔍 (s + 1) T₀ y₀ with hWdef
  have hWU : (W : Set Y₀) ⊆ openPreimage T₀ ⟨(tangentChoice 𝔍 (T₀.proj y₀)).1, hU.isOpen⟩ :=
    fun z hz => interior_subset hz.2
  obtain ⟨hwf, hdim⟩ := isWellFormed_dimLE_contactCoeffBM_of_le h𝔍 hd _ hU T₀ hk hT₀ W hWU
  have hJ := StepOneLowerDomain.isWellFormed_barMarked 𝔍 h𝔍
  have hWJ := coeff_homAlong_wEquiv 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
  have hT₀a : IsGeoTestTower 𝔍 T₀ := (hWJ.2 T₀).1.mp hT₀
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ (isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀a)
  obtain ⟨-, hC⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  have h𝔪 := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hSm : ∀ H ∈ throughMembers 𝔍 T₀ y₀, IsClosedSubmanifold n H := fun H hH => by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_take (mem_throughMembers.mp hH).1)
    exact MonomialPart.isClosedSubmanifold_get hn h𝔪.isSNCDivisor i
  have hcoh : (lowerIdealBM 𝔍 (s + 1) T₀ y₀).ideal.IsCoherent := by
    rw [lowerIdealBM_succ_ideal]
    exact isCoherent_sumIdeal hC (isCoherent_exceptionalTermBM hSm _)
  refine ⟨⟨hwf.isClosedSubmanifold_N, GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcoh,
    hwf.isSNCDivisor, hwf.isTransverse⟩, hdim, ?_, fun p hp => ?_⟩
  · show 1 ≤ (lowerIdealBM 𝔍 (s + 1) T₀ y₀).d
    rw [lowerIdealBM_d]
    exact one_le_coeffMarkedAlong_d (emptyBoundary 𝔍)
  · obtain ⟨g, hg, hfreq⟩ := isNonzeroAlongAt_lowerIdealBM_succ 𝔍 h𝔍 hd hn hmax T₀ hT₀ hy₀ hreg.1 p.2 hp
    refine ⟨g ∘ Subtype.val, comp_val_mem_pullback_val W hcoh hg, ?_⟩
    rw [← W.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p] at hfreq
    exact Filter.frequently_map.mp hfreq

/-- **Both levels**: at a point `y₀` of the cosupport in the regime of its level `s`, `y₀` lies in its Bierstone--Milman
mask and the lower marked ideal `lowerBM 𝔍 s T₀ y₀` lies in `IsInvDomain (k - 1)`. -/
theorem mem_maskBM_and_isInvDomain_lowerBM (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {k : ℕ} (hk : DimLE n 𝔍.N k) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) {s : ℕ} (hreg : stepRegime 𝔍 s T₀ y₀) :
    y₀ ∈ maskBM 𝔍 s T₀ y₀ ∧ IsInvDomain (k - 1) (lowerBM 𝔍 s T₀ y₀) := by
  match s, hreg with
  | 0, hreg => exact mem_maskBM_and_isInvDomain_lowerBM_zero 𝔍 h𝔍 hd hn hmax hk T₀ hT₀ hy₀ hreg
  | s + 1, hreg => exact mem_maskBM_and_isInvDomain_lowerBM_succ 𝔍 h𝔍 hd hn hmax hk T₀ hT₀ hy₀ hreg

end Succ

end

end Hironaka.HironakaG11InvBMLowerDomainSucc
