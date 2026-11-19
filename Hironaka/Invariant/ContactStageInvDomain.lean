import Hironaka.Invariant.ContactEquivalenceStage
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.Invariant.CodimOneAdmissibleAlong
import Hironaka.Invariant.CodimOnePartTowerAlong
import Hironaka.Blowup.BlowupTowerIsoTail

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1b's restricted marked ideal lies in the domain of the inductive invariant

Hironaka phase H3 (TN23-ENVELOPES), claimed on I-0981 C-0082 (f) (TN3 withdrew its overlapping claim, C-0086): the domain
hypothesis `hdom` of TN-CLASSICAL's `MaximalOrderStepOneB.inv_contactMarked_eq` (Step 1b of `hir:maximal-order-step`,
`blueprint/src/hironaka.tex`).  At the stage `T₀` where Step 1b starts, the restricted coefficient ideal
`𝓢_{u,T₀} = 𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(u))_{T₀}}`, restricted to `V = T₀⁻¹U`, lies in
`ResolutionInvariantSpec.IsInvDomain (k - 1)` when `dim N ≤ k` and no point of `(N ∩ V(u))_{T₀} ∩ V` lies in the
codimension-one part `Z₁(J̄_{T₀})` (the situation after Step 1ba).  Blueprint `mc:contact-stage-dimension`,
`mc:contact-stage-domain`, `mc:glueing-data-shrink` (`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005
(arXiv `hiron.tex`), Step 1bb (the induced marked ideal `(V(u)_p, J̄_{p|V(u)_p}, (E_p \ E)|_{V(u)_p}, μ̄)`, of dimension one
less, after the codimension-one components have been blown up in Step 1ba).

## Main results

* `exists_regularAtDim_strictAlong_stage`: at a point of `(N ∩ V(u))_{T₀}` over `U`, `N_{T₀}` is regular of some dimension
  `j + 1` and `(N ∩ V(u))_{T₀}` of dimension `j`; `dimLE_strictAlong_stage`: `dim N ≤ k` gives
  `dim (N ∩ V(u))_{T₀} ≤ k - 1` over `U`.
* `isNonzeroAlongAt_stage_of_wEquiv`: if `𝔫_{T₀}|_V ≃ 𝓢_{u,T₀}(𝔫)|_V`, the coefficient ideal of `𝔫_{T₀}` is nonzero along
  `(N ∩ V(u))_{T₀}` at every point of it in `V` off `Z₁(𝔫_{T₀})` (TN3's
  `CodimOnePartTowerAlong.isNonzeroAlongAt_of_notMem_codimOnePartAlong`).
* `isTransverse_strictAlong_stage_coeffHom`: for `J̄ = 𝓒_N(𝓗_N(𝔞), μ)` (`E = ∅`) the divisor `E_{T₀}` (all exceptional) is
  transverse to `(N ∩ V(u))_{T₀}` over `U` (TN3's `CodimOneAdmissibleAlong.isTransverse_drop_E_inter_preimage`).
* **`isInvDomain_stage_coeffHom`** (READING `(𝔞, μ)`): `IsInvDomain (k - 1) (𝓢_{u,T₀}|_V)`.
* `isTangentDirectionAlong_mono`, `exists_glueingDataAlong_trivial_subset`, `contact_independence_along_tail_subset`:
  tangent directions restrict to open subsets, and the glueing data of `BlowupTowerIsoTail.contact_independence_along_tail`
  can be chosen with domain and codomain inside the sets where `u` and `v` are tangent directions (so that the results
  above apply on `U = G.cod`).
* On any open `W ⊆ T₀⁻¹U` (the form of TN-CLASSICAL's `contactMarked N 𝔞 μ u T₀ W`), and for the Step 1 marked ideal
  `𝔍` keeping its divisor `E` (I-0981 C-0087 (b), C-0092): `isInvDomain_stage_coeffHomAlong_of_le` (`J̄ = 𝓒_N(𝓗_N(𝔍))`;
  masking hypothesis: the strict transforms of the original members of `E` miss `(N ∩ V(u))_{T₀} ∩ W`),
  `isInvDomain_stage_coeffHom_of_le` (`E = ∅`); pieces `isTransverse_append_of_forall_notMem` (transversality to `E₁ ++ E₂`
  when the members of `E₁` miss the set) and `isClosedSubmanifold_strictAlong_stage_of_le`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ContactStageInvDomain

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdealAlong
  TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower MarkedIdealEquivalence
  MarkedIdealEquivalence.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen MemberInterTowerAlong
  ContactEquivalenceAlong MaximalContactAlongTower ContactEquivalenceStage DivisorExponentAlong CodimOneSupportAlong
  NormalCrossings
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)
open ResolutionInvariantSpec (DimLE IsInvDomain)

noncomputable section

variable {n : ℕ}

/-! ### Dimension and nonvanishing at the stage `T₀` -/

section Stage

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
  (hd : 1 ≤ 𝔪.d) (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d U u)
  {Y : CMfd.{u} n} (T₀ : BlowupTower X Y) (hT₀ : IsGeoTestTower 𝔪 T₀)

include hN h𝔞 hd hu hT₀ in
/-- **The strict transform of the hypersurface of maximal contact has dimension one less**: at a point of
`(N ∩ V(u))_{T₀}` over `U`, `N_{T₀}` is regular of some dimension `j + 1` and `(N ∩ V(u))_{T₀}` of dimension `j`. -/
theorem exists_regularAtDim_strictAlong_stage {y : Y} (hyU : T₀.proj y ∈ U)
    (hyS : y ∈ strictAlong T₀ (𝔪.N ∩ {x | u x = 0})) :
    ∃ j, RegularAtDim (n := n) (geoTransformAlong 𝔪 T₀).N y (j + 1) ∧
      RegularAtDim (n := n) (strictAlong T₀ (𝔪.N ∩ {x | u x = 0})) y j := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T₀ hT₀
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcT
  have hyN : y ∈ (geoTransformAlong 𝔪 T₀).N := strictAlong_subset_N 𝔪 (fun x hx => hx.1) T₀ hyS
  obtain ⟨W, hyW, -, w, hw, hWS⟩ := exists_isTangentDirectionAlong_stage 𝔪 hN h𝔞 hd U hu T₀ hT₀ hyN hyU
  have hy' : y ∈ (geoTransformAlong 𝔪 T₀).N ∩ {x | w x = 0} ∩ W := by
    rw [hWS]
    exact ⟨hyS, hyW⟩
  obtain ⟨j, hj1, hj⟩ := CodimOnePartTowerAlong.IsTangentDirectionAlong.exists_regularAtDim_succ hhol hNT hw hy'
  exact ⟨j, hj1, RegularPointDimension.regularAtDim_of_inter_eq W.isOpen hyW (by rw [inter_assoc, inter_self, hWS]) hj⟩

include hN h𝔞 hd hu hT₀ in
/-- **`dim N ≤ k` gives `dim (N ∩ V(u))_{T₀} ≤ k - 1` over `U`.** -/
theorem dimLE_strictAlong_stage {k : ℕ} (hk : DimLE n 𝔪.N k) :
    DimLE n ((Subtype.val : openPreimage T₀ U → Y) ⁻¹' strictAlong T₀ (𝔪.N ∩ {x | u x = 0})) (k - 1) := by
  intro y hy
  obtain ⟨j, hj1, hj⟩ := exists_regularAtDim_strictAlong_stage 𝔪 hN h𝔞 hd U hu T₀ hT₀ y.2 hy
  obtain ⟨j', hj'k, hj'⟩ := InvDomainTowerAlong.dimLE_geoTransformAlong hN h𝔞 hk T₀ hT₀ y hj1.2.1
  have hjj := RegularPointDimension.eq_of_regularAtDim hj1 hj'
  exact ⟨j, by omega, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj⟩

include hN h𝔞 hd hu hT₀ in
/-- **The restricted coefficient ideal is nonzero along its submanifold off `Z₁`**: let `𝔫` have the submanifold of `𝔪`,
a coherent ideal, and `T₀` as a multiple test blow-up, with `𝔫_{T₀}|_V ≃ 𝓢_{u,T₀}(𝔫)|_V` on `V = T₀⁻¹U`
(`ContactEquivalenceStage.wEquiv_stage_of_wEquiv`).  At every point `y ∈ V` of `(N ∩ V(u))_{T₀}` outside the codimension-one
part `Z₁(𝔫_{T₀})`, the coefficient ideal of `𝔫_{T₀}` is nonzero along `(N ∩ V(u))_{T₀}` near `y`. -/
theorem isNonzeroAlongAt_stage_of_wEquiv (𝔫 : MarkedIdeal n X) (hN𝔫 : IsClosedSubmanifold n 𝔫.N)
    (h𝔫 : 𝔫.ideal.IsCoherent) (hNN : 𝔫.N = 𝔪.N) (hT₀𝔫 : IsGeoTestTower 𝔫 T₀)
    (h : WEquiv (X := CMfd.of (n := n) (openPreimage T₀ U))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔫 T₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong 𝔫 T₀)) (strictAlong T₀ (𝔪.N ∩ {x | u x = 0})))))
    (y : openPreimage T₀ U) (hy : (y : Y) ∈ strictAlong T₀ (𝔪.N ∩ {x | u x = 0}))
    (hZ : (y : Y) ∉ codimOnePartAlong (geoTransformAlong 𝔫 T₀).N (geoTransformAlong 𝔫 T₀).ideal
      (geoTransformAlong 𝔫 T₀).d) :
    IsNonzeroAlongAt ((Subtype.val : openPreimage T₀ U → Y) ⁻¹' strictAlong T₀ (𝔪.N ∩ {x | u x = 0}))
      (GermIdeal.pullback (m := n) (Subtype.val : openPreimage T₀ U → Y)
        (coeffMarkedAlong (geoTransformAlong 𝔫 T₀)).ideal) y := by
  obtain ⟨hNT𝔫, hcT𝔫⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN𝔫 h𝔫 T₀ hT₀𝔫
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcT𝔫
  have hN𝔫𝔪 : (geoTransformAlong 𝔫 T₀).N = (geoTransformAlong 𝔪 T₀).N := by
    rw [N_geoTransformAlong, N_geoTransformAlong, hNN]
  obtain ⟨j, hj1, hj⟩ := exists_regularAtDim_strictAlong_stage 𝔪 hN h𝔞 hd U hu T₀ hT₀ y.2 hy
  rw [← hN𝔫𝔪] at hj1
  have hcos := h.cosupp_eq
  have hcoh𝔟 : (GermIdeal.pullback (m := n) (Subtype.val : openPreimage T₀ U → Y)
      (coeffMarkedAlong (geoTransformAlong 𝔫 T₀)).ideal).IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (isCoherent_coeffMarkedAlong hcT𝔫 hNT𝔫)
  refine CodimOnePartTowerAlong.isNonzeroAlongAt_of_notMem_codimOnePartAlong
    (N := (Subtype.val : openPreimage T₀ U → Y) ⁻¹' (geoTransformAlong 𝔫 T₀).N)
    (𝔞 := GermIdeal.pullback (m := n) (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔫 T₀).ideal)
    (μ := (geoTransformAlong 𝔫 T₀).d) (ν := (coeffMarkedAlong (geoTransformAlong 𝔫 T₀)).d) (k := j) hcoh𝔟
    (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj1)
    (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj) (Eventually.of_forall fun z hz => ?_)
    (Eventually.of_forall fun z hz => ?_) ?_
  · have hz' : z ∈ (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔫 T₀)).cosupp := hz
    rw [hcos] at hz'
    exact hz'.1
  · have hz' : z ∈ (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong 𝔫 T₀)) (strictAlong T₀ (𝔪.N ∩ {x | u x = 0})))).cosupp := hz
    rw [← hcos] at hz'
    exact hz'
  · rw [CodimOnePartCanonical.codimOnePartAlong_pullback_val _ hhol]
    exact hZ

end Stage

/-! ### The instance `J̄ = 𝓒_N(𝓗_N(𝔞), μ)` -/

section CoeffHom

open HomogenizedGlueingAlongTower (homogenizedMarkedAlong)
open ContactIndependenceAlong (coeffHom_basic one_le_coeffMarkedAlong_d)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ}

/-- **`J̄ = 𝓒_N(𝓗_N(𝔞), μ)` is well formed** (`E = ∅`). -/
theorem isWellFormed_coeffHom (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) :
    (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)).IsWellFormed := by
  obtain ⟨hJN, hJc, -⟩ := coeffHom_basic (μ := μ) h𝔞 hN
  exact ⟨hJN, hJc, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hN⟩

/-- **The exceptional divisor of `J̄_{T₀}` is transverse to `(N ∩ V(u))_{T₀}` over `U`** (READING `(𝔞, μ)`): for `J̄` the
divisor `E_{T₀}` consists of the exceptional members of `T₀`, and their centres lie in the strict transforms of `N ∩ V(u)`
over `U` (Giraud for `(𝔞, μ)`, transported to `J̄` along `J̄ ≃ (𝔞, μ)`). -/
theorem isTransverse_strictAlong_stage_coeffHom (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (U : Opens M) {u : M → ℂ} (hu : IsTangentDirectionAlong N 𝔞 μ U u) {Y : CMfd.{u} n}
    (T₀ : BlowupTower (CMfd.of (n := n) M) Y)
    (hT₀ : IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀) :
    IsTransverse n ((Subtype.val : openPreimage T₀ U → Y) ⁻¹' strictAlong T₀ (N ∩ {x | u x = 0}))
      ((geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀).E.map
        ((Subtype.val : openPreimage T₀ U → Y) ⁻¹' ·)) := by
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  have hJwf := isWellFormed_coeffHom (μ := μ) h𝔞 hN
  have hW : WEquiv (X := CMfd.of (n := n) M) (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ))
      (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) :=
    coeff_homAlong_wEquiv (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) hN h𝔞 hμ
  -- the hypersurface of maximal contact is a closed submanifold of `U`
  have hA : IsClosedSubmanifold n ((Subtype.val : U → M) ⁻¹' (N ∩ {x | u x = 0})) := by
    have h1 := isClosedSubmanifold_contact_along (X := CMfd.of (n := n) U)
      (𝔪 := MarkedIdeal.pullback (Subtype.val : U → M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M))
      (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U)
      (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔞)
      (isTangentDirectionAlong_pullback_val U hhol hu)
    have hset : (MarkedIdeal.pullback (Subtype.val : U → M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M)).N ∩
        {x : U | (u ∘ Subtype.val) x = 0} ∩ univ = (Subtype.val : U → M) ⁻¹' (N ∩ {x | u x = 0}) := by
      ext y
      simp [MarkedIdeal.pullback]
    rw [hset] at h1
    exact h1
  -- the centres over `U` lie in the strict transforms of `N ∩ V(u)`
  have hcent : ∀ {Z : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Z) (C : Set Z),
      IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T →
      (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T).IsAdmissibleCentre C →
      C ∩ T.proj ⁻¹' (U : Set M) ⊆ strictAlong T (N ∩ {x | u x = 0}) := by
    intro Z T C hT hC z hz
    have hTa : IsGeoTestTower (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) T := (hW.2 T).1.mp hT
    have hzc : z ∈ (geoTransformAlong (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) T).cosupp := by
      rw [← (hW.2 T).2 hT]
      exact hC.2.1 hz.1
    exact strictAlong_mono T (fun x hx => hx.1)
      (cosupp_subset_strictAlong_along (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) hN h𝔞 hμ hu T hTa
        ⟨hzc, hz.2⟩)
  have hD := CodimOneAdmissibleAlong.isTransverse_drop_E_inter_preimage (X := CMfd.of (n := n) M) _ hJwf U hA hcent T₀
    hT₀
  have hlen : (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)).E.length = 0 := rfl
  rw [hlen, List.drop_zero] at hD
  have h2 := NormalCrossingsInvariance.isTransverse_preimage
    (NormalCrossingsInvariance.pullsBackCoordinates_val (openPreimage T₀ U)) hD
  have hset : (Subtype.val : openPreimage T₀ U → Y) ⁻¹' (strictAlong T₀ (N ∩ {x | u x = 0}) ∩ T₀.proj ⁻¹' (U : Set M)) =
      (Subtype.val : openPreimage T₀ U → Y) ⁻¹' strictAlong T₀ (N ∩ {x | u x = 0}) := by
    ext p
    exact ⟨fun h => h.1, fun h => ⟨h, p.2⟩⟩
  rw [hset] at h2
  exact h2

/-- **Step 1b's restricted marked ideal lies in the domain of the inductive invariant** (READING `(𝔞, μ)`; the hypothesis
`hdom` of `MaximalOrderStepOneB.inv_contactMarked_eq` with `U = G.cod`): for `𝔞` coherent, `N` a closed submanifold with
`dim N ≤ k`, `μ ≥ 1`, a tangent direction `u` of `(𝔞|_N, μ)` along `N` on an open `U`, a multiple test blow-up `T₀` of
`J̄ = 𝓒_N(𝓗_N(𝔞), μ)`, and no point of `(N ∩ V(u))_{T₀}` over `U` in the codimension-one part `Z₁(J̄_{T₀})` (e.g. after Step
1ba), the marked ideal `𝓢_{u,T₀}|_V = (𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(u))_{T₀}})|_V` on `V = T₀⁻¹U` is well formed, of dimension
`≤ k - 1`, with mark `≥ 1`, and nonzero along its submanifold at each of its points: `IsInvDomain (k - 1)`. -/
theorem isInvDomain_stage_coeffHom {k : ℕ} (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (hk : DimLE n N k) (U : Opens M) {u : M → ℂ} (hu : IsTangentDirectionAlong N 𝔞 μ U u) {Y : CMfd.{u} n}
    (T₀ : BlowupTower (CMfd.of (n := n) M) Y)
    (hT₀ : IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀)
    (hZ : ∀ y ∈ openPreimage T₀ U, y ∈ strictAlong T₀ (N ∩ {x | u x = 0}) →
      y ∉ codimOnePartAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀).N
        (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀).ideal
        (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀).d) :
    IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
      (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
        (strictAlong T₀ (N ∩ {x | u x = 0})))) := by
  obtain ⟨hJN, hJc, -⟩ := coeffHom_basic (μ := μ) h𝔞 hN
  have hJwf := isWellFormed_coeffHom (μ := μ) h𝔞 hN
  have hW : WEquiv (X := CMfd.of (n := n) M) (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ))
      (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) :=
    coeff_homAlong_wEquiv (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) hN h𝔞 hμ
  have hT₀a : IsGeoTestTower (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) T₀ := (hW.2 T₀).1.mp hT₀
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T₀ hT₀
  have hwfT := IsWellFormed.pullback_val
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJwf T₀ hT₀) (openPreimage T₀ U)
  refine ⟨⟨isClosedSubmanifold_strictAlong_stage (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) hN h𝔞 hμ U
      hu T₀ hT₀a,
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (isCoherent_coeffMarkedAlong hcT hNT),
    hwfT.isSNCDivisor, isTransverse_strictAlong_stage_coeffHom h𝔞 hN hμ U hu T₀ hT₀⟩,
    dimLE_strictAlong_stage (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) hN h𝔞 hμ U hu T₀ hT₀a hk,
    one_le_coeffMarkedAlong_d _, fun y hy => ?_⟩
  exact isNonzeroAlongAt_stage_of_wEquiv (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) hN h𝔞 hμ U hu T₀
    hT₀a _ hJN hJc rfl hT₀ (wEquiv_stage_coeffHom h𝔞 hN hμ U hu T₀ hT₀) y hy (hZ y y.2 hy)

end CoeffHom

/-! ### Glueing data inside the sets of the two tangent directions -/

section Glueing

open HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong GlueingTrivialAction BlowupTowerIsomorphism
  BlowupTowerIsoTail
open ContactIndependenceAlong (one_le_coeffMarkedAlong_d)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ}

/-- **Tangent directions along `N` restrict to open subsets.** -/
theorem isTangentDirectionAlong_mono {U V : Set M} (hu : IsTangentDirectionAlong N 𝔞 μ U u) (hV : IsOpen V)
    (hVU : V ⊆ U) : IsTangentDirectionAlong N 𝔞 μ V u :=
  ⟨hV, fun x hx => hu.mem x (hVU hx), fun x hx h0 => hu.multiplicity_one x (hVU hx) h0⟩

/-- **Glueing data acting trivially, inside the sets of the two tangent directions** (`exists_glueingDataAlong_trivial` with
its open set `W` shrunk to `W ∩ U ∩ U'`). -/
theorem exists_glueingDataAlong_trivial_subset (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    {x : M} (hx : x ∈ cosupport n N 𝔞 μ) {U U' : Set M} (hu : IsTangentDirectionAlong N 𝔞 μ U u) (hxU : x ∈ U)
    (hv : IsTangentDirectionAlong N 𝔞 μ U' v) (hxU' : x ∈ U') :
    ∃ G : GlueingDataAlong N 𝔞 μ u v, x ∈ G.W ∧ G.W ⊆ U ∩ U' ∧ ∀ y ∈ G.W, y ∈ zeroSet (glueIdealAlong N 𝔞 μ) →
      TrivialAt G.φ (glueIdealAlong N 𝔞 μ) y ∧ TrivialAt G.ψ (glueIdealAlong N 𝔞 μ) y := by
  obtain ⟨G, hxW, htriv⟩ := exists_glueingDataAlong_trivial h𝔞 hN hμ hx hu hxU hv hxU'
  refine ⟨⟨G.φ, G.ψ, G.W ∩ (U ∩ U'), ⟨G.pair.isOpen.inter (hu.isOpen.inter hv.isOpen),
      fun p hp => G.pair.mdifferentiableAt_left p hp.1, fun p hp => G.pair.mdifferentiableAt_right p hp.1,
      fun p hp => G.pair.left_inv p hp.1, fun p hp => G.pair.right_inv p hp.1⟩,
    fun y hy => G.pullback_iff y hy.1, fun p hp => G.comp_eq p hp.1, fun y hy => G.apply_eq_self y hy.1,
    fun p hp => G.mem_N_iff p hp.1⟩, ⟨hxW, hxU, hxU'⟩, inter_subset_right, fun y hy hz => htriv y hy.1 hz⟩

/-- **`BlowupTowerIsoTail.contact_independence_along_tail` with the glueing neighbourhoods inside the sets of the two
tangent directions**: the domain `U'` and the codomain `U` of the glueing biholomorphism lie in `U₁ ∩ U₂`, so that `u` and
`v` are tangent directions on `U` and `U'` (`isTangentDirectionAlong_mono`) and the stage results
(`ContactEquivalenceStage.isGeoTestTower_tail_coeffHom`, `isInvDomain_stage_coeffHom`) apply with the open set `U`. -/
theorem contact_independence_along_tail_subset (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) {x : M}
    (hx : x ∈ cosupport n N 𝔞 μ) {U₁ U₂ : Set M} (hu : IsTangentDirectionAlong N 𝔞 μ U₁ u) (hxU₁ : x ∈ U₁)
    (hv : IsTangentDirectionAlong N 𝔞 μ U₂ v) (hxU₂ : x ∈ U₂) :
    ∃ G : GlueingDataAlong N 𝔞 μ u v, x ∈ G.dom ∧ x ∈ G.cod ∧ (G.dom : Set M) ⊆ U₁ ∩ U₂ ∧
      (G.cod : Set M) ⊆ U₁ ∩ U₂ ∧
      ∀ {Y Z : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y) (T₁ : BlowupTower Y Z),
        IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) (T₀.append T₁) →
        ∃ (Φ₀ : CMfd.of (n := n) (openPreimage T₀ G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
              CMfd.of (n := n) (openPreimage T₀ G.cod))
          (χ : CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ G.dom))
            ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
              CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ G.cod))),
          IsGlueingLiftAlong G T₀ Φ₀ ∧
          IsTowerIso Φ₀ (restrict (openPreimage T₀ G.dom) T₁) (restrict (openPreimage T₀ G.cod) T₁) χ ∧
          MarkedIdeal.pullback Φ₀ (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ G.cod → Y)
              (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
                (strictAlong T₀ (N ∩ {x | u x = 0})))) =
            MarkedIdeal.pullback (Subtype.val : openPreimage T₀ G.dom → Y)
              (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
                (strictAlong T₀ (N ∩ {x | v x = 0}))) ∧
          ∀ p : openPreimage T₁ (openPreimage T₀ G.dom),
            (p : Z) ∈ (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) (T₀.append T₁)).cosupp →
              (χ p : Z) = p := by
  obtain ⟨G, hxW, hWsub, htriv⟩ := exists_glueingDataAlong_trivial_subset h𝔞 hN hμ hx hu hxU₁ hv hxU₂
  obtain ⟨hxd, hxc⟩ := G.mem_dom_and_mem_cod hxW hx
  refine ⟨G, hxd, hxc, fun p hp => hWsub hp.1, fun q hq => hWsub hq.1, fun T₀ T₁ hT => ?_⟩
  obtain ⟨Φ₀, χ, hL₀, -, hχ, -, hS₀, -, -, hfix⟩ := exists_isTowerIso_tail_coeffHom G h𝔞 hN hμ htriv T₀ T₁ hT
  exact ⟨Φ₀, χ, hL₀, hχ, hS₀, hfix⟩

end Glueing

/-! ### Any open set inside `T₀⁻¹U`, and the divisor of the Step 1 marked ideal masked on it -/

section Masked

open ContactIndependenceAlong (one_le_coeffMarkedAlong_d)

/-- **Transversality to `E₁ ++ E₂`** from transversality to `E₂` when no member of `E₁` meets the set. -/
theorem isTransverse_append_of_forall_notMem {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {A : Set M} {E₁ E₂ : List (Set M)} (h₂ : IsTransverse n A E₂) (h₁ : ∀ H ∈ E₁, ∀ x ∈ A, x ∉ H) :
    IsTransverse n A (E₁ ++ E₂) := by
  classical
  intro x hx
  obtain ⟨S₀, S, ⟨Φ, hΦt, hΦ0, hΦA⟩, hS⟩ := h₂ x hx
  have hidx : ∀ i : Fin (E₁ ++ E₂).length, x ∈ (E₁ ++ E₂).get i →
      ∃ j : Fin E₂.length, E₂.get j = (E₁ ++ E₂).get i := by
    intro i hi
    rcases List.mem_append.mp (List.get_mem _ _ : (E₁ ++ E₂).get i ∈ E₁ ++ E₂) with h | h
    · exact absurd hi (h₁ _ h x hx)
    · exact List.mem_iff_get.mp h
  refine ⟨S₀, fun i => if hi : x ∈ (E₁ ++ E₂).get i then S (hidx i hi).choose else ∅, ⟨Φ, hΦt, hΦ0, ?_⟩,
    fun i hi => ?_⟩
  · rintro (_ | i) hxi y hy hyΦ
    · exact hΦA none hxi hy hyΦ
    · simp only [Option.elim] at hxi ⊢
      rw [dif_pos hxi]
      have hj := (hidx i hxi).choose_spec
      have h1 := hΦA (some (hidx i hxi).choose) (by simp only [Option.elim]; rw [hj]; exact hxi) hy hyΦ
      simp only [Option.elim] at h1
      rw [hj] at h1
      exact h1
  · simp only [dif_pos hi]
    exact hS _ (by rw [(hidx i hi).choose_spec]; exact hi)

variable {X : CMfd.{u} n}

/-- **The strict transform of the hypersurface of maximal contact is a closed submanifold of every open `W ⊆ T₀⁻¹U`.** -/
theorem isClosedSubmanifold_strictAlong_stage_of_le (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d U u) {Y : CMfd.{u} n} (T₀ : BlowupTower X Y)
    (hT₀ : IsGeoTestTower 𝔪 T₀) (W : Opens Y) (hWU : (W : Set Y) ⊆ openPreimage T₀ U) :
    IsClosedSubmanifold n ((Subtype.val : W → Y) ⁻¹' strictAlong T₀ (𝔪.N ∩ {x | u x = 0})) := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T₀ hT₀
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcT
  have hSN : strictAlong T₀ (𝔪.N ∩ {x | u x = 0}) ⊆ (geoTransformAlong 𝔪 T₀).N :=
    strictAlong_subset_N 𝔪 (fun x hx => hx.1) T₀
  refine ⟨isClosed_of_closure_subset fun y hy => ?_, fun y hy => ?_⟩
  · have hyN : (y : Y) ∈ (geoTransformAlong 𝔪 T₀).N := by
      have h1 : y ∈ closure ((Subtype.val : W → Y) ⁻¹' (geoTransformAlong 𝔪 T₀).N) :=
        closure_mono (preimage_mono hSN) hy
      rw [(hNT.1.preimage continuous_subtype_val).closure_eq] at h1
      exact h1
    obtain ⟨O, hyO, -, w, hw, hOS⟩ := exists_isTangentDirectionAlong_stage 𝔪 hN h𝔞 hd U hu T₀ hT₀ hyN (hWU y.2)
    have hwc : ContinuousAt w (y : Y) :=
      (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong hhol _ y w (hw.mem y hyO)).self_of_nhds.continuousAt
    have hOy : ∀ᶠ p : W in 𝓝 y, (p : Y) ∈ O :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (O.isOpen.mem_nhds hyO)
    have hfreq : ∃ᶠ p : W in 𝓝 y, w (p : Y) = 0 := by
      refine ((mem_closure_iff_frequently.mp hy).and_eventually hOy).mono fun p hp => ?_
      have h2 : (p : Y) ∈ strictAlong T₀ (𝔪.N ∩ {x | u x = 0}) ∩ O := hp
      rw [← hOS] at h2
      exact h2.1.2
    have hy0 : w y = 0 := by
      have ht : Tendsto (fun p : W => w (p : Y)) (𝓝 y) (𝓝 (w y)) := hwc.comp continuous_subtype_val.continuousAt
      exact mem_singleton_iff.mp (isClosed_singleton.mem_of_frequently_of_tendsto
        (hfreq.mono fun p hp => mem_singleton_iff.mpr hp) ht)
    have h3 : (y : Y) ∈ (geoTransformAlong 𝔪 T₀).N ∩ {x | w x = 0} ∩ O := ⟨⟨hyN, hy0⟩, hyO⟩
    rw [hOS] at h3
    exact h3.1
  · obtain ⟨j, -, hj⟩ := exists_regularAtDim_strictAlong_stage 𝔪 hN h𝔞 hd U hu T₀ hT₀ (hWU y.2) hy
    exact ⟨j, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj⟩

/-- **Step 1b's restricted marked ideal is in the domain of the inductive invariant on every open `W ⊆ T₀⁻¹U`, for the
Step 1 marked ideal with its divisor kept and masked on `W`** (I-0981 C-0087 (b), C-0092): let `𝔍 = (X, N, E, 𝔞, d)` be well
formed with `d ≥ 1` and `dim N ≤ k`, `J̄ = 𝓒_N(𝓗_N(𝔍))`, `u` a tangent direction of `(𝔞|_N, d)` along `N` on an open `U`,
`T₀` a multiple test blow-up of `J̄` and `W ⊆ T₀⁻¹U` open.  If no point of `(N ∩ V(u))_{T₀} ∩ W` lies in `Z₁(J̄_{T₀})`, nor on
the strict transforms of the original members of `E` (the first `#E` members of `E_{T₀}`), then
`(𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(u))_{T₀}})|_W` lies in `IsInvDomain (k - 1)`. -/
theorem isInvDomain_stage_coeffHomAlong_of_le {k : ℕ} (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hk : DimLE n 𝔍.N k) (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u)
    {Y : CMfd.{u} n} (T₀ : BlowupTower X Y) (hT₀ : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀)
    (W : Opens Y) (hWU : (W : Set Y) ⊆ openPreimage T₀ U)
    (hZ : ∀ y ∈ W, y ∈ strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) →
      y ∉ codimOnePartAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).N
        (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).ideal
        (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).d)
    (hmask : ∀ H ∈ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).E.take 𝔍.E.length,
      ∀ y ∈ W, y ∈ strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) → y ∉ H) :
    IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : W → Y)
      (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
        (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hhol𝔍 := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  have hJwf : (coeffMarkedAlong (homMarkedAlong 𝔍)).IsWellFormed := ⟨hJN, hJc, h𝔍.isSNCDivisor, h𝔍.isTransverse⟩
  have hW := coeff_homAlong_wEquiv 𝔍 hN h𝔞 hd
  have hT₀a : IsGeoTestTower 𝔍 T₀ := (hW.2 T₀).1.mp hT₀
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T₀ hT₀
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcT
  have hdT : 1 ≤ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).d := by
    rw [d_geoTransformAlong]; exact one_le_coeffMarkedAlong_d _
  have hcC : (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong hcT hNT
  have hSN : strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ⊆ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).N :=
    strictAlong_subset_N (coeffMarkedAlong (homMarkedAlong 𝔍)) (fun x hx => hx.1) T₀
  -- Giraud at the stage `T₀` over `U`
  have hGir : ∀ z ∈ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).cosupp, T₀.proj z ∈ U →
      z ∈ strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) := by
    intro z hz hzU
    rw [(hW.2 T₀).2 hT₀] at hz
    exact strictAlong_mono T₀ (fun x hx => hx.1) (cosupp_subset_strictAlong_along 𝔍 hN h𝔞 hd hu T₀ hT₀a ⟨hz, hzU⟩)
  refine ⟨⟨isClosedSubmanifold_strictAlong_stage_of_le 𝔍 hN h𝔞 hd U hu T₀ hT₀a W hWU,
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcC,
    (IsWellFormed.pullback_val (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJwf T₀ hT₀) W).isSNCDivisor,
    ?_⟩, fun y hy => ?_, one_le_coeffMarkedAlong_d _, fun y hy => ?_⟩
  · -- transversality: the exceptional members (TN3's lemma), and the masked original members miss the set
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
        IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T →
        (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T).IsAdmissibleCentre C →
        C ∩ T.proj ⁻¹' (U : Set X) ⊆ strictAlong T (𝔍.N ∩ {x | u x = 0}) := by
      intro Z T C hT hC z hz
      have hTa : IsGeoTestTower 𝔍 T := (hW.2 T).1.mp hT
      have hzc : z ∈ (geoTransformAlong 𝔍 T).cosupp := by
        rw [← (hW.2 T).2 hT]
        exact hC.2.1 hz.1
      exact strictAlong_mono T (fun x hx => hx.1) (cosupp_subset_strictAlong_along 𝔍 hN h𝔞 hd hu T hTa ⟨hzc, hz.2⟩)
    have hD := CodimOneAdmissibleAlong.isTransverse_drop_E_inter_preimage _ hJwf U hA hcent T₀ hT₀
    have hD' : IsTransverse n (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ∩ (W : Set Y))
        ((geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).E.drop 𝔍.E.length) := by
      refine CodimOneAdmissibleAlong.isTransverse_of_forall_eventually fun x hx => ?_
      refine ⟨strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ∩ T₀.proj ⁻¹' (U : Set X), ⟨hx.1, hWU hx.2⟩, ?_, hD⟩
      filter_upwards [W.isOpen.mem_nhds hx.2] with y hyW
      exact ⟨fun h => ⟨h.1, hWU h.2⟩, fun h => ⟨h.1, hyW⟩⟩
    have hT' := isTransverse_append_of_forall_notMem hD' (fun H hH x hx => hmask H hH x hx.2 hx.1)
    rw [List.take_append_drop] at hT'
    have h2 := NormalCrossingsInvariance.isTransverse_preimage (NormalCrossingsInvariance.pullsBackCoordinates_val W) hT'
    have hset : (Subtype.val : W → Y) ⁻¹' (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ∩ (W : Set Y)) =
        (Subtype.val : W → Y) ⁻¹' strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) := by
      ext p
      exact ⟨fun h => h.1, fun h => ⟨h, p.2⟩⟩
    rw [hset] at h2
    exact h2
  · -- dimension
    obtain ⟨j, hj1, hj⟩ := exists_regularAtDim_strictAlong_stage 𝔍 hN h𝔞 hd U hu T₀ hT₀a (hWU y.2) hy
    obtain ⟨j', hj'k, hj'⟩ := InvDomainTowerAlong.dimLE_geoTransformAlong hN h𝔞 hk T₀ hT₀a y hj1.2.1
    have hjj := RegularPointDimension.eq_of_regularAtDim hj1 hj'
    exact ⟨j, by omega, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj⟩
  · -- nonvanishing along the submanifold (TN3's lemma, with Giraud and le:S at the stage)
    have hN𝔍J : (geoTransformAlong 𝔍 T₀).N = (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).N := by
      rw [N_geoTransformAlong, N_geoTransformAlong]
      rfl
    obtain ⟨j, hj1, hj⟩ := exists_regularAtDim_strictAlong_stage 𝔍 hN h𝔞 hd U hu T₀ hT₀a (hWU y.2) hy
    rw [hN𝔍J] at hj1
    refine CodimOnePartTowerAlong.isNonzeroAlongAt_of_notMem_codimOnePartAlong
      (N := (Subtype.val : W → Y) ⁻¹' (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).N)
      (𝔞 := GermIdeal.pullback (m := n) (Subtype.val : W → Y)
        (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).ideal)
      (μ := (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).d)
      (ν := (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀)).d) (k := j)
      (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcC)
      (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj1)
      (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj) (Eventually.of_forall fun z hz => ?_)
      (Eventually.of_forall fun z hz => ?_) ?_
    · have hz' : z ∈ (MarkedIdeal.pullback (Subtype.val : W → Y)
          (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀)).cosupp := hz
      rw [cosupp_pullback_val _ hhol W] at hz'
      exact hGir z hz' (hWU z.2)
    · have hz' : z ∈ (MarkedIdeal.pullback (Subtype.val : W → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))).cosupp := hz
      rw [cosupp_pullback_val (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}))) (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcC) W,
        CoefficientIdealAlongRestriction.cosupp_coeffMarkedAlong_withN hNT.2 hhol hdT hSN] at hz'
      show z ∈ (MarkedIdeal.pullback (Subtype.val : W → Y)
        (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀)).cosupp
      rw [cosupp_pullback_val _ hhol W]
      exact hz'.1
    · rw [CodimOnePartCanonical.codimOnePartAlong_pullback_val _ hhol]
      exact hZ y y.2 hy

/-- **Step 1b's restricted marked ideal is in the domain of the inductive invariant on every open `W ⊆ T₀⁻¹U`** (`E = ∅`,
`J̄ = 𝓒_N(𝓗_N(𝔞), μ)`; READING `(𝔞, μ)`): `isInvDomain_stage_coeffHom` with any `W` in place of `T₀⁻¹U` -- the form of
`MaximalOrderStepOneB.contactMarked N 𝔞 μ u T₀ W`. -/
theorem isInvDomain_stage_coeffHom_of_le {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {k : ℕ} (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) (hk : DimLE n N k) (U : Opens M) {u : M → ℂ}
    (hu : IsTangentDirectionAlong N 𝔞 μ U u) {Y : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y)
    (hT₀ : IsGeoTestTower (coeffMarkedAlong (HomogenizedGlueingAlongTower.homogenizedMarkedAlong N 𝔞 μ)) T₀)
    (W : Opens Y) (hWU : (W : Set Y) ⊆ openPreimage T₀ U)
    (hZ : ∀ y ∈ W, y ∈ strictAlong T₀ (N ∩ {x | u x = 0}) →
      y ∉ codimOnePartAlong
        (geoTransformAlong (coeffMarkedAlong (HomogenizedGlueingAlongTower.homogenizedMarkedAlong N 𝔞 μ)) T₀).N
        (geoTransformAlong (coeffMarkedAlong (HomogenizedGlueingAlongTower.homogenizedMarkedAlong N 𝔞 μ)) T₀).ideal
        (geoTransformAlong (coeffMarkedAlong (HomogenizedGlueingAlongTower.homogenizedMarkedAlong N 𝔞 μ)) T₀).d) :
    IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : W → Y)
      (withN (coeffMarkedAlong
        (geoTransformAlong (coeffMarkedAlong (HomogenizedGlueingAlongTower.homogenizedMarkedAlong N 𝔞 μ)) T₀))
        (strictAlong T₀ (N ∩ {x | u x = 0})))) :=
  isInvDomain_stage_coeffHomAlong_of_le (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M)
    ⟨hN, h𝔞, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hN⟩ hμ hk U hu T₀ hT₀ W hWU hZ
    (fun H hH => by simp at hH)

end Masked

end

end Hironaka.ContactStageInvDomain
