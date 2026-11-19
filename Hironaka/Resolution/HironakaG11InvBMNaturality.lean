import Hironaka.Resolution.HironakaG11InvBMTangentIndep
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal
import Hironaka.Invariant.MaxLocusLocal

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Naturality of Bierstone--Milman's lower ideals (repair (B'), plan module 8, properties (5)--(7))

Blueprint: `hironaka-g11-inv-bm-max-order.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6c.

The lower ideals `lowerIdealWBM 𝔍 s w T₀ S` (coefficient ideal on the hypersurface `V(w)` of maximal contact, transformed along
`T₀`, plus at the levels `s + 1` the `ℰ`-term of the members `S`) are natural:

* `pullback_exceptionalTermBM_of`: the `ℰ`-term pulls back to the `ℰ`-term of the preimages along every holomorphic map that
  pulls back the vanishing ideals of the members to those of their preimages (open inclusions, biholomorphisms);
* `withExcBM`, `pullback_withExcBM`: the same-mark sum with the `ℰ`-term, and its pullbacks;
* **`lowerIdealWBM_restrict`**: restriction to an open set `U` of the base (the tower `T₀|_U`, the tangent function `w ∘ ι`);
* **`lowerIdealWBM_isTowerIso`**: isomorphisms of towers over a biholomorphism `Φ` (the tangent function `w ∘ Φ`);
* **`inv_transport_opens`**: a general transport of the values of a resolution invariant on the restriction of a marked ideal
  of a stage to an open set `W`, along a biholomorphism of `W` with an open set `W'` of another stage covering a holomorphic
  map `ψ` (the marked ideal there is `ψ^*L`).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMNaturality

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.StepOneValue Hironaka.MarkedIdealRestrictOpen
  Hironaka.HomogenizedIdealAlong Hironaka.BlowupTowerIsomorphism
  Hironaka.HironakaG11InvBMMask Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG11InvBMTangentIndep Hironaka.MarkedIdealBiholomorphism
  Hironaka.HironakaG11InvBMExceptionalTerm
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.IdealWeightPowers
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)
open Hironaka.HomogenizedGlueing (finSumIdeal)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (hol_of_isCoherent)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical
  isCanonical_of_isTowerIso)

noncomputable section

variable {n : ℕ}

/-! ### The `ℰ`-term and the same-mark sum with it -/

section Exc

variable {M M' : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **The `ℰ`-term pulls back to the `ℰ`-term of the preimages** along a holomorphic map which pulls back the vanishing
ideals of the members to those of their preimages (members closed submanifolds, at least one). -/
theorem pullback_exceptionalTermBM_of {f : M' → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {S : List (Set M)} (hS : ∀ H ∈ S, IsClosedSubmanifold n H) (hSne : S ≠ [])
    (hvan : ∀ H ∈ S, GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) H) = vanishingIdeal (n := n) (f ⁻¹' H))
    (e : ℕ) :
    GermIdeal.pullback (m := n) f (exceptionalTermBM (n := n) S e) =
      exceptionalTermBM (n := n) (S.map (f ⁻¹' ·)) e := by
  have hm : 1 ≤ S.length := List.length_pos_iff.mpr hSne
  have hmem : ∀ i < S.length, S.getD i ∅ ∈ S := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hJ : ∀ i < S.length, (idealPow (vanishingIdeal (n := n) (S.getD i ∅)) e).IsCoherent := fun i hi =>
    GermIdealPullbackCalculus.isCoherent_idealPow (VanishingIdealCoherent.isCoherent_vanishingIdeal (hS _ (hmem i hi))) e
  show GermIdeal.pullback (m := n) f (finSumIdeal _ S.length) = finSumIdeal _ (S.map _).length
  rw [HomogenizedIdealAlongTower.pullback_finSumIdeal_of_lt hf hm hJ, List.length_map]
  refine CoefficientIdeal.finSumIdeal_congr fun i hi => ?_
  have hH := hS _ (hmem i hi)
  rw [getD_map_empty _ hi, BlowupExceptionalDivisor.pullback_idealPow hf
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hH) e, hvan _ (hmem i hi)]

/-- **The same-mark sum with the `ℰ`-term of `S`** (same carrier, divisor and mark). -/
def withExcBM (C : MarkedIdeal n M) (S : List (Set M)) : MarkedIdeal n M where
  N := C.N
  E := C.E
  ideal := sumIdeal C.ideal (exceptionalTermBM (n := n) S C.d)
  d := C.d

/-- The lower ideals of the levels `s + 1` are the sums with the `ℰ`-term. -/
theorem lowerIdealWBM_succ {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (s : ℕ) (w : X → ℂ) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (S : List (Set Y₀)) :
    lowerIdealWBM 𝔍 (s + 1) w T₀ S = withExcBM (contactCoeffBM 𝔍 w T₀) S := rfl

/-- **Pullback of the sum with the `ℰ`-term** along a holomorphic map pulling back the vanishing ideals of the members. -/
theorem pullback_withExcBM {f : M' → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {C : MarkedIdeal n M} (hC : C.ideal.IsCoherent) {S : List (Set M)} (hS : ∀ H ∈ S, IsClosedSubmanifold n H)
    (hSne : S ≠ [])
    (hvan : ∀ H ∈ S, GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) H) = vanishingIdeal (n := n) (f ⁻¹' H)) :
    MarkedIdeal.pullback f (withExcBM C S) = withExcBM (MarkedIdeal.pullback f C) (S.map (f ⁻¹' ·)) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  show GermIdeal.pullback (m := n) f (sumIdeal C.ideal (exceptionalTermBM (n := n) S C.d)) =
    sumIdeal (GermIdeal.pullback (m := n) f C.ideal) (exceptionalTermBM (n := n) (S.map (f ⁻¹' ·)) C.d)
  rw [MarkedIdealOperationsTransform.pullback_sumIdeal hf (hol_of_isCoherent hC)
      (hol_of_isCoherent (HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hS _)),
    pullback_exceptionalTermBM_of hf hS hSne hvan]

end Exc

/-! ### Restriction and isomorphisms of towers -/

section Natural

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- A multiple test blow-up of `J̄` is one of `𝓒_N(𝔍_∅)`. -/
theorem isGeoTestTower_coeffEmptyBM_of_barMarked (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) : IsGeoTestTower (coeffEmptyBM 𝔍) T₀ :=
  HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM h𝔍 hd _
    (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary 𝔍 _ (HironakaG11InvBMStage.isGeoTestTower_of_barMarked h𝔍 hd _ hT₀))

/-- The coefficient ideal on maximal contact has a coherent ideal along multiple test blow-ups of `J̄`. -/
theorem isCoherent_contactCoeffBM (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (w : X → ℂ) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) : (contactCoeffBM 𝔍 w T₀).ideal.IsCoherent := by
  have hwfc := HironakaG11InvBMStage.isWellFormed_coeffEmptyBM h𝔍
  exact (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N hwfc.isCoherent T₀
    (isGeoTestTower_coeffEmptyBM_of_barMarked 𝔍 h𝔍 hd T₀ hT₀)).2

/-- **The lower ideals along restricted towers** (property (5)): for `U ⊆ X` open, `T₀` a multiple test blow-up of `J̄` and
members `S` (closed submanifolds; at least one at the levels `≥ 1`), the lower ideal of `𝔍|_U` along `T₀|_U` with the tangent
function `w ∘ ι` and the traces of `S` is the restriction to `T₀⁻¹U` of that of `𝔍` along `T₀`. -/
theorem lowerIdealWBM_restrict (U : Opens X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (s : ℕ) (w : X → ℂ)
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) (S : List (Set Y₀))
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) (hSne : s ≠ 0 → S ≠ []) :
    lowerIdealWBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) s
        (w ∘ (Subtype.val : U → X)) (restrict U T₀) (S.map ((Subtype.val : openPreimage T₀ U → Y₀) ⁻¹' ·)) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (lowerIdealWBM 𝔍 s w T₀ S) := by
  have hc := contactCoeffBM_restrict U 𝔍 h𝔍 hd w T₀ (isGeoTestTower_coeffEmptyBM_of_barMarked 𝔍 h𝔍 hd T₀ hT₀)
  cases s with
  | zero => exact hc
  | succ s =>
    rw [lowerIdealWBM_succ, lowerIdealWBM_succ, hc, pullback_withExcBM contMDiff_subtype_val
      (isCoherent_contactCoeffBM 𝔍 h𝔍 hd w T₀ hT₀) hS (hSne (Nat.succ_ne_zero s))
      (fun H _ => HironakaActualOpenEmbeddingVanishingIdeal.pullback_vanishingIdeal_of_isOpenHoloEmbedding _
        (HironakaBaseChange.isOpenHoloEmbedding_val _) H)]

/-- **The lower ideals along isomorphic towers** (property (6)): for a biholomorphism `Φ : X' ≃ X` and towers `T₀' ≅ T₀` over
`Φ` with last-stage map `χ₀`, `T₀` a multiple test blow-up of `J̄`, the lower ideal of `Φ^*𝔍` along `T₀'` with `w ∘ Φ` and the
`χ₀`-preimages of `S` is the `χ₀`-pullback of that of `𝔍` along `T₀`. -/
theorem lowerIdealWBM_isTowerIso {X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (s : ℕ) (w : X → ℂ) {Y₀' Y₀ : CMfd.{u} n}
    {T₀' : BlowupTower X' Y₀'} {T₀ : BlowupTower X Y₀}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₀} (hiso : IsTowerIso Φ T₀' T₀ χ₀)
    (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) (S : List (Set Y₀)) (hS : ∀ H ∈ S, IsClosedSubmanifold n H)
    (hSne : s ≠ 0 → S ≠ []) :
    lowerIdealWBM (MarkedIdeal.pullback Φ 𝔍) s (w ∘ Φ) T₀' (S.map (χ₀ ⁻¹' ·)) =
      MarkedIdeal.pullback χ₀ (lowerIdealWBM 𝔍 s w T₀ S) := by
  have hc := contactCoeffBM_isTowerIso Φ 𝔍 h𝔍 hd w hiso (isGeoTestTower_coeffEmptyBM_of_barMarked 𝔍 h𝔍 hd T₀ hT₀)
  cases s with
  | zero => exact hc
  | succ s =>
    rw [lowerIdealWBM_succ, lowerIdealWBM_succ, hc, pullback_withExcBM χ₀.contMDiff
      (isCoherent_contactCoeffBM 𝔍 h𝔍 hd w T₀ hT₀) hS (hSne (Nat.succ_ne_zero s))
      (fun H _ => HironakaActualOpenEmbeddingVanishingIdeal.pullback_vanishingIdeal_of_biholomorphism χ₀ H)]

end Natural

/-! ### Transport of the values of a resolution invariant between open sets of two stages -/

section Transport

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Transport of the values of a resolution invariant between open sets of two stages**: let `L` be a marked ideal on `Y₀`
with coherent ideal, `ψ : Y₀' → Y₀` holomorphic, `W ⊆ Y₀`, `W' ⊆ Y₀'` open with a biholomorphism `ξ : W' ≃ W` covering `ψ`,
and towers `T₁` over `Y₀`, `T₁'` over `Y₀'` whose restrictions `T₁'|_{W'} ≅ T₁|_W` are isomorphic over `ξ` (last-stage map
`ξ₁`).  If `L|_W` lies in the domain of `R` with `T₁|_W` a canonical segment, then so does `(ψ^*L)|_{W'}` with `T₁'|_{W'}`, the
cosupports correspond under `ξ₁`, and so do the values on them. -/
theorem inv_transport_opens (R : ResolutionInvariant.{u, v} n k Λ) {Y₀ Y₀' Z Z' : CMfd.{u} n} {L : MarkedIdeal n Y₀}
    (hL : L.ideal.IsCoherent) {ψ : Y₀' → Y₀} (hψ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ)
    {W : Opens Y₀} {W' : Opens Y₀'}
    (ξ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) W)
    (hξ : ∀ q, ((ξ q : W) : Y₀) = ψ q) {T₁ : BlowupTower Y₀ Z} {T₁' : BlowupTower Y₀' Z'}
    {ξ₁ : CMfd.of (n := n) (openPreimage T₁' W') ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T₁ W)}
    (hiso : IsTowerIso ξ (restrict W' T₁') (restrict W T₁) ξ₁)
    (hdom : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → Y₀) L))
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : W → Y₀) L)
      (R.inv (MarkedIdeal.pullback (Subtype.val : W → Y₀) L)) (restrict W T₁)) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W' → Y₀') (MarkedIdeal.pullback ψ L)) ∧
      IsCanonical (MarkedIdeal.pullback (Subtype.val : W' → Y₀') (MarkedIdeal.pullback ψ L))
        (R.inv (MarkedIdeal.pullback (Subtype.val : W' → Y₀') (MarkedIdeal.pullback ψ L))) (restrict W' T₁') ∧
      ∀ p' : openPreimage T₁' W',
        (p' ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W' → Y₀') (MarkedIdeal.pullback ψ L))
            (restrict W' T₁')).cosupp ↔
          ξ₁ p' ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀) L) (restrict W T₁)).cosupp) ∧
        (ξ₁ p' ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀) L) (restrict W T₁)).cosupp →
          R.inv (MarkedIdeal.pullback (Subtype.val : W' → Y₀') (MarkedIdeal.pullback ψ L)) (restrict W' T₁') p' =
            R.inv (MarkedIdeal.pullback (Subtype.val : W → Y₀) L) (restrict W T₁) (ξ₁ p')) := by
  have heq : MarkedIdeal.pullback (Subtype.val : W' → Y₀') (MarkedIdeal.pullback ψ L) =
      MarkedIdeal.pullback ξ (MarkedIdeal.pullback (Subtype.val : W → Y₀) L) :=
    (StepOneTangentChange.pullback_pullback_of_comp hL hψ contMDiff_subtype_val (d := fun q => ψ q.1)
      fun _ => rfl).trans
      (StepOneTangentChange.pullback_pullback_of_comp hL contMDiff_subtype_val ξ.contMDiff (d := fun q => ψ q.1)
        fun q => hξ q).symm
  rw [heq]
  have hTt := isGeoTestTower_of_isCanonical R hdom _ hcan
  have hcos := IsTowerIso.cosupp_geoTransformAlong ξ hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent hiso hTt
  refine ⟨InvDomainTowerAlong.isInvDomain_pullback ξ hdom, isCanonical_of_isTowerIso R hdom ξ hiso hcan,
    fun p' => ⟨by rw [hcos]; rfl, fun hq => R.towerIso ξ _ hdom _ _ _ hiso hcan p' hq⟩⟩

/-- **Cosupports on nested open sets of a stage**: for `V ⊆ W` open and `𝔫|_W` well formed with `T|_W` a multiple test blow-up
of it, a point over `V` lies in the cosupport of `𝔫|_V` along `T|_V` iff it lies in that of `𝔫|_W` along `T|_W`. -/
theorem mem_cosupp_nested_iff {X : CMfd.{u} n} {𝔫 : MarkedIdeal n X} (h𝔫 : 𝔫.ideal.IsCoherent) {W V : Opens X}
    (hVW : V ≤ W) (hwf : (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫).IsWellFormed) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫) (restrict W T))
    (p : openPreimage T V) :
    p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫) (restrict V T)).cosupp ↔
      (⟨(p : Y), MaxLocusLocal.openPreimage_mono T hVW p.2⟩ : openPreimage T W) ∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫) (restrict W T)).cosupp := by
  have hN := hwf.isClosedSubmanifold_N
  have hc := hwf.isCoherent
  have hiso := (MaxLocusLocal.isTowerIso_restrict_nestedOpens (X := X) hVW T).symm
  have heq := MaxLocusLocal.pullback_symm_nestedOpensDiffeo (M := X) h𝔫 hVW
  have hNn := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN (MaxLocusLocal.nestedOpens W V)
  have hcn := GermIdealPullbackCalculus.isCoherent_pullback
    (contMDiff_subtype_val (U := MaxLocusLocal.nestedOpens W V)) hc
  have hTn := isGeoTestTower_restrict (MaxLocusLocal.nestedOpens W V) hN hc (restrict W T) hT
  have hcos := IsTowerIso.cosupp_geoTransformAlong (MaxLocusLocal.nestedOpensDiffeo (n := n) hVW).symm hNn hcn hiso hTn
  rw [heq] at hcos
  rw [hcos, mem_preimage, ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hN hc
    (MaxLocusLocal.nestedOpens W V) (restrict W T) hT, mem_preimage]
  rfl

end Transport

/-! ### The anchor: the lower value through any tangent direction -/

section Anchor

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **The lower value through any tangent direction** (Bierstone--Milman's family; the anchor of properties (4')--(7)): let
`T₀ T₁` be a multiple test blow-up of `J̄`, `q` a point with lower data at level `s` at the split `T₀ T₁` whose image `a` at `T₀`
lies in `cosupp J̄_{T₀}` with level `s`, `u` a tangent direction of `(𝔍.ideal|_N, d)` on `U`, and `O ⊆ T₀⁻¹U` an open set of the
stage containing `a` on which the lower ideal formed with `u` (and the original members through `a`) lies in the domain of `R`
with `T₁|_O` a canonical segment of it.  Given the independence of the hypersurface of maximal contact, the lower value of `q` is
the value of `R` for that lower ideal along `T₁|_O` at `q`. -/
theorem lowerValueG_eq_of_tangent (hTI : TangentIndepBM 𝔍 R) {s : ℕ} {Y₀ Z : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Z) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {q : Z}
    (ha : T₁.proj q ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) (hl : level 𝔍 T₀ (T₁.proj q) = s)
    (hD : LowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s T₀ T₁ q) {U : Set X} {u : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (O : Opens Y₀) (hOU : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U)
    (hqO : T₁.proj q ∈ O)
    (hdom : IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM 𝔍 s u T₀ (throughMembers 𝔍 T₀ (T₁.proj q)))))
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 s u T₀ (throughMembers 𝔍 T₀ (T₁.proj q))))
      (R.inv (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 s u T₀ (throughMembers 𝔍 T₀ (T₁.proj q))))) (restrict O T₁)) :
    lowerValueG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s T₀ T₁ q =
      ((R.inv (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 s u T₀ (throughMembers 𝔍 T₀ (T₁.proj q))))) (restrict O T₁) ⟨q, hqO⟩ : Λ) := by
  obtain ⟨h, hdomM, hcanM, hcosM⟩ := hD
  rw [lowerValueG_eq_of_mem R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) h]
  congr 1
  have hw := isTangentDirectionAlong_tangentChoice_of_nonempty 𝔍
    ⟨_, HironakaG11InvBMCanonicalTail.maskBM_subset_tangent 𝔍 s T₀ _ h⟩
  have hLeq : lowerBM 𝔍 s T₀ (T₁.proj q) = MarkedIdeal.pullback (Subtype.val : maskBM 𝔍 s T₀ (T₁.proj q) → Y₀)
      (lowerIdealWBM 𝔍 s (tangentChoice 𝔍 (T₀.proj (T₁.proj q))).2 T₀ (throughMembers 𝔍 T₀ (T₁.proj q))) := by
    rw [lowerBM_eq, lowerIdealBM_eq_lowerIdealWBM]
  rw [hLeq] at hdomM hcanM hcosM ⊢
  exact (hTI T₀ T₁ hT s _ ha hl U _ u _ hu hw O _ hOU (HironakaG11InvBMCanonicalTail.maskBM_subset_tangent 𝔍 s T₀ _)
    hdom hdomM hcan hcanM q hqO h hcosM).symm

end Anchor

end

end Hironaka.HironakaG11InvBMNaturality
