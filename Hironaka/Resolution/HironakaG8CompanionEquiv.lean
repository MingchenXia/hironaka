import Hironaka.Resolution.HironakaG8ProjEquiv

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The companion ideals of same-mark equivalent marked ideals are Włodarczyk-equivalent (G8 lane, run 0080; D01, E4a)

Blueprint: `hironaka-g8-resume-companion-equivalence.tex`.

Entry E4 of `CanonicalCentres.canonicalInvariant` (the companion value at points of positive order `o`) evaluates the
lower value function on the companion ideal `𝓞(𝔪, o) = companionOf 𝔪 o` (formed on the mask `{ν ≤ o}`).  A first step
toward comparing these values for two equivalent marked ideals is to compare the companions as marked ideals.  Along a
test tower `T` of the companion, its cosupport is `{ν_{𝔪_T} ≥ o} ∩ cosupp 𝔪_T` (`CompanionOpen.companionOf_reduction` and
the restricted equality of the transform of the nonmonomial part with the nonmonomial part of the transform,
`NonmonomialTransformAlong.nonmonomialPart_geoTransformAlong_along`).  Both sets are class data on the cosupport by the
entries E1 already proved (`HironakaG8ProjEquiv`).  This module proves:

* `wEquiv_of_cosupp_eq`: a constructor of Włodarczyk's equivalence from equal cosupports along common test towers;
* `cosupp_companionOf_geoTransformAlong`: along a test tower of `𝓞(𝔪, o)` (`ν ≤ o` on the cosupport, `o ≥ 1`), the
  cosupport of the transform of the companion is `{ν ≥ o} ∩ cosupp 𝔪_T`;
* **`wEquiv_companionOf_of_ordAgree`**, **`projEquiv_wEquiv_companionOf`**: for `A`, `B` in the native domain with the
  same carrier, the same mark and agreeing initial exponents, Włodarczyk-equivalent with equal orders along towers (in
  particular `s(i,ii)`-equivalent), with `ν_A ≤ o` on the cosupport: `𝓞(A, o) ≃ 𝓞(B, o)` (`WEquiv`).

Not here: the comparison of the masks (the companion of the general value is formed on `{ν ≤ o}`, an open set on which
`ν_A`, `ν_B` may differ off the cosupport; global equivalences do not restrict to open sets formally, see the report),
products with a line for the companion, and the lower value itself (E5).  Sorry-free.  Universe `0`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CompanionEquiv

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal GermIdealOrder RelativePrincipalizationSpan
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.MonomialPartAlong (nonmonomialPartAlong monomialPartAlong)
open Hironaka.NonmonomialOrderLocal (nmOrd ordGe mem_ordGe_iff)
open Hironaka.CompanionRebase (companionOf)
open Hironaka.HironakaG8MixedEquiv (isAdmissibleCentre_congr)
open Hironaka.HironakaG8MixedBoundaryExponents (ExpAgree)
open Hironaka.HironakaG8ProjEquiv

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n}

/-- **Włodarczyk's equivalence from equal cosupports along common test towers** (same boundary): admissibility of the
next centre only depends on the current cosupport and boundary. -/
theorem wEquiv_of_cosupp_eq {P Q : MarkedIdeal n X} (hE : P.E = Q.E)
    (hc : ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower P T → IsGeoTestTower Q T →
      (geoTransformAlong P T).cosupp = (geoTransformAlong Q T).cosupp) : WEquiv P Q := by
  have key : ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower P T ↔ IsGeoTestTower Q T := by
    intro Y T
    induction T with
    | refl => exact Iff.rfl
    | step T C π hπ ih =>
      rw [isGeoTestTower_step_iff P T C π hπ, isGeoTestTower_step_iff Q T C π hπ]
      have hET : (geoTransformAlong P T).E = (geoTransformAlong Q T).E :=
        MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE T
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨ih.mp h1, (isAdmissibleCentre_congr hET (hc T h1 (ih.mp h1)) C).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨ih.mpr h1, (isAdmissibleCentre_congr hET (hc T (ih.mpr h1) h1) C).mpr h2⟩
  exact ⟨hE, fun T => ⟨key T, fun hT => hc T hT ((key T).mp hT)⟩⟩

/-- **The cosupport of the transform of the companion** along one of its test towers: `{ν ≥ o} ∩ cosupp 𝔪_T`. -/
theorem cosupp_companionOf_geoTransformAlong {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) (hn : 0 < n)
    {o : ℕ} (ho : 1 ≤ o) (hbound : ∀ x ∈ 𝔪.cosupp, x ∉ ordGe 𝔪 (o + 1)) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (companionOf n 𝔪 o) T) :
    IsGeoTestTower 𝔪 T ∧
      (geoTransformAlong (companionOf n 𝔪 o) T).cosupp = ordGe (geoTransformAlong 𝔪 T) o ∩ (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨hT𝔪, -, hNeq, hcoh, hle, hge, -, -⟩ :=
    NonmonomialTransformAlong.nonmonomialPart_geoTransformAlong_along hn 𝔪 h.isWellFormed h.isNonzeroAlongAt ho
      hbound T hT
  obtain ⟨-, -, -, hcos⟩ := CompanionOpen.companionOf_reduction hn h.isWellFormed h.isNonzeroAlongAt ho hbound T hT
  refine ⟨hT𝔪, ?_⟩
  rw [hcos]
  congr 1
  unfold MarkedIdeals.MarkedIdeal.cosupp
  rw [d_geoTransformAlong, hNeq]
  show cosupport n (geoTransformAlong 𝔪 T).N
      (geoTransformAlong (⟨𝔪.N, 𝔪.E, nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E, o⟩ : MarkedIdeal n X) T).ideal o =
    cosupport n (geoTransformAlong 𝔪 T).N
      (nonmonomialPartAlong n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E) o
  refine Subset.antisymm ?_ ?_
  · exact MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hge o
  · exact MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe
      (fun z _ f hf => IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self (hle z f hf)
        (GermIdeal.IsCoherent.holomorphicAt_mem hcoh hf))) o

variable {kA kB : ℕ} {A B : MarkedIdeal n X}

/-- **E4a: the companions of same-mark equivalent marked ideals are Włodarczyk-equivalent** (from equal orders along
towers; `ν_A ≤ o` on the cosupport, `o ≥ 1`). -/
theorem wEquiv_companionOf_of_ordAgree (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n) {o : ℕ} (ho : 1 ≤ o)
    (hbound : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)) : WEquiv (companionOf n A o) (companionOf n B o) := by
  have hcos0 : A.cosupp = B.cosupp := hW.cosupp_eq
  have hνagree : ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower A T →
      ∀ q, ordGe (geoTransformAlong A T) q ∩ (geoTransformAlong A T).cosupp =
        ordGe (geoTransformAlong B T) q ∩ (geoTransformAlong B T).cosupp := by
    intro Y T hT q
    have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hT
    have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (hW.2 T).2 hT
    have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hT
    have hdB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T hTB
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      have hzB : z ∈ (geoTransformAlong B T).cosupp := hcos ▸ h2
      have hν := nmOrd_geoTransformAlong_eq_of_ordAgree hW hOrd hA hB hN hd h0 T hT h2
      refine ⟨(mem_ordGe_iff hdB.isWellFormed hdB.isNonzeroAlongAt ((geoTransformAlong B T).cosupp_subset_N hzB) q).mpr
        ?_, hzB⟩
      rw [← hν]
      exact (mem_ordGe_iff hdA.isWellFormed hdA.isNonzeroAlongAt ((geoTransformAlong A T).cosupp_subset_N h2) q).mp h1
    · rintro ⟨h1, h2⟩
      have hzA : z ∈ (geoTransformAlong A T).cosupp := hcos.symm ▸ h2
      have hν := nmOrd_geoTransformAlong_eq_of_ordAgree hW hOrd hA hB hN hd h0 T hT hzA
      refine ⟨(mem_ordGe_iff hdA.isWellFormed hdA.isNonzeroAlongAt ((geoTransformAlong A T).cosupp_subset_N hzA) q).mpr
        ?_, hzA⟩
      rw [hν]
      exact (mem_ordGe_iff hdB.isWellFormed hdB.isNonzeroAlongAt ((geoTransformAlong B T).cosupp_subset_N h2) q).mp h1
  have hboundB : ∀ x ∈ B.cosupp, x ∉ ordGe B (o + 1) := by
    intro x hx hxo
    have hmem : x ∈ ordGe (geoTransformAlong B (BlowupTower.refl : BlowupTower X X)) (o + 1) ∩
        (geoTransformAlong B (BlowupTower.refl : BlowupTower X X)).cosupp := ⟨hxo, hx⟩
    rw [← hνagree (BlowupTower.refl : BlowupTower X X) trivial (o + 1)] at hmem
    exact hbound x hmem.2 hmem.1
  refine wEquiv_of_cosupp_eq ?_ fun T hTA hTB => ?_
  · show (companionOf n A o).E = (companionOf n B o).E
    simp only [companionOf, CompanionReductionAlong.companionAlong_E]
    exact hW.1
  · obtain ⟨hT𝔪A, hcA⟩ := cosupp_companionOf_geoTransformAlong hA hn ho hbound T hTA
    obtain ⟨-, hcB⟩ := cosupp_companionOf_geoTransformAlong hB hn ho hboundB T hTB
    rw [hcA, hcB]
    exact hνagree T hT𝔪A o

/-- **E4a for `s(i,ii)`.** -/
theorem projEquiv_wEquiv_companionOf (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n) {o : ℕ} (ho : 1 ≤ o)
    (hbound : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)) : WEquiv (companionOf n A o) (companionOf n B o) :=
  wEquiv_companionOf_of_ordAgree h.wEquiv (projEquiv_towerOrdAgree h hA hB hN hd) hA hB hN hd h0 hn ho hbound

end

end Hironaka.HironakaG8CompanionEquiv
