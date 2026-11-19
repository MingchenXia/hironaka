import Hironaka.Resolution.HironakaG11InvSameMarkSum
import Hironaka.Resolution.HironakaG11InvBMLowerDomainSucc
import Hironaka.Invariant.SmoothCentreLocus

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The `ℰ`-term of Bierstone--Milman's lower family under admissible blowups (repair (B'), plan module 5, level `s + 1`)

Blueprint: `hironaka-g11-inv-bm-lower.tex`.  Source: Bierstone--Milman 2008, §5 Step I, Case B: the term
`ℰ = Σ_{H ∈ S} (𝓘_H, 1)^{d_𝒞}` built from the original members `S` through the point; since the centres of the year lie in
the intersection of these members, its transforms are the same term for the strict transforms of the members ("`ℰ` is
the same along the year").  For a list `S` of closed submanifolds, a closed submanifold `N` and a mark `e ≥ 1`, let
`excMarked n N E S e = (N, E, Σ_{H ∈ S} 𝓘_H^e, e)`:

* `cosupp_excMarked`: `cosupp = N ∩ H_S` (the points of `N` on all members of `S`);
* `pullback_exceptionalTermBM`: for a blowup `π` along `C ⊆ ⋂ S`, `π^*(Σ 𝓘_H^e) = (π^*𝓘_C)^e · Σ 𝓘_{H'}^e`
  (`π^*𝓘_H = 𝒪(-D) · 𝓘_{H'}`, `BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul`);
* **`geoTransformAlong_excMarked`**: along every multiple test blow-up `T`, the transform is restricted-equivalent to
  `excMarked n N_T E_T S_T e` with `S_T` the strict transforms of the members, which stay closed submanifolds;
  `cosupp_geoTransformAlong_excMarked`: its cosupport is `N_T ∩ H_{S_T}`;
* `pullback_val_exceptionalTermBM`: on an open set `W`, the restriction of the `ℰ`-term is the `ℰ`-term of the traces.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11InvBMExceptionalTerm

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers
  Hironaka.GermIdealPullbackCalculus Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupStrictSubmanifold
  Hironaka.BlowupTowers Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG11InvSameMarkSum
open Hironaka.HomogenizedGlueing (finSumIdeal)
open Hironaka.HomogenizedGlueingTower (strictAlong N_geoTransformAlong)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv hol_of_isCoherent)

noncomputable section

variable {n : ℕ}

/-! ### The `ℰ`-marked ideal -/

section OneSpace

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable (n) in
/-- **The `ℰ`-marked ideal** `(N, E, Σ_{H ∈ S} 𝓘_H^e, e)`. -/
def excMarked (N : Set M) (E S : List (Set M)) (e : ℕ) : MarkedIdeal n M where
  N := N
  E := E
  ideal := exceptionalTermBM S e
  d := e

@[simp] theorem excMarked_N (N : Set M) (E S : List (Set M)) (e : ℕ) : (excMarked n N E S e).N = N := rfl
@[simp] theorem excMarked_E (N : Set M) (E S : List (Set M)) (e : ℕ) : (excMarked n N E S e).E = E := rfl
@[simp] theorem excMarked_d (N : Set M) (E S : List (Set M)) (e : ℕ) : (excMarked n N E S e).d = e := rfl
theorem excMarked_ideal (N : Set M) (E S : List (Set M)) (e : ℕ) :
    (excMarked n N E S e).ideal = exceptionalTermBM S e := rfl

/-- The `i`-th member, as read by the `ℰ`-term, of a mapped list. -/
theorem getD_map_empty {S : List (Set M)} {M' : Type*} (f : Set M → Set M') {i : ℕ} (hi : i < S.length) :
    (S.map f).getD i ∅ = f (S.getD i ∅) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_map]

/-- **The cosupport of the `ℰ`-marked ideal**: the points of `N` on all members of `S` (`e ≥ 1`, closed members). -/
theorem cosupp_excMarked {N : Set M} (hN : ∀ x ∈ N, ∃ k, RegularAtDim (n := n) N x k) (E : List (Set M))
    {S : List (Set M)} (hS : ∀ H ∈ S, IsClosed H) {e : ℕ} (he : 1 ≤ e) :
    (excMarked n N E S e).cosupp = N ∩ {x | ∀ H ∈ S, x ∈ H} := by
  ext x
  show x ∈ cosupport n N (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) (S.getD i ∅)) e) S.length) e ↔ _
  rw [CoefficientIdeal.mem_cosupport_finSumIdeal (fun i _ _ _ hg => holomorphicAt_of_mem_idealPow hg)]
  have hpow : ∀ i < S.length, x ∈ cosupport n N (idealPow (vanishingIdeal (n := n) (S.getD i ∅)) e) e ↔
      x ∈ N ∧ x ∈ S.getD i ∅ := fun i hi => by
    have h := MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along hN
      (SmoothCentreLocus.holomorphicAt_of_mem_vanishingIdeal (Z := S.getD i ∅)) he 1
    rw [one_mul] at h
    rw [h, SmoothCentreLocus.cosupport_vanishingIdeal_one]
    · exact Iff.rfl
    · rw [List.getD_eq_getElem _ _ hi]
      exact hS _ (List.getElem_mem hi)
  constructor
  · rintro ⟨hxN, hx⟩
    refine ⟨hxN, fun H hH => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hH
    have h := ((hpow i hi).mp (hx i hi)).2
    rwa [List.getD_eq_getElem _ _ hi] at h
  · rintro ⟨hxN, hx⟩
    refine ⟨hxN, fun i hi => (hpow i hi).mpr ⟨hxN, ?_⟩⟩
    rw [List.getD_eq_getElem _ _ hi]
    exact hx _ (List.getElem_mem hi)

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **The total transform of the `ℰ`-term** along a blowup `π` along `C` contained in all members of `S`:
`π^*(Σ_{H ∈ S} 𝓘_H^e) = (π^*𝓘_C)^e · Σ_{H ∈ S} 𝓘_{H'}^e`. -/
theorem pullback_exceptionalTermBM {C : Set M} {π : M' → M} (hπ : IsBlowupAlong n C π) {S : List (Set M)}
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) (hCS : ∀ H ∈ S, C ⊆ H) (hSne : S ≠ []) (e : ℕ) :
    GermIdeal.pullback (m := n) π (exceptionalTermBM (n := n) S e) =
      (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) e).mul
        (exceptionalTermBM (n := n) (S.map (geoStrictTransform π C)) e) := by
  have hm : 1 ≤ S.length := List.length_pos_iff.mpr hSne
  have hmem : ∀ i < S.length, S.getD i ∅ ∈ S := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have h𝔩 : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsCoherent :=
    isCoherent_pullback hπ.contMDiff hIC
  have hJ : ∀ i < S.length, (idealPow (vanishingIdeal (n := n) (S.getD i ∅)) e).IsCoherent := fun i hi =>
    isCoherent_idealPow (VanishingIdealCoherent.isCoherent_vanishingIdeal (hS _ (hmem i hi))) e
  have hS' : ∀ i < S.length, IsClosedSubmanifold n (geoStrictTransform π C (S.getD i ∅)) := fun i hi =>
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ (hS _ (hmem i hi))
      (hCS _ (hmem i hi))
  have hJ' : ∀ i < (S.map (geoStrictTransform π C)).length,
      (idealPow (vanishingIdeal (n := n) ((S.map (geoStrictTransform π C)).getD i ∅)) e).IsCoherent := fun i hi => by
    rw [List.length_map] at hi
    rw [getD_map_empty _ hi]
    exact isCoherent_idealPow (VanishingIdealCoherent.isCoherent_vanishingIdeal (hS' i hi)) e
  show GermIdeal.pullback (m := n) π (finSumIdeal _ S.length) =
    (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) e).mul
      (finSumIdeal _ (S.map (geoStrictTransform π C)).length)
  rw [HomogenizedIdealAlongTower.pullback_finSumIdeal_of_lt hπ.contMDiff hm hJ,
    HomogenizedIdealAlongTower.mul_finSumIdeal (isCoherent_idealPow h𝔩 e) (by simpa using hm) hJ', List.length_map]
  refine CoefficientIdeal.finSumIdeal_congr fun i hi => ?_
  have hH := hS _ (hmem i hi)
  rw [getD_map_empty _ hi, BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hH) e,
    BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul hπ hH (hCS _ (hmem i hi)),
    BlowupControlledTransform.idealPow_mul (BlowupExceptionalDivisor.isCoherent_ideal _)
      (VanishingIdealCoherent.isCoherent_vanishingIdeal (hS' i hi)) e]
  rfl

end OneSpace

/-! ### Along towers -/

section Tower

variable {X : CMfd.{u} n}

/-- **The `ℰ`-marked ideal along its multiple test blow-ups**: the transform is restricted-equivalent to the `ℰ`-marked
ideal of the strict transforms of the members (which stay closed submanifolds), on the strict transform of `N`. -/
theorem geoTransformAlong_excMarked {N : Set X} {E S : List (Set X)} {e : ℕ} (hN : IsClosedSubmanifold n N)
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) (hSne : S ≠ []) (he : 1 ≤ e) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower (excMarked n N E S e) T →
      RestrictEquiv (geoTransformAlong (excMarked n N E S e) T)
        (excMarked n (strictAlong T N) (geoTransformAlong (excMarked n N E S e) T).E (S.map (strictAlong T)) e) ∧
      ∀ H ∈ S.map (strictAlong T), IsClosedSubmanifold n H
  | _, .refl, _ => by
      have hS0 : S.map (strictAlong (BlowupTower.refl : BlowupTower X X)) = S := List.map_id S
      rw [hS0]
      exact ⟨RestrictEquiv.refl (HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hS e), hS⟩
  | _, .step T C π hπ, hT => by
      obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
      obtain ⟨ihE, ihS⟩ := geoTransformAlong_excMarked hN hS hSne he T hTT
      have hcoh₀ : (excMarked n N E S e).ideal.IsCoherent :=
        HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hS e
      obtain ⟨hNT, hcT⟩ := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hcoh₀
        T hTT
      set 𝔫 := excMarked n (strictAlong T N) (geoTransformAlong (excMarked n N E S e) T).E (S.map (strictAlong T)) e
        with h𝔫
      have hNT' : IsClosedSubmanifold n 𝔫.N := by
        have h := hNT
        rw [N_geoTransformAlong] at h
        exact h
      have hcoh𝔫 : 𝔫.ideal.IsCoherent := HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM ihS e
      have hstep := ihE.geoTransform_eq hNT.1 hcT hcoh𝔫 hπ.contMDiff (C := C)
      have hC𝔫 : 𝔫.IsAdmissibleCentre C := ihE.isAdmissibleCentre_iff.mp hC
      have hcos : 𝔫.cosupp = strictAlong T N ∩ {x | ∀ H ∈ S.map (strictAlong T), x ∈ H} :=
        cosupp_excMarked hNT'.2 _ (fun H hH => (ihS H hH).1) he
      have hCS : ∀ H ∈ S.map (strictAlong T), C ⊆ H := fun H hH x hx => by
        have h := hC𝔫.2.1 hx
        rw [hcos] at h
        exact h.2 H hH
      have hSne' : S.map (strictAlong T) ≠ [] := by simpa using hSne
      have heq := pullback_exceptionalTermBM hπ ihS hCS hSne' e
      have hS'' : ∀ H ∈ S.map (strictAlong (.step T C π hπ)), IsClosedSubmanifold n H := by
        intro H hH
        rw [List.mem_map] at hH
        obtain ⟨H₀, hH₀, rfl⟩ := hH
        exact BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ
          (ihS _ (List.mem_map_of_mem hH₀)) (hCS _ (List.mem_map_of_mem hH₀))
      have hcoh' : (exceptionalTermBM (n := n) ((S.map (strictAlong T)).map (geoStrictTransform π C)) e).IsCoherent :=
        HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM (by rwa [List.map_map]) e
      have hR := restrictEquiv_geoTransform_of_pullback_eq hNT' hcoh𝔫 hC𝔫 hπ hcoh' heq
      refine ⟨?_, hS''⟩
      rw [geoTransformAlong_step, hstep]
      have hmap : (S.map (strictAlong T)).map (geoStrictTransform π C) = S.map (strictAlong (.step T C π hπ)) := by
        rw [List.map_map]
        rfl
      rw [hmap] at hR
      exact hR

/-- **The cosupport of the `ℰ`-marked ideal along its multiple test blow-ups**: `N_T ∩ H_{S_T}`. -/
theorem cosupp_geoTransformAlong_excMarked {N : Set X} {E S : List (Set X)} {e : ℕ} (hN : IsClosedSubmanifold n N)
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) (hSne : S ≠ []) (he : 1 ≤ e) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (excMarked n N E S e) T) :
    (geoTransformAlong (excMarked n N E S e) T).cosupp =
      strictAlong T N ∩ {x | ∀ H ∈ S, x ∈ strictAlong T H} := by
  obtain ⟨hE, hS'⟩ := geoTransformAlong_excMarked hN hS hSne he T hT
  have hcoh₀ : (excMarked n N E S e).ideal.IsCoherent :=
    HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hS e
  obtain ⟨hNT, -⟩ := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hcoh₀ T hT
  rw [N_geoTransformAlong] at hNT
  have hNT' : IsClosedSubmanifold n (strictAlong T N) := hNT
  rw [hE.cosupp_eq, cosupp_excMarked hNT'.2 _ (fun H hH => (hS' H hH).1) he]
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, List.mem_map, forall_exists_index, and_imp]
  exact and_congr Iff.rfl ⟨fun h H hH => h _ H hH rfl, fun h _ H hH hH' => hH' ▸ h H hH⟩

end Tower

/-! ### Restriction to an open set -/

section Open

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **On an open set the `ℰ`-term restricts to the `ℰ`-term of the traces** (closed submanifolds, `S ≠ []`). -/
theorem pullback_val_exceptionalTermBM (W : Opens M) {S : List (Set M)} (hS : ∀ H ∈ S, IsClosedSubmanifold n H)
    (hSne : S ≠ []) (e : ℕ) :
    GermIdeal.pullback (m := n) (Subtype.val : W → M) (exceptionalTermBM (n := n) S e) =
      exceptionalTermBM (n := n) (S.map ((Subtype.val : W → M) ⁻¹' ·)) e := by
  have hm : 1 ≤ S.length := List.length_pos_iff.mpr hSne
  have hmem : ∀ i < S.length, S.getD i ∅ ∈ S := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hJ : ∀ i < S.length, (idealPow (vanishingIdeal (n := n) (S.getD i ∅)) e).IsCoherent := fun i hi =>
    isCoherent_idealPow (VanishingIdealCoherent.isCoherent_vanishingIdeal (hS _ (hmem i hi))) e
  show GermIdeal.pullback (m := n) (Subtype.val : W → M) (finSumIdeal _ S.length) = finSumIdeal _ (S.map _).length
  rw [HomogenizedIdealAlongTower.pullback_finSumIdeal_of_lt contMDiff_subtype_val hm hJ, List.length_map]
  refine CoefficientIdeal.finSumIdeal_congr fun i hi => ?_
  have hH := hS _ (hmem i hi)
  rw [getD_map_empty _ hi, BlowupExceptionalDivisor.pullback_idealPow contMDiff_subtype_val
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hH) e]
  congr 1
  have h := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) W (id : W → W) (S.getD i ∅)
  rw [BlowupControlledTransform.pullback_id (VanishingIdealCoherent.isCoherent_vanishingIdeal
    (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hH W))] at h
  exact h.symm

end Open

end

end Hironaka.HironakaG11InvBMExceptionalTerm
