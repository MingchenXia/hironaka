/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MaximalContactAlongTower
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Blowup.ExceptionalLocus
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.LocalGiraudTransformAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.NormalCrossingsInvariance
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.TangentDirectionAlong
import Hironaka.MarkedIdeal.TransformOffCentre
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1ba inside a submanifold at a later stage: the centre has normal crossings with the divisor

Source: Włodarczyk 2009 (`wlodarczyk09-analytic-resolution`) Step 1ba (printed p. 57): "the irreducible components
of the centers of blow-ups were either contained in the strict transforms or disjoint from them. Therefore `E_r`
will be transversal to all the codimension 1 components" -- stated there without proof. In the route of
`hironaka.tex` the codimension-one part along `N_T` of the cosupport is, near each of its points, the strict
transform of the hypersurface of maximal contact `N ∩ V(u) ∩ U` (`MaximalContactAlongTower.exists_contact_along` and
`CodimOneSupportAlong`), and the exceptional divisors are transverse to that strict transform
(`MemberInterTowerAlong`, over `U`).

* `isCoordinateFamilyAt_congr`, `isTransverse_of_forall_eventually`,
  `hasNormalCrossings_of_forall_eventually`: adapted coordinates, transversality and normal crossings
  are local -- a set agreeing near each of its points with a set having them has them.
* `isTransverse_inter_of_preimage_val`: transversality on an open subset `O` gives transversality of
  `W ∩ O` in the ambient manifold.
* `isTransverse_drop_E_inter_preimage`: for a well-formed `𝔪`, an open `U` and `A` with `A ∩ U` a closed submanifold
  of `U`, if every admissible centre `C` of every multiple test blow-up `T` satisfies `C ∩ T⁻¹ U ⊆ A_T`
  (`centre_subset_strictAlong_along`), then the exceptional members of `E_T` are transverse to `A_T ∩ T⁻¹ U`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CodimOneAdmissibleAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.NormalCrossingsInvariance Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.HomogenizedGlueingTower Hironaka.MemberInterTowerAlong Hironaka.MarkedIdealRestrictOpen Hironaka.CodimOneSupportAlong Hironaka.HomogenizedIdealAlong Hironaka.MarkedIdealBiholomorphism

noncomputable section

variable {n : ℕ}

/-! ### Normal crossings and transversality are local -/

section Local

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Adapted coordinates only depend on the germs of the family**: if near `x` every `A' i` agrees
with `A i`, adapted coordinates for `A` at `x` are adapted coordinates for `A'`. -/
theorem isCoordinateFamilyAt_congr {ι : Type*} {A A' : ι → Set M} {S : ι → Finset (Fin n)} {x : M}
    (hAA' : ∀ᶠ y in 𝓝 x, ∀ i, y ∈ A' i ↔ y ∈ A i) (hA : IsCoordinateFamilyAt n A S x) :
    IsCoordinateFamilyAt n A' S x := by
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp hAA'
  exact isCoordinateFamilyAt_of_preimage (g := id) contMDiff_id
    (by rw [exceptionalLocus_id]; exact notMem_empty x) hO hxO (fun i u hu => hOsub hu i) hA

/-- **Transversality is local**: if near each of its points `R` agrees with a set `W` transverse to
`E`, then `R` is transverse to `E`. -/
theorem isTransverse_of_forall_eventually {R : Set M} {E : List (Set M)}
    (h : ∀ x ∈ R, ∃ W : Set M, x ∈ W ∧ (∀ᶠ y in 𝓝 x, y ∈ R ↔ y ∈ W) ∧ IsTransverse n W E) :
    IsTransverse n R E := by
  intro x hx
  obtain ⟨W, hxW, hRW, hW⟩ := h x hx
  obtain ⟨S₀, S, hc, hS⟩ := hW x hxW
  refine ⟨S₀, S, isCoordinateFamilyAt_congr ?_ hc, hS⟩
  filter_upwards [hRW] with y hy
  rintro (_ | i)
  · exact hy
  · exact Iff.rfl

/-- **Normal crossings are local.** -/
theorem hasNormalCrossings_of_forall_eventually {R : Set M} {E : List (Set M)}
    (h : ∀ x ∈ R, ∃ W : Set M, x ∈ W ∧ (∀ᶠ y in 𝓝 x, y ∈ R ↔ y ∈ W) ∧ HasNormalCrossings n W E) :
    HasNormalCrossings n R E := by
  intro x hx
  obtain ⟨W, hxW, hRW, hW⟩ := h x hx
  obtain ⟨S₀, S, hc, hS⟩ := hW x hxW
  refine ⟨S₀, S, isCoordinateFamilyAt_congr ?_ hc, hS⟩
  filter_upwards [hRW] with y hy
  rintro (_ | i)
  · exact hy
  · exact Iff.rfl

/-- **Transversality on an open subset gives transversality in the ambient manifold**: if the trace of
`W` on the open set `O` is transverse (in `O`) to the traces of the members of `E`, then `W ∩ O` is
transverse to `E`. -/
theorem isTransverse_inter_of_preimage_val (O : Opens M) {W : Set M} {E : List (Set M)}
    (h : IsTransverse n ((↑) ⁻¹' W : Set O) (E.map ((↑) ⁻¹' · : Set M → Set O))) :
    IsTransverse n (W ∩ O) E := by
  intro z hz
  set p : O := ⟨z, hz.2⟩
  obtain ⟨S₀, S', hS', hcard⟩ := h p hz.1
  set c : Fin E.length → Fin (E.map ((↑) ⁻¹' · : Set M → Set O)).length :=
    Fin.cast (List.length_map _).symm with hc
  have hcc : ∀ i, Fin.cast (List.length_map _) (c i) = i := fun i => by simp [hc]
  have h1 : IsCoordinateFamilyAt n
      (fun o : Option (Fin E.length) => ((↑) ⁻¹' (o.elim W fun i => E.get i) : Set O))
      (fun o => o.elim S₀ fun i => S' (c i)) p := by
    refine IsCoordinateFamilyAt.reindex hS' (Option.map c) ?_ ?_
    · rintro (_ | i)
      · rfl
      · show _ = (E.map ((↑) ⁻¹' · : Set M → Set O)).get (c i)
        rw [get_map_preimage E (c i), hcc i]
        rfl
    · rintro (_ | i) <;> rfl
  have h2 := (isCoordinateFamilyAt_preimage_val_iff (U := O)).mp h1
  refine ⟨S₀, fun i => S' (c i), isCoordinateFamilyAt_congr ?_ h2, fun i hi => ?_⟩
  · filter_upwards [O.isOpen.mem_nhds hz.2] with y hyO
    rintro (_ | i)
    · exact ⟨fun h => h.1, fun h => ⟨h, hyO⟩⟩
    · exact Iff.rfl
  · refine hcard (c i) ?_
    rw [get_map_preimage E (c i), hcc i]
    exact hi

end Local

/-! ### The exceptional members over an open set -/

section Tower

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)

/-- **The exceptional members are transverse to the strict transform of a submanifold containing the
centres over an open set.**  Let `𝔪` be well formed, `U` open and `A` a set whose trace on `U` is a
closed submanifold of `U`, and assume that every admissible centre `C` of every multiple test blow-up
`T'` of `𝔪` satisfies `C ∩ T'⁻¹ U ⊆ A_{T'}` (the shape of
`MaximalContactAlongTower.centre_subset_strictAlong_along`, `A = N ∩ V(u) ∩ U`).  Then for every
multiple test blow-up `T`, the members of `E_T` after the original ones are transverse to
`A_T ∩ T⁻¹ U`. -/
theorem isTransverse_drop_E_inter_preimage (h𝔪 : 𝔪.IsWellFormed) (U : Opens X) {A : Set X}
    (hA : IsClosedSubmanifold n ((↑) ⁻¹' A : Set U))
    (h : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y), IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).IsAdmissibleCentre C → C ∩ T.proj ⁻¹' (U : Set X) ⊆ strictAlong T A)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    IsTransverse n (strictAlong T A ∩ T.proj ⁻¹' (U : Set X))
      ((geoTransformAlong 𝔪 T).E.drop 𝔪.E.length) := by
  have hN := h𝔪.isClosedSubmanifold_N
  have h𝔞 := h𝔪.isCoherent
  have hTU := isGeoTestTower_restrict U hN h𝔞 T hT
  have hcent := centresIn_restrict_of_forall 𝔪 U h T hT
  have hD := (isTransverse_drop_E_geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
    (IsWellFormed.pullback_val h𝔪 U) hA (restrict U T) hTU hcent).2.2
  rw [strictAlong_restrict U T A, geoTransformAlong_restrict U hN h𝔞 T hT] at hD
  have hlen : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).E.length = 𝔪.E.length := by
    simp [MarkedIdealBiholomorphism.MarkedIdeal.pullback]
  have hE : (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong 𝔪 T)).E.drop
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).E.length =
      ((geoTransformAlong 𝔪 T).E.drop 𝔪.E.length).map ((↑) ⁻¹' · : Set Y → Set (openPreimage T U)) := by
    rw [hlen]
    simp [MarkedIdealBiholomorphism.MarkedIdeal.pullback, List.map_drop]
  rw [hE] at hD
  exact isTransverse_inter_of_preimage_val (openPreimage T U) hD

end Tower

/-! ### The codimension-one part along `N_T` at every stage -/

section Stage

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)

open Hironaka.TangentDirectionAlong Hironaka.GiraudAlong Hironaka.TransformOffCentre Hironaka.MaximalContactAlongTower Hironaka.LocalGiraudTransformAlong Hironaka.GermIdealOrder

/-- **At every stage of Step 1 inside `N` the codimension-one part along `N_T` of the cosupport is
transverse to the exceptional divisors.**  Let `(M, N, E, 𝔞, d)` be well formed, of maximal order along
`N`, `d ≥ 1`, and `T` a multiple test blow-up.  Then the codimension-one part along `N_T` of the
cosupport of the transform is transverse to the members of `E_T` after the original ones.  (Near each
of its points it is `N_T ∩ V(w)` for the tangent direction `w` of the transform
(`CodimOneSupportAlong`), which is the strict transform of a hypersurface of maximal contact
`N ∩ V(u) ∩ U` (`MaximalContactAlongTower.exists_contact_along`), to which the exceptional members are
transverse (`isTransverse_drop_E_inter_preimage`).)  This is Włodarczyk's sentence in Step 1ba
(2009, p. 57). -/
theorem isTransverse_codimOnePartAlong_drop_E (h𝔪 : 𝔪.IsWellFormed) (hμ : 1 ≤ 𝔪.d)
    (hmax : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) :
    IsTransverse n (codimOnePartAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal
      (geoTransformAlong 𝔪 T).d) ((geoTransformAlong 𝔪 T).E.drop 𝔪.E.length) := by
  have hN := h𝔪.isClosedSubmanifold_N
  have h𝔞 := h𝔪.isCoherent
  obtain ⟨hNT, h𝔞T⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  have hhol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  rw [d_geoTransformAlong]
  refine isTransverse_of_forall_eventually fun x hx => ?_
  have hxS : x ∈ cosupport n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal 𝔪.d :=
    codimOnePartAlong_subset hx
  have hx0 : T.proj x ∈ 𝔪.cosupp := cosupp_geoTransformAlong_subset 𝔪 hN h𝔞 T hT (by
    show x ∈ cosupport n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal
      (geoTransformAlong 𝔪 T).d
    rw [d_geoTransformAlong]; exact hxS)
  obtain ⟨U, u, hxU, hu⟩ := exists_isTangentDirectionAlong h𝔞 hN hμ hx0
    fun h => hmax (T.proj x) ⟨hx0.1, h⟩
  obtain ⟨O, w, hxO, hO, hOU, hw, hwD, hw1, hwA⟩ :=
    exists_contact_along 𝔪 hN h𝔞 hμ hu T hT x hxS.1 hxU
  have hR := eventually_mem_codimOnePartAlong_iff_eq_zero_of_isInSpanOnAt h𝔞T hNT hμ hO hw hwD hw1
    hxO hx
  set U' : Opens X := ⟨U, hu.isOpen⟩ with hU'
  set A : Set X := 𝔪.N ∩ {y | u y = 0} ∩ U with hA
  have hAN : A ⊆ 𝔪.N := fun _ hy => hy.1.1
  have hA' : IsClosedSubmanifold n ((↑) ⁻¹' A : Set U') :=
    isClosedSubmanifold_preimage_val_inter_zeroSet hN U'
      (fun y hy => holomorphicAt_of_mem_iterDerivIdealAlong hhol _ y u (hu.mem y hy))
      (fun y hy _ h0 => hu.multiplicity_one y hy h0)
  have htr := isTransverse_drop_E_inter_preimage 𝔪 h𝔪 U' hA'
    (fun T' C hT' hC => centre_subset_strictAlong_along 𝔪 hN h𝔞 hμ hu T' hT' hC) T hT
  have hxw : x ∈ (geoTransformAlong 𝔪 T).N ∧ w x = 0 := hR.self_of_nhds.mp hx
  refine ⟨strictAlong T A ∩ T.proj ⁻¹' (U' : Set X),
    ⟨(hwA x hxO hxw.1).mp hxw.2, hOU hxO⟩, ?_, htr⟩
  filter_upwards [hR, hO.mem_nhds hxO] with y h1 hyO
  rw [h1]
  constructor
  · rintro ⟨hyN, hy0⟩
    exact ⟨(hwA y hyO hyN).mp hy0, hOU hyO⟩
  · rintro ⟨hyA, -⟩
    have hyN : y ∈ (geoTransformAlong 𝔪 T).N := strictAlong_subset_N 𝔪 hAN T hyA
    exact ⟨hyN, (hwA y hyO hyN).mpr hyA⟩

end Stage

end

end Hironaka.CodimOneAdmissibleAlong
