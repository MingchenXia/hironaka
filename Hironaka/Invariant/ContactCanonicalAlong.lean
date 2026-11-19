import Hironaka.Invariant.ContactEquivalenceAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.MarkedIdeal.TransformOffCentre

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Canonicity of the coefficient ideals along `N` and of their restrictions, along multiple test blow-ups

Hironaka phase H3 (TN23-ENVELOPES), claimed on I-0981 C-0069 (continued C-0070): the H3 half of properties (4)--(7) of
`hir:centre-function` for Step 1 of `hir:maximal-order-step` inside `N` ("(4)--(7) hold since every ingredient (`𝓗`, `𝓒`,
`s`, tangent directions, restriction to `S` and to `V(w)`) commutes with restriction to open sets and with
biholomorphisms, and is unchanged by empty steps"); TN3's `CodimOnePartCanonical` is the H2 half (the codimension-one
part and the boundary count).  Blueprint `mc:coefficient-representatives-along`, `mc:coefficient-representatives-tower`,
`mc:restriction-operations-along`, `mc:coefficient-transported-tower`, `mc:coefficient-restricted-tower`,
`mc:empty-blowup-inverse`, `mc:coefficient-empty-step`, `mc:tangent-direction-canonical-along`
(`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005 (arXiv `hiron.tex`), the unlabelled lemma "Commutativity of
the resolution procedure in Step 1 with étale morphisms" in the proof of Proposition `pr: resol`: its items (2)--(3),
`φ^*(J̄_{i|H^s_α}) = J̄'_{j|(H')^s_α}` and `J̄'_{|V(u)} = φ^*(J̄_{|V(u)})`, and its item (1), along which blow-ups whose
centres miss the image pull back to isomorphisms; with Proposition `pr: funct` (multiple test blow-ups pull back along
smooth morphisms) and `pr: resol` (4).  Here étale maps are open embeddings and biholomorphisms, and the induced
isomorphisms are steps with empty centre.

Notation: `𝔪_T = geoTransformAlong 𝔪 T`; `A_T = strictAlong T A`; `S_A(𝔪_T) = withN (coeffMarkedAlong 𝔪_T) A_T`, the
coefficient ideal along `N_T` restricted to the strict transform of `A ⊆ N` (`A = N ∩ H_S` in Step 1a,
`A = N ∩ V(u)` in Step 1b).  Standing hypotheses on `𝔪`: `N` a closed submanifold, coherent ideal, `d ≥ 1`, `T` a multiple
test blow-up.

## (K4) Representatives

* `restrictLe_iterDerivIdealAlong`, `restrictLe_coeffMarkedAlong`: `𝔞|_N ⊆ 𝔟|_N` gives `𝓓_N^i(𝔞)|_N ⊆ 𝓓_N^i(𝔟)|_N` and
  `𝓒_N(𝔞)|_N ⊆ 𝓒_N(𝔟)|_N`; `restrictEquiv_coeffMarkedAlong`, `restrictEquiv_withN`, `restrictEquiv_restrictedCoeff`:
  `𝔪 ≃ 𝔫` (`RestrictEquiv`) gives `𝓒_N(𝔪) ≃ 𝓒_N(𝔫)` and `S_A(𝔪) ≃ S_A(𝔫)` for `A ⊆ N`.
* `restrictEquiv_coeffMarkedAlong_geoTransformAlong`, `restrictEquiv_restrictedCoeff_geoTransformAlong`: the same at every
  stage of every tower (from the first blowup on the transforms are equal).

## Restriction, dropping members and pullbacks

* `pullback_withN`, `pullback_dropE`, `pullback_id`: `φ^*(𝔟|_S) = (φ^*𝔟)|_{φ⁻¹S}`, dropping members commutes with
  pullback, `id^*𝔪 = 𝔪`; `pullback_restrictedCoeff`, `pullback_val_restrictedCoeff`: `S_A` commutes with biholomorphisms
  and with restriction to open sets; `restrictEquiv_dropE`, `geoTransform_dropE`: dropping the first `k ≤ #E` members
  commutes with restricted equivalence and with the transform.

## (K1) Transported towers (property (6))

* `geoTransformAlong_transport`: `(Φ^*𝔪)_{Φ^*T} = Φ_T^*(𝔪_T)` (`Φ_T` the last-stage biholomorphism of
  `MarkedIdealTowerTransport.transport`); `coeffMarkedAlong_geoTransformAlong_transport`:
  `𝓒((Φ^*𝔪)_{Φ^*T}) = Φ_T^*𝓒(𝔪_T)`; **`restrictedCoeff_geoTransformAlong_transport`**: `S_{Φ⁻¹A}((Φ^*𝔪)_{Φ^*T}) =
  Φ_T^* S_A(𝔪_T)`; `restricted_geoTransformAlong_transport` (without `𝓒`);
  `cosupp_restrictedCoeff_geoTransformAlong_transport` (cosupports: `Φ_T⁻¹`).

## (K2) Restricted towers (property (5))

* `coeffMarkedAlong_geoTransformAlong_restrict`, **`restrictedCoeff_geoTransformAlong_restrict`**:
  `S_{A ∩ U}((𝔪|_U)_{T|_U}) = S_A(𝔪_T)|_{T⁻¹U}`; `restricted_geoTransformAlong_restrict`,
  `cosupp_restrictedCoeff_geoTransformAlong_restrict`.

## (K3) Steps with empty centre (property (4))

* `exists_isLocalInverseAt_of_isBlowupAlong_empty`: a blowup along `∅` is a local biholomorphism at every point;
  `geoStrictTransform_empty`: the strict transform of a closed set is its preimage;
  `restrictLe_geoTransform_empty_le_pullback`, `restrictLe_pullback_le_geoTransform`: along `∅` the transform is the
  pullback on `N'` up to restricted equivalence.
* `restrictEquiv_coeffMarkedAlong_geoTransform_empty`: `𝓒_{N'}(𝔪') ≃ 𝓒_N(𝔪)'`;
  **`restrictEquiv_restrictedCoeff_geoTransform_empty`**: `𝓒_{N'}(𝔪')|_{A'} ≃ (𝓒_N(𝔪)|_A)'` (restricting at the new stage
  or transforming the old restriction); `cosupp_restrictedCoeff_geoTransform_empty` (`π⁻¹` of the cosupport);
  `restrictEquiv_restrictedCoeff_geoTransformAlong_empty`: the form along a tower, `S_A(𝔪_{T·π}) ≃ S_A(𝔪_T)'`.

## (K5) Tangent directions

* `isTangentDirectionAlong_geoTransformAlong_transport`, `isTangentDirectionAlong_geoTransformAlong_restrict`: a tangent
  direction `u` of `(𝔪_T|_{N_T}, μ)` on `V` gives the tangent directions `u ∘ Φ_T` on `Φ_T⁻¹V` and `u|_{T⁻¹U}` along the
  transported and restricted towers; `N_inter_zeroSet_geoTransformAlong_transport`,
  `N_inter_zeroSet_geoTransformAlong_restrict`: the hypersurfaces `N_T ∩ V(u)` correspond;
  `isTangentDirectionAlong_geoTransform_empty`: across a step with empty centre, `u ∘ π` (on `π⁻¹V`, with
  `N' ∩ V(u ∘ π) = π⁻¹(N ∩ V(u))`); `iterDerivIdealAlong_le` (monotonicity).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ContactCanonicalAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder IdealWeightPowers
  RestrictedIdealWeight DerivativeIdealAlong DerivativeIdealAlongEtale DerivativeIdealAlongTransform
  HomogenizedGlueing HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdeal CoefficientIdealRestriction
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms MarkedIdealBiholomorphism MarkedIdealTowerTransport MarkedIdealRestrictOpen
  BlowupStrictSubmanifold TangentDirectionAlong
open HomogenizedGlueingTower (strictAlong strictAlong_step strictAlong_restrict strictAlong_transport
  N_geoTransformAlong)

noncomputable section

variable {n : ℕ}

/-! ### (K4) Representatives -/

section Representatives

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Germs of the coefficient ideal along `N` are holomorphic. -/
theorem holomorphicAt_of_mem_coeffMarkedAlong (𝔪 : MarkedIdeal n M) {x : M} {g : M → ℂ}
    (hg : (coeffMarkedAlong 𝔪).ideal.mem x g) : HolomorphicAt n g x :=
  hg.1

/-- **Derivatives along `W` respect restricted inclusions on `W`**, iterated: `𝔞|_W ⊆ 𝔟|_W` gives
`𝓓_W^i(𝔞)|_W ⊆ 𝓓_W^i(𝔟)|_W`. -/
theorem restrictLe_iterDerivIdealAlong {W : Set M} {𝔞 𝔟 : GermIdeal n M}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x)
    (h : RestrictLe W 𝔞 𝔟) : ∀ i, RestrictLe W (iterDerivIdealAlong W 𝔞 i) (iterDerivIdealAlong W 𝔟 i)
  | 0 => h
  | i + 1 => restrictLe_derivIdealAlong (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 i)
      (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔟 i) (restrictLe_iterDerivIdealAlong h𝔞 h𝔟 h i)

/-- **The coefficient ideal along `N` respects restricted inclusions on `N`**: for two marked ideals with the same `N` and
the same mark, `𝔞|_N ⊆ 𝔟|_N` gives `𝓒_N(𝔞)|_N ⊆ 𝓒_N(𝔟)|_N`. -/
theorem restrictLe_coeffMarkedAlong {𝔪 𝔫 : MarkedIdeal n M} (hN : 𝔪.N = 𝔫.N) (hd : 𝔪.d = 𝔫.d)
    (h𝔪 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (h𝔫 : ∀ x g, 𝔫.ideal.mem x g → HolomorphicAt n g x)
    (h : RestrictLe 𝔪.N 𝔪.ideal 𝔫.ideal) :
    RestrictLe 𝔪.N (coeffMarkedAlong 𝔪).ideal (coeffMarkedAlong 𝔫).ideal := by
  show RestrictLe 𝔪.N (finSumIdeal (fun i => idealPow (iterDerivIdealAlong 𝔪.N 𝔪.ideal i)
      (sumExp (fun j => 𝔪.d - j) 𝔪.d i)) 𝔪.d)
    (finSumIdeal (fun i => idealPow (iterDerivIdealAlong 𝔫.N 𝔫.ideal i) (sumExp (fun j => 𝔫.d - j) 𝔫.d i)) 𝔫.d)
  rw [← hN, ← hd]
  refine restrictLe_finSumIdeal (fun i _ _ _ hg => holomorphicAt_of_mem_idealPow hg) fun i _ => ?_
  exact restrictLe_idealPow (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔫 i)
    (restrictLe_iterDerivIdealAlong h𝔪 h𝔫 h i) _

/-- **Restricted-equivalent marked ideals have restricted-equivalent coefficient ideals along `N`**. -/
theorem restrictEquiv_coeffMarkedAlong {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫)
    (h𝔪 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (h𝔫 : ∀ x g, 𝔫.ideal.mem x g → HolomorphicAt n g x) :
    RestrictEquiv (coeffMarkedAlong 𝔪) (coeffMarkedAlong 𝔫) where
  N_eq := h.N_eq
  E_eq := h.E_eq
  d_eq := by
    show ((Finset.range 𝔪.d).prod fun j => 𝔪.d - j) = (Finset.range 𝔫.d).prod fun j => 𝔫.d - j
    rw [h.d_eq]
  le := restrictLe_coeffMarkedAlong h.N_eq h.d_eq h𝔪 h𝔫 h.le
  ge := by
    have := restrictLe_coeffMarkedAlong h.N_eq.symm h.d_eq.symm h𝔫 h𝔪 (h.N_eq ▸ h.ge)
    exact h.N_eq ▸ this

/-- **Restricted equivalence restricts to subsets of `N`**: `𝔪 ≃ 𝔫` gives `𝔪|_A ≃ 𝔫|_A` for `A ⊆ N`. -/
theorem restrictEquiv_withN {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫) {A : Set M} (hA : A ⊆ 𝔪.N) :
    RestrictEquiv (withN 𝔪 A) (withN 𝔫 A) :=
  ⟨rfl, h.E_eq, h.d_eq, restrictLe_mono hA h.le, restrictLe_mono hA h.ge⟩

/-- **(K4) The restricted coefficient ideals of restricted-equivalent marked ideals are restricted-equivalent**:
`𝓒_N(𝔪)|_A ≃ 𝓒_N(𝔫)|_A` for `A ⊆ N`. -/
theorem restrictEquiv_restrictedCoeff {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫)
    (h𝔪 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (h𝔫 : ∀ x g, 𝔫.ideal.mem x g → HolomorphicAt n g x)
    {A : Set M} (hA : A ⊆ 𝔪.N) :
    RestrictEquiv (withN (coeffMarkedAlong 𝔪) A) (withN (coeffMarkedAlong 𝔫) A) :=
  restrictEquiv_withN (restrictEquiv_coeffMarkedAlong h h𝔪 h𝔫) hA

end Representatives

section RepresentativesTower

variable {X : CMfd.{u} n} {𝔪 𝔫 : MarkedIdeal n X}

/-- A marked ideal whose germs are holomorphic is restricted-equivalent to itself. -/
theorem restrictEquiv_self (𝔟 : MarkedIdeal n X) (h𝔟 : ∀ x g, 𝔟.ideal.mem x g → HolomorphicAt n g x) :
    RestrictEquiv 𝔟 𝔟 :=
  ⟨rfl, rfl, rfl, restrictLe_refl h𝔟, restrictLe_refl h𝔟⟩

/-- **(K4) along every tower**: restricted-equivalent marked ideals (closed `N`, coherent ideals) have, at every stage of
every tower, restricted-equivalent coefficient ideals along `N_T` (from the first blowup on the transforms are equal). -/
theorem restrictEquiv_coeffMarkedAlong_geoTransformAlong (h : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      RestrictEquiv (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (coeffMarkedAlong (geoTransformAlong 𝔫 T))
  | _, .refl => restrictEquiv_coeffMarkedAlong h (hol_of_isCoherent h𝔪) (hol_of_isCoherent h𝔫)
  | _, .step T C π hπ => by
      rw [MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq h hN h𝔪 h𝔫 T C π hπ]
      exact restrictEquiv_self _ fun _ _ hg => hg.1

/-- **(K4) for the restricted coefficient ideals along every tower**: for `A ⊆ N`, at every stage `T`,
`𝓒_{N_T}(𝔪_T)|_{A_T} ≃ 𝓒_{N_T}(𝔫_T)|_{A_T}` (`A_T` the strict transform of `A`). -/
theorem restrictEquiv_restrictedCoeff_geoTransformAlong (h : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) {A : Set X} (hA : A ⊆ 𝔪.N) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) :
    RestrictEquiv (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A))
      (withN (coeffMarkedAlong (geoTransformAlong 𝔫 T)) (strictAlong T A)) := by
  refine restrictEquiv_withN (restrictEquiv_coeffMarkedAlong_geoTransformAlong h hN h𝔪 h𝔫 T) ?_
  show strictAlong T A ⊆ (geoTransformAlong 𝔪 T).N
  rw [N_geoTransformAlong]
  exact MemberInterTowerAlong.strictAlong_mono T hA

end RepresentativesTower

/-! ### Restrictions to sets and pullbacks -/

section Pullback

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **Restriction to a set commutes with pullback**: `φ^*(𝔟|_S) = (φ^*𝔟)|_{φ⁻¹S}`. -/
theorem pullback_withN (φ : M' → M) (𝔟 : MarkedIdeal n M) (S : Set M) :
    MarkedIdeal.pullback φ (withN 𝔟 S) = withN (MarkedIdeal.pullback φ 𝔟) (φ ⁻¹' S) :=
  rfl

/-- **Dropping members commutes with pullback**: `φ^*{𝔪 with E := E.drop k} = {φ^*𝔪 with E := (φ^*E).drop k}` (the
marked ideals of Steps 1a/1b with the old members dropped). -/
theorem pullback_dropE (φ : M' → M) (𝔪 : MarkedIdeal n M) (k : ℕ) :
    MarkedIdeal.pullback φ { 𝔪 with E := 𝔪.E.drop k } =
      { MarkedIdeal.pullback φ 𝔪 with E := (MarkedIdeal.pullback φ 𝔪).E.drop k } := by
  show (⟨φ ⁻¹' 𝔪.N, (𝔪.E.drop k).map (φ ⁻¹' ·), GermIdeal.pullback (m := n) φ 𝔪.ideal, 𝔪.d⟩ : MarkedIdeal n M') =
    ⟨φ ⁻¹' 𝔪.N, (𝔪.E.map (φ ⁻¹' ·)).drop k, GermIdeal.pullback (m := n) φ 𝔪.ideal, 𝔪.d⟩
  rw [List.map_drop]

/-- The pullback along the identity of a marked ideal with coherent ideal is the marked ideal. -/
theorem pullback_id (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent) : MarkedIdeal.pullback (id : M → M) 𝔪 = 𝔪 :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl
    (show List.map (fun s => (id : M → M) ⁻¹' s) 𝔪.E = 𝔪.E by simp) (BlowupControlledTransform.pullback_id h𝔞) rfl

/-- **The restricted coefficient ideal commutes with biholomorphisms**: `Φ^*(𝓒_N(𝔪)|_A) = 𝓒_{Φ⁻¹N}(Φ^*𝔪)|_{Φ⁻¹A}`
(`N` a closed submanifold, coherent ideal, `d ≥ 1`). -/
theorem pullback_restrictedCoeff (Φ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M) (𝔪 : MarkedIdeal n M)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔪.N) (hd : 1 ≤ 𝔪.d) (A : Set M) :
    MarkedIdeal.pullback Φ (withN (coeffMarkedAlong 𝔪) A) =
      withN (coeffMarkedAlong (MarkedIdeal.pullback Φ 𝔪)) (Φ ⁻¹' A) := by
  rw [pullback_withN, pullback_coeffMarkedAlong_of_inverse Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
    Φ.symm_apply_apply 𝔪 h𝔞 hN hd]

/-- **The restricted coefficient ideal commutes with restriction to open sets**:
`(𝓒_N(𝔪)|_A)|_U = 𝓒_{N ∩ U}(𝔪|_U)|_{A ∩ U}`. -/
theorem pullback_val_restrictedCoeff (U : Opens M) (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n 𝔪.N) (hd : 1 ≤ 𝔪.d) (A : Set M) :
    MarkedIdeal.pullback (Subtype.val : U → M) (withN (coeffMarkedAlong 𝔪) A) =
      withN (coeffMarkedAlong (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪)) ((Subtype.val : U → M) ⁻¹' A) := by
  rw [pullback_withN, pullback_val_coeffMarkedAlong U 𝔪 h𝔞 hN hd]

end Pullback

/-! ### Dropping members -/

section Drop

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **Restricted equivalence survives dropping members**: `𝔪 ≃ 𝔫` gives
`{𝔪 with E := E.drop k} ≃ {𝔫 with E := E.drop k}`. -/
theorem restrictEquiv_dropE {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫) (k : ℕ) :
    RestrictEquiv { 𝔪 with E := 𝔪.E.drop k } { 𝔫 with E := 𝔫.E.drop k } :=
  ⟨h.N_eq, by rw [h.E_eq], h.d_eq, h.le, h.ge⟩

/-- **Dropping old members commutes with the transform**: for `k ≤ #E`,
`{𝔪 with E := E.drop k}' = {𝔪' with E := E'.drop k}`. -/
theorem geoTransform_dropE (𝔪 : MarkedIdeal n M) (C : Set M) (π : M' → M) {k : ℕ} (hk : k ≤ 𝔪.E.length) :
    ({ 𝔪 with E := 𝔪.E.drop k } : MarkedIdeal n M).geoTransform C π =
      { 𝔪.geoTransform C π with E := (𝔪.geoTransform C π).E.drop k } := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
  simp only [geoTransform_E]
  rw [List.drop_append_of_le_length (by simpa using hk), List.map_drop]

end Drop

/-! ### (K1) Transported towers -/

section Transport

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {𝔪 : MarkedIdeal n X}

/-- **Transforms along transported towers** (`hir:tower-transport`, uniform form): along the transport of a multiple test
blow-up `T` of `𝔪` by a biholomorphism `Φ : X' ≅ X`, the transform of `Φ^*𝔪` is the pullback of the transform of `𝔪` by
the last-stage biholomorphism (`N` a closed submanifold, coherent ideal). -/
theorem geoTransformAlong_transport (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower =
        MarkedIdeal.pullback (transport Φ T).back (geoTransformAlong 𝔪 T)
  | _, .refl, _ => rfl
  | _, .step T C π hπ, hT => by
      obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 _ hT
      rw [geoTransformAlong_transport_step Φ h𝔞 T C π hπ]
      exact (pullback_id _ hcT).symm

/-- **(K1) The coefficient ideal along `N_T` along transported towers**: `𝓒_{N'_{T'}}((Φ^*𝔪)_{T'}) = Φ_T^*𝓒_{N_T}(𝔪_T)`. -/
theorem coeffMarkedAlong_geoTransformAlong_transport (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    coeffMarkedAlong (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower) =
      MarkedIdeal.pullback (transport Φ T).back (coeffMarkedAlong (geoTransformAlong 𝔪 T)) := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  rw [geoTransformAlong_transport Φ hN h𝔞 T hT, pullback_coeffMarkedAlong_of_inverse (transport Φ T).back.contMDiff
    (transport Φ T).back.symm.contMDiff (transport Φ T).back.apply_symm_apply (transport Φ T).back.symm_apply_apply _
    hcT hNT (by rwa [d_geoTransformAlong])]

/-- **(K1) The restricted coefficient ideals along transported towers** (property (6) for Steps 1a/1b inside `N`):
`S_{Φ⁻¹A}((Φ^*𝔪)_{T'}) = Φ_T^* S_A(𝔪_T)` for `S_A(𝔪_T) = 𝓒_{N_T}(𝔪_T)|_{A_T}`. -/
theorem restrictedCoeff_geoTransformAlong_transport (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (A : Set X) :
    withN (coeffMarkedAlong (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower))
        (strictAlong (transport Φ T).tower (Φ ⁻¹' A)) =
      MarkedIdeal.pullback (transport Φ T).back (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A)) := by
  rw [coeffMarkedAlong_geoTransformAlong_transport Φ hN h𝔞 hd T hT, strictAlong_transport Φ T A]
  rfl

/-- **(K1) without `𝓒`**: `(Φ^*𝔪)_{T'}|_{(Φ⁻¹A)_{T'}} = Φ_T^*(𝔪_T|_{A_T})`. -/
theorem restricted_geoTransformAlong_transport (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (A : Set X) :
    withN (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower)
        (strictAlong (transport Φ T).tower (Φ ⁻¹' A)) =
      MarkedIdeal.pullback (transport Φ T).back (withN (geoTransformAlong 𝔪 T) (strictAlong T A)) := by
  rw [geoTransformAlong_transport Φ hN h𝔞 T hT, strictAlong_transport Φ T A]
  rfl

/-- **(K1) Cosupports of the restricted coefficient ideals along transported towers**:
`cosupp S_{Φ⁻¹A}((Φ^*𝔪)_{T'}) = Φ_T⁻¹ cosupp S_A(𝔪_T)`. -/
theorem cosupp_restrictedCoeff_geoTransformAlong_transport (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    (A : Set X) :
    (withN (coeffMarkedAlong (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower))
        (strictAlong (transport Φ T).tower (Φ ⁻¹' A))).cosupp =
      (transport Φ T).back ⁻¹' (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A)).cosupp := by
  rw [restrictedCoeff_geoTransformAlong_transport Φ hN h𝔞 hd T hT A]
  exact MarkedIdeal.cosupp_pullback (transport Φ T).back.contMDiff (transport Φ T).back.symm.contMDiff
    (transport Φ T).back.apply_symm_apply (transport Φ T).back.symm_apply_apply _ fun _ _ hg => hg.1

end Transport

/-! ### (K2) Restricted towers -/

section Restrict

variable {X : CMfd.{u} n} (U : Opens X) {𝔪 : MarkedIdeal n X}

/-- **(K2) The coefficient ideal along `N_T` along restricted towers**:
`𝓒((𝔪|_U)_{T|_U}) = 𝓒(𝔪_T)|_{T⁻¹U}`. -/
theorem coeffMarkedAlong_geoTransformAlong_restrict (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    coeffMarkedAlong (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (coeffMarkedAlong (geoTransformAlong 𝔪 T)) := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  rw [geoTransformAlong_restrict U hN h𝔞 T hT,
    pullback_val_coeffMarkedAlong (openPreimage T U) _ hcT hNT (by rwa [d_geoTransformAlong])]

/-- **(K2) The restricted coefficient ideals along restricted towers** (property (5) for Steps 1a/1b inside `N`):
`S_{A ∩ U}((𝔪|_U)_{T|_U}) = S_A(𝔪_T)|_{T⁻¹U}`. -/
theorem restrictedCoeff_geoTransformAlong_restrict (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (A : Set X) :
    withN (coeffMarkedAlong (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)))
        (strictAlong (restrict U T) ((↑) ⁻¹' A : Set U)) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A)) := by
  rw [coeffMarkedAlong_geoTransformAlong_restrict U hN h𝔞 hd T hT, strictAlong_restrict U T A]
  rfl

/-- **(K2) without `𝓒`**: `(𝔪|_U)_{T|_U}|_{(A ∩ U)_{T|_U}} = (𝔪_T|_{A_T})|_{T⁻¹U}`. -/
theorem restricted_geoTransformAlong_restrict (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (A : Set X) :
    withN (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T))
        (strictAlong (restrict U T) ((↑) ⁻¹' A : Set U)) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (withN (geoTransformAlong 𝔪 T) (strictAlong T A)) := by
  rw [geoTransformAlong_restrict U hN h𝔞 T hT, strictAlong_restrict U T A]
  rfl

/-- **(K2) Cosupports of the restricted coefficient ideals along restricted towers**:
`cosupp S_{A ∩ U}((𝔪|_U)_{T|_U}) = T⁻¹U ∩ cosupp S_A(𝔪_T)`. -/
theorem cosupp_restrictedCoeff_geoTransformAlong_restrict (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    (A : Set X) :
    (withN (coeffMarkedAlong (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)))
        (strictAlong (restrict U T) ((↑) ⁻¹' A : Set U))).cosupp =
      ((↑) : openPreimage T U → Y) ⁻¹' (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A)).cosupp := by
  rw [restrictedCoeff_geoTransformAlong_restrict U hN h𝔞 hd T hT A]
  exact cosupp_pullback_val (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A))
    (fun _ _ hg => holomorphicAt_of_mem_coeffMarkedAlong _ hg) (openPreimage T U)

end Restrict

/-! ### (K3) Steps with empty centre -/

section EmptyStep

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {π : Z → Y}

/-- **A blowup along `∅` is a local biholomorphism at every point**: its holomorphic section over the complement of the
centre (`BlowupIsomorphismOff.exists_section_compl`) is a global inverse. -/
theorem exists_isLocalInverseAt_of_isBlowupAlong_empty (hπ : IsBlowupAlong n (∅ : Set Y) π) (z : Z) :
    ∃ ψ : Y → Z, IsLocalInverseAt n π ψ z := by
  obtain ⟨s, hs, hsπ, hsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hmem : ∀ y : Y, y ∈ (⟨(∅ : Set Y)ᶜ, hπ.1.1.isOpen_compl⟩ : Opens Y) := fun y => notMem_empty y
  set y₀ : (⟨(∅ : Set Y)ᶜ, hπ.1.1.isOpen_compl⟩ : Opens Y) := ⟨π z, hmem _⟩ with hy₀
  have hinv := isLocalInverseAt_val (n := n) (⟨(∅ : Set Y)ᶜ, hπ.1.1.isOpen_compl⟩ : Opens Y) y₀
  have hopen : ∀ q : Y, openInv (⟨(∅ : Set Y)ᶜ, hπ.1.1.isOpen_compl⟩ : Opens Y) y₀ q = ⟨q, hmem q⟩ := fun q => by
    simp [openInv]
  refine ⟨s ∘ openInv (⟨(∅ : Set Y)ᶜ, hπ.1.1.isOpen_compl⟩ : Opens Y) y₀,
    ⟨Eventually.of_forall fun p => (hπ.contMDiff p).mdifferentiableAt (by simp), ?_, ?_, ?_⟩⟩
  · have h := hinv.mdiff_inv
    filter_upwards [h] with q hq
    exact ((hs _).mdifferentiableAt (by simp)).comp q hq
  · exact Eventually.of_forall fun p => by
      simp only [Function.comp_apply, hopen]
      exact hsec p (hmem _)
  · exact Eventually.of_forall fun q => by
      simp only [Function.comp_apply, hopen]
      exact congrFun hsπ ⟨q, hmem q⟩

/-- **The strict transform of a closed set along an empty centre is its preimage.** -/
theorem geoStrictTransform_empty (hπc : Continuous π) {A : Set Y} (hA : IsClosed A) :
    geoStrictTransform π (∅ : Set Y) A = π ⁻¹' A := by
  rw [geoStrictTransform, sdiff_empty, (hA.preimage hπc).closure_eq]

/-- **Along an empty centre the transform lies in the pullback on `N'`**: `Res_{N'} 𝔞' ⊆ Res_{N'} π^*𝔞`. -/
theorem restrictLe_geoTransform_empty_le_pullback (hπ : IsBlowupAlong n (∅ : Set Y) π) (𝔫 : MarkedIdeal n Y) :
    RestrictLe (𝔫.geoTransform ∅ π).N (𝔫.geoTransform ∅ π).ideal (GermIdeal.pullback (m := n) π 𝔫.ideal) :=
  fun _ _ _ hf =>
    CoefficientIdealAlongRestrictionFull.isInSpanOnAt_pullback_of_mem_geoTransform_of_notMem hπ 𝔫 (notMem_empty _) hf

/-- **The pullback lies in the transform**, restricted form: `Res_{N'} π^*𝔞 ⊆ Res_{N'} 𝔞'` (any centre). -/
theorem restrictLe_pullback_le_geoTransform (C : Set Y) (𝔫 : MarkedIdeal n Y) :
    RestrictLe (𝔫.geoTransform C π).N (GermIdeal.pullback (m := n) π 𝔫.ideal) (𝔫.geoTransform C π).ideal :=
  fun _ _ _ hG => RelativePrincipalizationSpan.IsInSpanAt.restrict
    (InvertibleIdealQuotient.isInSpanAt_self
      (CoefficientIdealAlongRestrictionFull.mem_geoTransform_of_mem_pullback 𝔫 hG) (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hG).1)

/-- **(K3) The coefficient ideal along `N` is unchanged by a step with empty centre**: for the blowup `π` along `∅`,
`𝓒_{N'}(𝔪') ≃ 𝓒_N(𝔪)'` (`N` a closed submanifold, coherent ideal, `d ≥ 1`).  Both are restricted-equivalent on
`N' = π⁻¹N` to `π^*𝓒_N(𝔪) = 𝓒_{π⁻¹N}(π^*𝔪)` (`π` is a biholomorphism). -/
theorem restrictEquiv_coeffMarkedAlong_geoTransform_empty (𝔪 : MarkedIdeal n Y) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (hπ : IsBlowupAlong n (∅ : Set Y) π) :
    RestrictEquiv (coeffMarkedAlong (𝔪.geoTransform ∅ π)) ((coeffMarkedAlong 𝔪).geoTransform ∅ π) := by
  have hloc := exists_isLocalInverseAt_of_isBlowupAlong_empty hπ
  have hW : (𝔪.geoTransform ∅ π).N = (MarkedIdeal.pullback π 𝔪).N :=
    geoStrictTransform_empty hπ.contMDiff.continuous hN.1
  have hpb : (coeffMarkedAlong (MarkedIdeal.pullback π 𝔪)).ideal =
      GermIdeal.pullback (m := n) π (coeffMarkedAlong 𝔪).ideal :=
    (congrArg MarkedIdeal.ideal (pullback_coeffMarkedAlong hπ.contMDiff hloc 𝔪 h𝔞 hN hd)).symm
  have hhol𝔭 : ∀ x g, (MarkedIdeal.pullback π 𝔪).ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg).1
  have hhol' : ∀ x g, (𝔪.geoTransform ∅ π).ideal.mem x g → HolomorphicAt n g x :=
    hol_of_isCoherent (HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h𝔞
      (isAdmissibleCentre_empty 𝔪) hπ)
  have a1 : RestrictLe (𝔪.geoTransform ∅ π).N (coeffMarkedAlong (𝔪.geoTransform ∅ π)).ideal
      (coeffMarkedAlong (MarkedIdeal.pullback π 𝔪)).ideal :=
    restrictLe_coeffMarkedAlong hW rfl hhol' hhol𝔭 (restrictLe_geoTransform_empty_le_pullback hπ 𝔪)
  have a2 : RestrictLe (𝔪.geoTransform ∅ π).N (coeffMarkedAlong (MarkedIdeal.pullback π 𝔪)).ideal
      (coeffMarkedAlong (𝔪.geoTransform ∅ π)).ideal := by
    have h0 : RestrictLe (MarkedIdeal.pullback π 𝔪).N (MarkedIdeal.pullback π 𝔪).ideal (𝔪.geoTransform ∅ π).ideal := by
      rw [← hW]
      exact restrictLe_pullback_le_geoTransform (π := π) ∅ 𝔪
    have := restrictLe_coeffMarkedAlong hW.symm rfl hhol𝔭 hhol' h0
    rwa [← hW] at this
  have b1 := restrictLe_geoTransform_empty_le_pullback hπ (coeffMarkedAlong 𝔪)
  have b2 := restrictLe_pullback_le_geoTransform (π := π) ∅ (coeffMarkedAlong 𝔪)
  rw [← hpb] at b1 b2
  exact ⟨rfl, rfl, rfl, restrictLe_trans a1 b2, restrictLe_trans b1 a2⟩

/-- **(K3) The restricted coefficient ideal is unchanged by a step with empty centre**: for `A ⊆ N` and the blowup `π`
along `∅`, `𝓒_{N'}(𝔪')|_{A'} ≃ (𝓒_N(𝔪)|_A)'` (`A'` the strict transform of `A`); restricting at the new stage or
transforming the old restriction gives restricted-equivalent marked ideals. -/
theorem restrictEquiv_restrictedCoeff_geoTransform_empty (𝔪 : MarkedIdeal n Y) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (hπ : IsBlowupAlong n (∅ : Set Y) π) {A : Set Y} (hA : A ⊆ 𝔪.N) :
    RestrictEquiv (withN (coeffMarkedAlong (𝔪.geoTransform ∅ π)) (geoStrictTransform π ∅ A))
      ((withN (coeffMarkedAlong 𝔪) A).geoTransform ∅ π) := by
  have hK := restrictEquiv_coeffMarkedAlong_geoTransform_empty 𝔪 hN h𝔞 hd hπ
  have hA' : geoStrictTransform π ∅ A ⊆ (𝔪.geoTransform ∅ π).N :=
    closure_mono (preimage_mono (sdiff_subset_sdiff_left hA))
  have b1 := restrictLe_geoTransform_empty_le_pullback hπ (coeffMarkedAlong 𝔪)
  have b2 := restrictLe_pullback_le_geoTransform (π := π) ∅ (coeffMarkedAlong 𝔪)
  have c1 := restrictLe_geoTransform_empty_le_pullback hπ (withN (coeffMarkedAlong 𝔪) A)
  have c2 := restrictLe_pullback_le_geoTransform (π := π) ∅ (withN (coeffMarkedAlong 𝔪) A)
  exact ⟨rfl, rfl, rfl, restrictLe_trans (restrictLe_mono hA' (restrictLe_trans hK.le b1)) c2,
    restrictLe_trans c1 (restrictLe_mono hA' (restrictLe_trans b2 hK.ge))⟩

/-- **(K3) Cosupports**: for the blowup `π` along `∅` and a closed `A ⊆ N`, `cosupp 𝓒_{N'}(𝔪')|_{A'} = π⁻¹ cosupp 𝓒_N(𝔪)|_A`. -/
theorem cosupp_restrictedCoeff_geoTransform_empty (𝔪 : MarkedIdeal n Y) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (hπ : IsBlowupAlong n (∅ : Set Y) π) {A : Set Y} (hA : A ⊆ 𝔪.N)
    (hAc : IsClosed A) :
    (withN (coeffMarkedAlong (𝔪.geoTransform ∅ π)) (geoStrictTransform π ∅ A)).cosupp =
      π ⁻¹' (withN (coeffMarkedAlong 𝔪) A).cosupp := by
  rw [(restrictEquiv_restrictedCoeff_geoTransform_empty 𝔪 hN h𝔞 hd hπ hA).cosupp_eq]
  ext z
  exact TransformOffCentre.mem_cosupp_geoTransform_iff (withN (coeffMarkedAlong 𝔪) A) hAc
    (fun _ _ hg => holomorphicAt_of_mem_coeffMarkedAlong _ hg) hπ (notMem_empty _)

end EmptyStep

section EmptyStepTower

variable {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}

/-- **(K3) along a tower**: for a multiple test blow-up `T` of `𝔪` followed by a blowup `π` along `∅` and `A ⊆ N`,
`S_A(𝔪_{T·π}) ≃ S_A(𝔪_T)'`, `S_A(𝔪_T) = 𝓒_{N_T}(𝔪_T)|_{A_T}`. -/
theorem restrictEquiv_restrictedCoeff_geoTransformAlong_empty (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    (π : Z → Y) (hπ : IsBlowupAlong n (∅ : Set Y) π) {A : Set X} (hA : A ⊆ 𝔪.N) :
    RestrictEquiv (withN (coeffMarkedAlong (geoTransformAlong 𝔪 (.step T ∅ π hπ))) (strictAlong (.step T ∅ π hπ) A))
      ((withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A)).geoTransform ∅ π) := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  have hAT : strictAlong T A ⊆ (geoTransformAlong 𝔪 T).N := by
    rw [N_geoTransformAlong]
    exact MemberInterTowerAlong.strictAlong_mono T hA
  exact restrictEquiv_restrictedCoeff_geoTransform_empty _ hNT hcT (by rwa [d_geoTransformAlong]) hπ hAT

end EmptyStepTower

/-! ### (K5) Tangent directions along towers -/

section Tangent

/-- Iterated derivative ideals along `N` are monotone in the ideal. -/
theorem iterDerivIdealAlong_le {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {N : Set M} {𝔞 𝔟 : GermIdeal n M} (h : 𝔞.Le 𝔟) :
    ∀ j, (iterDerivIdealAlong N 𝔞 j).Le (iterDerivIdealAlong N 𝔟 j)
  | 0 => h
  | j + 1 => derivIdealAlong_mono (iterDerivIdealAlong_le h j)

variable {X X' : CMfd.{u} n} {𝔪 : MarkedIdeal n X} {μ : ℕ}

/-- **(K5) Tangent directions along transported towers**: if `u` is a tangent direction of `(𝔪_T|_{N_T}, μ)` on `V`, then
`u ∘ Φ_T` is one of `((Φ^*𝔪)_{T'}|_{N'_{T'}}, μ)` on `Φ_T⁻¹V`. -/
theorem isTangentDirectionAlong_geoTransformAlong_transport
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) {V : Set Y}
    {u : Y → ℂ} (hu : IsTangentDirectionAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal μ V u) :
    IsTangentDirectionAlong (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower).N
      (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower).ideal μ ((transport Φ T).back ⁻¹' V)
      (u ∘ (transport Φ T).back) := by
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  rw [geoTransformAlong_transport Φ hN h𝔞 T hT]
  exact ContactEquivalenceAlong.isTangentDirectionAlong_pullback
    (fun y => ⟨_, isLocalInverseAt_of_contMDiff (transport Φ T).back.contMDiff (transport Φ T).back.symm.contMDiff
      (transport Φ T).back.apply_symm_apply (transport Φ T).back.symm_apply_apply y⟩) (hol_of_isCoherent hcT) hu

/-- **(K5) The hypersurfaces of maximal contact along transported towers**:
`N'_{T'} ∩ V(u ∘ Φ_T) = Φ_T⁻¹(N_T ∩ V(u))`. -/
theorem N_inter_zeroSet_geoTransformAlong_transport
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (u : Y → ℂ) :
    (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower).N ∩ {p | (u ∘ (transport Φ T).back) p = 0} =
      (transport Φ T).back ⁻¹' ((geoTransformAlong 𝔪 T).N ∩ {y | u y = 0}) := by
  rw [geoTransformAlong_transport Φ hN h𝔞 T hT]
  rfl

/-- **(K5) Tangent directions along restricted towers**: if `u` is a tangent direction of `(𝔪_T|_{N_T}, μ)` on `V`, then
`u|_{T⁻¹U}` is one of `((𝔪|_U)_{T|_U}|_{N_T ∩ T⁻¹U}, μ)` on `V ∩ T⁻¹U`. -/
theorem isTangentDirectionAlong_geoTransformAlong_restrict (U : Opens X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) {V : Set Y}
    {u : Y → ℂ} (hu : IsTangentDirectionAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal μ V u) :
    IsTangentDirectionAlong (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).N
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).ideal μ
      ((Subtype.val : openPreimage T U → Y) ⁻¹' V) (u ∘ Subtype.val) := by
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  rw [geoTransformAlong_restrict U hN h𝔞 T hT]
  exact ContactEquivalenceAlong.isTangentDirectionAlong_pullback
    (fun y => ⟨openInv (openPreimage T U) y, isLocalInverseAt_val (openPreimage T U) y⟩) (hol_of_isCoherent hcT) hu

/-- **(K5) The hypersurfaces of maximal contact along restricted towers**:
`N_{T|_U} ∩ V(u|_{T⁻¹U}) = T⁻¹U ∩ (N_T ∩ V(u))`. -/
theorem N_inter_zeroSet_geoTransformAlong_restrict (U : Opens X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (u : Y → ℂ) :
    (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).N ∩
        {p | (u ∘ (Subtype.val : openPreimage T U → Y)) p = 0} =
      (Subtype.val : openPreimage T U → Y) ⁻¹' ((geoTransformAlong 𝔪 T).N ∩ {y | u y = 0}) := by
  rw [geoTransformAlong_restrict U hN h𝔞 T hT]
  rfl

end Tangent

section TangentEmpty

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {π : Z → Y}

/-- **(K5) Tangent directions across a step with empty centre**: for the blowup `π` along `∅`, if `u` is a tangent
direction of `(𝔪|_N, d')` on `V` (any mark `d'`), then `u ∘ π` is one of `(𝔪'|_{N'}, d')` on `π⁻¹V` (`N` closed, ideal of
holomorphic germs); and `N' ∩ V(u ∘ π) = π⁻¹(N ∩ V(u))`. -/
theorem isTangentDirectionAlong_geoTransform_empty (𝔪 : MarkedIdeal n Y) (hN : IsClosed 𝔪.N)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (hπ : IsBlowupAlong n (∅ : Set Y) π) {μ : ℕ} {V : Set Y}
    {u : Y → ℂ} (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal μ V u) :
    IsTangentDirectionAlong (𝔪.geoTransform ∅ π).N (𝔪.geoTransform ∅ π).ideal μ (π ⁻¹' V) (u ∘ π) ∧
      (𝔪.geoTransform ∅ π).N ∩ {z | (u ∘ π) z = 0} = π ⁻¹' (𝔪.N ∩ {y | u y = 0}) := by
  have hP := ContactEquivalenceAlong.isTangentDirectionAlong_pullback
    (exists_isLocalInverseAt_of_isBlowupAlong_empty hπ) h𝔞 hu
  have hW : (𝔪.geoTransform ∅ π).N = π ⁻¹' 𝔪.N := geoStrictTransform_empty hπ.contMDiff.continuous hN
  have hle : (GermIdeal.pullback (m := n) π 𝔪.ideal).Le (𝔪.geoTransform ∅ π).ideal := fun _ _ hG =>
    CoefficientIdealAlongRestrictionFull.mem_geoTransform_of_mem_pullback 𝔪 hG
  rw [hW]
  exact ⟨⟨hP.isOpen, fun x hx => iterDerivIdealAlong_le hle (μ - 1) x _ (hP.mem x hx), hP.multiplicity_one⟩, rfl⟩

end TangentEmpty

end

end Hironaka.ContactCanonicalAlong
