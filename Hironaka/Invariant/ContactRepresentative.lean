import Hironaka.Invariant.ContactStageRebase

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1 does not depend on the representative of the marked ideal

Hironaka phase H3 (TN23-ENVELOPES), claimed on I-0981 C-0103 / I-0977 C-0142: the H3 input for property (7) (independence
of the representative) of `hir:centre-function` for the Step 1 value function of `hir:maximal-order-step` and hence for
`hir:general-step` (`blueprint/src/hironaka.tex`).  A marked ideal is only determined by the restriction of its ideal to `N`
(`MarkedIdealOperationsAlong.RestrictEquiv`); Step 1 forms `J̄ = 𝓒_N(𝓗_N(𝔍))`, chooses a tangent direction of
`(𝔍.ideal|_N, d)` and restricts the coefficient ideal of the transform to the strict transform of the hypersurface of
maximal contact.  All three steps respect restricted equivalence.  Blueprint `mc:contact-representative`
(`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005 (arXiv `hiron.tex`), Proposition `pr:resol` (4) and the
definition of marked ideals (`(M, N, E, 𝓘, μ)` with `𝓘` an ideal of `𝒪_N`).

## Main results

* `restrictLe_homogenizedIdealAlong`, `restrictEquiv_homMarkedAlong`, `restrictEquiv_barMarked`: `𝓗_N` and
  `𝓒_N(𝓗_N(·))` respect restricted inclusions / equivalence on `N`;
* `restrictEquiv_pullback_val`: restricted equivalence passes to open sets;
* `exists_isTangentDirectionAlong_of_restrictLe`: a tangent direction `u` of `(𝔞|_N, μ)` on `U` gives, near every point of
  `N ∩ U`, a tangent direction `w` of `(𝔟|_N, μ)` with `w = u` on `N` whenever `𝔞|_N ⊆ 𝔟|_N` (so the hypersurface of maximal
  contact inside `N` is the same);
* `restrictEquiv_contactMarked`: for `(M, N, ∅, 𝔞, μ) ≃ (M, N, ∅, 𝔞', μ)`, tangent directions `u`, `w` equal on `N` over an
  open `O`, a multiple test blow-up `T₀` and `W ⊆ T₀⁻¹O`:
  `contactMarked N 𝔞 μ u T₀ W ≃ contactMarked N 𝔞' μ w T₀ W`;
* `contactMarked_representative`: with TN3's `InvDomainRebase` -- the domain, the canonical segments and the values of a
  resolution invariant agree for the two.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ContactRepresentative

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CoefficientIdealRestriction HomogenizedIdealAlong MarkedIdealBiholomorphism DerivativeIdealAlong
  MarkedIdealRestrictOpen MarkedIdealOperationsAlong.MarkedIdeal ResolutionInvariantExt RestrictedIdealWeight
open HomogenizedGlueingTower (strictAlong)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### The homogenized and coefficient ideals respect restricted equivalence -/

section Hom

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The homogenized ideal along `N` respects restricted inclusions on `N`**: `𝔞|_N ⊆ 𝔟|_N` gives
`𝓗_N(𝔞, μ)|_N ⊆ 𝓗_N(𝔟, μ)|_N` (the derivative ideals along `N` do, and so do products, powers and finite sums). -/
theorem restrictLe_homogenizedIdealAlong {N : Set M} {𝔞 𝔟 : GermIdeal n M}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x)
    (h : RestrictLe N 𝔞 𝔟) (μ : ℕ) :
    RestrictLe N (homogenizedIdealAlong N 𝔞 μ) (homogenizedIdealAlong N 𝔟 μ) :=
  HomogenizedIdealAlongTower.restrictLe_homSum
    (fun i _ => GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔟 i)
    (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔟 (μ - 1))
    (fun i _ => ContactCanonicalAlong.restrictLe_iterDerivIdealAlong h𝔞 h𝔟 h i)
    (ContactCanonicalAlong.restrictLe_iterDerivIdealAlong h𝔞 h𝔟 h (μ - 1))

/-- **Restricted-equivalent marked ideals have restricted-equivalent homogenized marked ideals along `N`.** -/
theorem restrictEquiv_homMarkedAlong {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫)
    (h𝔪 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (h𝔫 : ∀ x g, 𝔫.ideal.mem x g → HolomorphicAt n g x) :
    RestrictEquiv (homMarkedAlong 𝔪) (homMarkedAlong 𝔫) where
  N_eq := h.N_eq
  E_eq := h.E_eq
  d_eq := h.d_eq
  le := by
    show RestrictLe 𝔪.N (homogenizedIdealAlong 𝔪.N 𝔪.ideal 𝔪.d) (homogenizedIdealAlong 𝔫.N 𝔫.ideal 𝔫.d)
    rw [← h.N_eq, ← h.d_eq]
    exact restrictLe_homogenizedIdealAlong h𝔪 h𝔫 h.le 𝔪.d
  ge := by
    show RestrictLe 𝔪.N (homogenizedIdealAlong 𝔫.N 𝔫.ideal 𝔫.d) (homogenizedIdealAlong 𝔪.N 𝔪.ideal 𝔪.d)
    rw [← h.N_eq, ← h.d_eq]
    exact restrictLe_homogenizedIdealAlong h𝔫 h𝔪 h.ge 𝔪.d

/-- **The marked ideal of Step 1 respects restricted equivalence**: `𝔍 ≃ 𝔍'` gives `𝓒_N(𝓗_N(𝔍)) ≃ 𝓒_N(𝓗_N(𝔍'))` (`N` a
closed submanifold, coherent ideals). -/
theorem restrictEquiv_barMarked {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    RestrictEquiv (coeffMarkedAlong (homMarkedAlong 𝔪)) (coeffMarkedAlong (homMarkedAlong 𝔫)) :=
  ContactCanonicalAlong.restrictEquiv_coeffMarkedAlong
    (restrictEquiv_homMarkedAlong h (hol_of_isCoherent h𝔪) (hol_of_isCoherent h𝔫))
    (hol_of_isCoherent (isCoherent_homMarkedAlong h𝔪 hN))
    (hol_of_isCoherent (isCoherent_homMarkedAlong h𝔫 (h.N_eq ▸ hN)))

/-- **Restricted equivalence passes to open sets** (the second ideal coherent). -/
theorem restrictEquiv_pullback_val (U : Opens M) {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    RestrictEquiv (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪) (MarkedIdeal.pullback (Subtype.val : U → M) 𝔫) where
  N_eq := by
    show (Subtype.val : U → M) ⁻¹' 𝔪.N = (Subtype.val : U → M) ⁻¹' 𝔫.N
    rw [h.N_eq]
  E_eq := by
    show 𝔪.E.map ((Subtype.val : U → M) ⁻¹' ·) = 𝔫.E.map ((Subtype.val : U → M) ⁻¹' ·)
    rw [h.E_eq]
  d_eq := h.d_eq
  le := RestrictLeCalculus.restrictLe_pullback contMDiff_subtype_val (fun _ hy => hy) h𝔫 h.le
  ge := RestrictLeCalculus.restrictLe_pullback contMDiff_subtype_val (fun _ hy => hy) h𝔪 h.ge

end Hom

/-! ### Tangent directions of restricted-equivalent marked ideals -/

section Tangent

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Tangent directions transfer along restricted inclusions**: if `𝔞|_N ⊆ 𝔟|_N` (`N` a closed submanifold, `𝔟` coherent)
and `u` is a tangent direction of `(𝔞|_N, μ)` along `N` on `U`, then every `x ∈ N ∩ U` has an open neighbourhood `O ⊆ U`
carrying a tangent direction `w` of `(𝔟|_N, μ)` along `N` with `w = u` on `N ∩ O`: on `N`, the germs of `𝓓_N^{μ-1}(𝔞)` are
combinations of germs of `𝓓_N^{μ-1}(𝔟)` (`ContactEquivalenceAlong.exists_isTangentDirectionAlong_of_isInSpanOnAt`). -/
theorem exists_isTangentDirectionAlong_of_restrictLe {N : Set M} {𝔞 𝔟 : GermIdeal n M}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (h𝔟 : 𝔟.IsCoherent) (hN : IsClosedSubmanifold n N)
    (h : RestrictLe N 𝔞 𝔟) {μ : ℕ} {U : Set M} {u : M → ℂ} (hu : IsTangentDirectionAlong N 𝔞 μ U u) {x : M}
    (hxU : x ∈ U) (hxN : x ∈ N) :
    ∃ O : Opens M, x ∈ O ∧ (O : Set M) ⊆ U ∧ ∃ w : M → ℂ, IsTangentDirectionAlong N 𝔟 μ O w ∧
      ∀ y ∈ O, y ∈ N → w y = u y :=
  ContactEquivalenceAlong.exists_isTangentDirectionAlong_of_isInSpanOnAt h𝔟 hN hu.isOpen
    (fun y hy => GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (μ - 1) y u (hu.mem y hy))
    (fun y hy hyN => ContactCanonicalAlong.restrictLe_iterDerivIdealAlong h𝔞 (hol_of_isCoherent h𝔟) h (μ - 1) y hyN u
      (hu.mem y hy))
    (fun y hy _ h0 => hu.multiplicity_one y hy h0) hxU hxN

end Tangent

/-! ### Step 1b's restricted marked ideal for restricted-equivalent representatives -/

section ContactMarked

open MaximalOrderStepOneB (stepOneMarked contactMarked)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 𝔞' : GermIdeal n M} {μ : ℕ}

/-- **Step 1b's restricted marked ideal does not depend on the representative**: let `(M, N, ∅, 𝔞, μ) ≃ (M, N, ∅, 𝔞', μ)`
(coherent ideals, `N` a closed submanifold), `u`, `w` functions equal on `N` over an open `O` (in use: a tangent direction of
`(𝔞|_N, μ)` and the one of `(𝔞'|_N, μ)` given by `exists_isTangentDirectionAlong_of_restrictLe`), `T₀` a multiple test
blow-up of `stepOneMarked N 𝔞 μ` and `W ⊆ T₀⁻¹O` open.  Then `contactMarked N 𝔞 μ u T₀ W ≃ contactMarked N 𝔞' μ w T₀ W`. -/
theorem restrictEquiv_contactMarked (h𝔞 : 𝔞.IsCoherent) (h𝔞' : 𝔞'.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hEq : RestrictEquiv (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) ⟨N, [], 𝔞', μ⟩) {u w : M → ℂ} (O : Opens M)
    (huw : ∀ y ∈ O, y ∈ N → u y = w y) {Y : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y)
    (hT₀ : IsGeoTestTower (stepOneMarked N 𝔞 μ) T₀) (W : Opens Y) (hWO : (W : Set Y) ⊆ openPreimage T₀ O) :
    RestrictEquiv (contactMarked N 𝔞 μ u T₀ W) (contactMarked N 𝔞' μ w T₀ W) := by
  have hJ : RestrictEquiv (stepOneMarked N 𝔞 μ) (stepOneMarked N 𝔞' μ) :=
    restrictEquiv_barMarked (M := M) (𝔪 := ⟨N, [], 𝔞, μ⟩) (𝔫 := ⟨N, [], 𝔞', μ⟩) hEq hN h𝔞 h𝔞'
  obtain ⟨hJN, hJc, -⟩ := ContactIndependenceAlong.coeffHom_basic (μ := μ) h𝔞 hN
  obtain ⟨-, hJc', -⟩ := ContactIndependenceAlong.coeffHom_basic (μ := μ) h𝔞' hN
  have hT₀' : IsGeoTestTower (stepOneMarked N 𝔞' μ) T₀ :=
    ((MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hJ hJN.1 hJc hJc').2 T₀).1.mp hT₀
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T₀ hT₀
  obtain ⟨hNT', hcT'⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (hJ.N_eq ▸ hJN) hJc' T₀ hT₀'
  have hK := ContactCanonicalAlong.restrictEquiv_restrictedCoeff_geoTransformAlong hJ hJN.1 hJc hJc'
    (A := N ∩ {x | u x = 0}) (fun x hx => hx.1) T₀
  have hP := restrictEquiv_pullback_val W hK (isCoherent_coeffMarkedAlong hcT hNT) (isCoherent_coeffMarkedAlong hcT' hNT')
  -- the hypersurfaces `N ∩ V(u)` and `N ∩ V(w)` have the same strict transform over `O`
  have hloc := ContactEquivalenceStage.strictAlong_inter_preimage_eq O.isOpen
    (A := N ∩ {x | u x = 0}) (B := N ∩ {x | w x = 0}) (by
      ext y
      show (y ∈ N ∧ u y = 0) ∧ y ∈ O ↔ (y ∈ N ∧ w y = 0) ∧ y ∈ O
      constructor
      · rintro ⟨⟨hyN, hy0⟩, hyO⟩
        exact ⟨⟨hyN, by rw [← huw y hyO hyN]; exact hy0⟩, hyO⟩
      · rintro ⟨⟨hyN, hy0⟩, hyO⟩
        exact ⟨⟨hyN, by rw [huw y hyO hyN]; exact hy0⟩, hyO⟩) T₀
  have hset : (Subtype.val : W → Y) ⁻¹' strictAlong T₀ (N ∩ {x | w x = 0}) =
      (Subtype.val : W → Y) ⁻¹' strictAlong T₀ (N ∩ {x | u x = 0}) := by
    ext p
    have hp : (p : Y) ∈ T₀.proj ⁻¹' (O : Set M) := hWO p.2
    constructor
    · intro h
      have h1 : (p : Y) ∈ strictAlong T₀ (N ∩ {x | w x = 0}) ∩ T₀.proj ⁻¹' (O : Set M) := ⟨h, hp⟩
      rw [← hloc] at h1
      exact h1.1
    · intro h
      have h1 : (p : Y) ∈ strictAlong T₀ (N ∩ {x | u x = 0}) ∩ T₀.proj ⁻¹' (O : Set M) := ⟨h, hp⟩
      rw [hloc] at h1
      exact h1.1
  unfold contactMarked
  rw [ContactCanonicalAlong.pullback_withN, ContactCanonicalAlong.pullback_withN (Subtype.val : W → Y)
    (coeffMarkedAlong (geoTransformAlong (stepOneMarked N 𝔞' μ) T₀)), hset, ← ContactCanonicalAlong.pullback_withN,
    ← ContactCanonicalAlong.pullback_withN]
  exact hP

variable {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **The values of Step 1b do not depend on the representative**: in the situation of `restrictEquiv_contactMarked`, if
`contactMarked N 𝔞 μ u T₀ W` lies in the domain of a resolution invariant `R`, so does `contactMarked N 𝔞' μ w T₀ W`, the two
have the same canonical segments, and along them `R` takes the same values on the cosupport (properties (7) and (5) of
`R` with TN3's `InvDomainRebase.isInvDomain_of_restrictEquiv` / `isCanonical_of_restrictEquiv`). -/
theorem contactMarked_representative (R : ResolutionInvariant.{u, v} n k Λ) (h𝔞 : 𝔞.IsCoherent)
    (h𝔞' : 𝔞'.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hEq : RestrictEquiv (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) ⟨N, [], 𝔞', μ⟩) {u w : M → ℂ} (O : Opens M)
    (huw : ∀ y ∈ O, y ∈ N → u y = w y) {Y : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y)
    (hT₀ : IsGeoTestTower (stepOneMarked N 𝔞 μ) T₀) (W : Opens Y) (hWO : (W : Set Y) ⊆ openPreimage T₀ O)
    (hdom : IsInvDomain k (contactMarked N 𝔞 μ u T₀ W)) :
    IsInvDomain k (contactMarked N 𝔞' μ w T₀ W) ∧
      ∀ {Z : CMfd.{u} n} (T₁ : BlowupTower (CMfd.of (n := n) W) Z),
        IsCanonical (contactMarked N 𝔞 μ u T₀ W) (R.inv (contactMarked N 𝔞 μ u T₀ W)) T₁ →
        IsCanonical (contactMarked N 𝔞' μ w T₀ W) (R.inv (contactMarked N 𝔞' μ w T₀ W)) T₁ ∧
        ∀ z ∈ (geoTransformAlong (contactMarked N 𝔞 μ u T₀ W) T₁).cosupp,
          R.inv (contactMarked N 𝔞 μ u T₀ W) T₁ z = R.inv (contactMarked N 𝔞' μ w T₀ W) T₁ z := by
  have hE := restrictEquiv_contactMarked h𝔞 h𝔞' hN hEq O huw T₀ hT₀ W hWO
  have hc' : (contactMarked N 𝔞' μ w T₀ W).ideal.IsCoherent := by
    have hJ : RestrictEquiv (stepOneMarked N 𝔞 μ) (stepOneMarked N 𝔞' μ) :=
      restrictEquiv_barMarked (M := M) (𝔪 := ⟨N, [], 𝔞, μ⟩) (𝔫 := ⟨N, [], 𝔞', μ⟩) hEq hN h𝔞 h𝔞'
    obtain ⟨hJN, hJc, -⟩ := ContactIndependenceAlong.coeffHom_basic (μ := μ) h𝔞 hN
    obtain ⟨-, hJc', -⟩ := ContactIndependenceAlong.coeffHom_basic (μ := μ) h𝔞' hN
    have hT₀' : IsGeoTestTower (stepOneMarked N 𝔞' μ) T₀ :=
      ((MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hJ hJN.1 hJc hJc').2 T₀).1.mp hT₀
    obtain ⟨hNT', hcT'⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (hJ.N_eq ▸ hJN) hJc' T₀ hT₀'
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (isCoherent_coeffMarkedAlong hcT' hNT')
  have hdom' := InvDomainRebase.isInvDomain_of_restrictEquiv hdom hE hc'
  refine ⟨hdom', fun T₁ hcan => ⟨InvDomainRebase.isCanonical_of_restrictEquiv R hdom hdom' hE T₁ hcan, fun z hz => ?_⟩⟩
  exact R.representative _ _ hdom hdom' hE T₁ hcan z hz

end ContactMarked

end

end Hironaka.ContactRepresentative
