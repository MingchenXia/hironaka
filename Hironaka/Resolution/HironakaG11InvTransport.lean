import Hironaka.Resolution.CanonicalResolution
import Hironaka.Blowup.BlowupUniqueness
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal

/-!
# Transport of canonical towers and invariant values along biholomorphisms and equivalent records

Lane G11B (run 0080), G11 route step 2 (`work/hironaka-resume-20261111/G11B/ROUTE-r1.md` §1); blueprint
`hironaka-g11-inv-transport.tex`.  Sources: Włodarczyk 2005, Proposition `pr:resol` and §2.4 (the canonical resolution
commutes with étale maps -- here biholomorphisms and open embeddings); Bierstone--Milman 1997, §1 (the invariant depends only
on the local isomorphism class of the presentation).

Throughout, `R` is a resolution invariant of the route (`ResolutionInvariantSeq.ResolutionInvariant n k Λ`, e.g.
`CanonicalCentres.canonicalInvariant n`), `Φ : X' ≅ X` a biholomorphism, `𝔪` on `X` and `𝔫` on `X'` marked ideals of the
domain with `RestrictEquiv (Φ^*𝔪) 𝔫` (`𝔫` is an *equivalent record after transport*).

## Main results

* `isTowerIso_transport_values`: along an isomorphism of towers `T' ≅ T` over `Φ` with `T` canonical for `𝔪`, `T'` is
  canonical for `𝔫`, the cosupports correspond, the values agree (`inv 𝔫 T' = inv 𝔪 T ∘ χ` on the cosupport) and the
  maximum loci correspond;
* `exists_transport_canonical`: every canonical tower of `𝔪` transports to a canonical tower of `𝔫`;
* `canonicalSegments_isTowerIso_of_length_eq`, **`resolving_canonicalSegments_isTowerIso`**: canonical segments without
  empty centres of `𝔫` and `𝔪` of equal length are isomorphic over `Φ`; resolving ones always are (uniqueness of the canonical
  resolution up to isomorphism, for every route invariant and every equivalent record);
* **`inv_eq_on_overlap`**, `levelSet_preimage_on_overlap`: for windows `U ⊆ X`, `U' ⊆ X'` with `Φ : U' ≅ U` and
  `RestrictEquiv (Φ^*(𝔪|_U)) (𝔫|_{U'})`, along canonical towers whose restrictions are isomorphic over `Φ`, the values agree on
  the overlap and every level set of the invariant on the cosupport corresponds (the compatibility of local centres needed
  for gluing); `inv_refl_eq_on_overlap`: the first stage (no tower needed);
* `restrictEquiv_vanishingRecord`, `inv_vanishingRecord_eq_on_overlap`: the vanishing-ideal records `(univ, [], I_C, 1)` of two
  windows whose ambient biholomorphism carries carrier to carrier are restricted-equivalent (indeed equal) after transport,
  so their values agree on overlaps.

Import discipline (Hironaka phase): this module does not import, even transitively, `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvTransport

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdealTowerTransport MarkedIdealRestrictOpen ResolutionInvariantSeq BlowupTowerSplit
open MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus IsCanonicalSegment isCanonicalSegment_step_iff)
open ResolutionInvariantSegments (maxLocus_preimage_of_surjective)
open ResolutionInvariantDriver (isCanonical_of_isCanonicalSegment)
open CanonicalResolution (isCanonicalSegment_of_append length_eq_zero_of_cosupp_eq_empty)

noncomputable section

variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-! ### Isomorphisms of towers over a biholomorphism, with an equivalent record -/

section Iso

variable (R : ResolutionInvariant.{u, v} n k Λ) {X X' : CMfd.{u} n}
  (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {𝔪 : MarkedIdeal n X} {𝔫 : MarkedIdeal n X'}

/-- **Transport of canonicality, cosupports and values along an isomorphism of towers, to an equivalent record**: if
`Φ^*𝔪` and `𝔫` are restricted-equivalent (both in the domain), `T` is a canonical segment of `𝔪` and `T' ≅ T` over `Φ` with
last-stage biholomorphism `χ`, then `T'` is a canonical segment of `𝔫`, `cosupp 𝔫_{T'} = χ⁻¹ cosupp 𝔪_T`, and
`inv 𝔫 T' p = inv 𝔪 T (χ p)` on the cosupport (properties (6) and (7)). -/
theorem isTowerIso_transport_values (h𝔪 : IsInvDomain k 𝔪) (h𝔫 : IsInvDomain k 𝔫)
    (hEq : RestrictEquiv (MarkedIdeal.pullback Φ 𝔪) 𝔫) {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'}
    {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hiso : IsTowerIso Φ T' T χ)
    (hcan : IsCanonical 𝔪 (R.inv 𝔪) T) :
    IsCanonical 𝔫 (R.inv 𝔫) T' ∧
      (geoTransformAlong 𝔫 T').cosupp = χ ⁻¹' (geoTransformAlong 𝔪 T).cosupp ∧
      ∀ p : Y', χ p ∈ (geoTransformAlong 𝔪 T).cosupp → R.inv 𝔫 T' p = R.inv 𝔪 T (χ p) := by
  have hΦ : IsInvDomain k (MarkedIdeal.pullback Φ 𝔪) := InvDomainTowerAlong.isInvDomain_pullback Φ h𝔪
  have hcanΦ : IsCanonical (MarkedIdeal.pullback Φ 𝔪) (R.inv (MarkedIdeal.pullback Φ 𝔪)) T' :=
    Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R h𝔪 Φ hiso hcan
  have hTt : IsGeoTestTower 𝔪 T := R.isInvValue.isGeoTestTower_of_isCanonical h𝔪 T hcan
  have hcosΦ : (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T').cosupp = χ ⁻¹' (geoTransformAlong 𝔪 T).cosupp :=
    IsTowerIso.cosupp_geoTransformAlong Φ h𝔪.isWellFormed.isClosedSubmanifold_N h𝔪.isWellFormed.isCoherent hiso hTt
  have hcosEq : (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T').cosupp = (geoTransformAlong 𝔫 T').cosupp :=
    (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hEq
      hΦ.isWellFormed.isClosedSubmanifold_N.1 hΦ.isWellFormed.isCoherent h𝔫.isWellFormed.isCoherent T').1
  refine ⟨Seq.InvDomainRebase.isCanonical_of_restrictEquiv R hΦ h𝔫 hEq T' hcanΦ, hcosEq.symm.trans hcosΦ,
    fun p hp => ?_⟩
  have hpΦ : p ∈ (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T').cosupp := by rw [hcosΦ]; exact hp
  rw [← R.isInvValue.representative _ _ hΦ h𝔫 hEq T' hcanΦ p hpΦ]
  exact R.isInvValue.towerIso Φ 𝔪 h𝔪 T' T χ hiso hcan p hp

/-- **The maximum loci correspond** along an isomorphism of towers, to an equivalent record:
`maxLocus (inv 𝔫 T') (cosupp 𝔫_{T'}) = χ⁻¹ maxLocus (inv 𝔪 T) (cosupp 𝔪_T)`. -/
theorem isTowerIso_maxLocus (h𝔪 : IsInvDomain k 𝔪) (h𝔫 : IsInvDomain k 𝔫)
    (hEq : RestrictEquiv (MarkedIdeal.pullback Φ 𝔪) 𝔫) {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'}
    {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hiso : IsTowerIso Φ T' T χ)
    (hcan : IsCanonical 𝔪 (R.inv 𝔪) T) :
    maxLocus (R.inv 𝔫 T') (geoTransformAlong 𝔫 T').cosupp =
      χ ⁻¹' maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨-, hcos, hval⟩ := isTowerIso_transport_values R Φ h𝔪 h𝔫 hEq hiso hcan
  rw [hcos]
  exact maxLocus_preimage_of_surjective χ.toEquiv.surjective hval

/-- **Every canonical tower transports**: for a canonical segment `T` of `𝔪`, the transported tower `Φ^*T` is a canonical
segment of the equivalent record `𝔫`, isomorphic to `T` over `Φ`, and its maximum loci are the preimages of those of `T`. -/
theorem exists_transport_canonical (h𝔪 : IsInvDomain k 𝔪) (h𝔫 : IsInvDomain k 𝔫)
    (hEq : RestrictEquiv (MarkedIdeal.pullback Φ 𝔪) 𝔫) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical 𝔪 (R.inv 𝔪) T) :
    ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X' Y') (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y),
      IsTowerIso Φ T' T χ ∧ IsCanonical 𝔫 (R.inv 𝔫) T' ∧
      maxLocus (R.inv 𝔫 T') (geoTransformAlong 𝔫 T').cosupp =
        χ ⁻¹' maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp := by
  have hiso := transport_isTowerIso Φ T
  exact ⟨_, _, _, hiso, (isTowerIso_transport_values R Φ h𝔪 h𝔫 hEq hiso hcan).1,
    isTowerIso_maxLocus R Φ h𝔪 h𝔫 hEq hiso hcan⟩

/-- **Canonical segments without empty centres of equal length are isomorphic over `Φ`** (for an equivalent record): each
centre of `T'` is the maximum locus, hence the preimage of the corresponding centre of `T`, and blowups along the same centre
are biholomorphic over the base (`BlowupUniqueness.exists_biholomorphism_over`). -/
theorem canonicalSegments_isTowerIso_of_length_eq (h𝔪 : IsInvDomain k 𝔪) (h𝔫 : IsInvDomain k 𝔫)
    (hEq : RestrictEquiv (MarkedIdeal.pullback Φ 𝔪) 𝔫) :
    ∀ {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y') (T : BlowupTower X Y),
      IsCanonicalSegment 𝔫 (R.inv 𝔫) T' → IsCanonicalSegment 𝔪 (R.inv 𝔪) T → T'.length = T.length →
        ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, IsTowerIso Φ T' T χ
  | _, _, .refl, .refl, _, _, _ => ⟨Φ, .refl⟩
  | _, _, .refl, .step _ _ _ _, _, _, hlen => by simp [BlowupTower.length] at hlen
  | _, _, .step _ _ _ _, .refl, _, _, hlen => by simp [BlowupTower.length] at hlen
  | _, _, .step T' C' π' hπ', .step T C π hπ, hT', hT, hlen => by
      obtain ⟨hT'₀, -, hC'⟩ := (isCanonicalSegment_step_iff _ _ T' C' π' hπ').mp hT'
      obtain ⟨hT₀, -, hC⟩ := (isCanonicalSegment_step_iff _ _ T C π hπ).mp hT
      have hlen₀ : T'.length = T.length := by simpa [BlowupTower.length] using hlen
      obtain ⟨χ, hIso⟩ := canonicalSegments_isTowerIso_of_length_eq h𝔪 h𝔫 hEq T' T hT'₀ hT₀ hlen₀
      have hCan := isCanonical_of_isCanonicalSegment (𝔪 := 𝔪) (R.inv 𝔪) T hT₀
      have hCC : χ ⁻¹' C = C' := by
        rw [hC', hC]
        exact (isTowerIso_maxLocus R Φ h𝔪 h𝔫 hEq hIso hCan).symm
      have hB := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse χ.contMDiff χ.symm.contMDiff
        χ.apply_symm_apply χ.symm_apply_apply hπ
      rw [hCC] at hB
      obtain ⟨e, f, he, hf, hπe, -, hfe, hef⟩ := BlowupUniqueness.exists_biholomorphism_over hπ' hB
      refine ⟨⟨⟨e, f, congrFun hfe, congrFun hef⟩, he, hf⟩, IsTowerIso.step hIso hπ' hπ _ (fun p => ?_) hCC⟩
      have h1 : χ.symm (π (e p)) = π' p := congrFun hπe p
      show π (e p) = χ (π' p)
      rw [← h1, χ.apply_symm_apply]

/-- **Uniqueness of the canonical resolution up to isomorphism** (for every route invariant and every equivalent record
after transport): two resolving canonical segments without empty centres, of `𝔫` and of `𝔪`, are isomorphic over `Φ`.  The
lengths agree: a longer one would continue after a stage of empty cosupport, where a canonical segment without empty centres
stops (`CanonicalResolution.length_eq_zero_of_cosupp_eq_empty`). -/
theorem resolving_canonicalSegments_isTowerIso (h𝔪 : IsInvDomain k 𝔪) (h𝔫 : IsInvDomain k 𝔫)
    (hEq : RestrictEquiv (MarkedIdeal.pullback Φ 𝔪) 𝔫) {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y')
    (T : BlowupTower X Y) (hT' : IsCanonicalSegment 𝔫 (R.inv 𝔫) T') (hT : IsCanonicalSegment 𝔪 (R.inv 𝔪) T)
    (hRes' : IsGeoResolution 𝔫 T') (hRes : IsGeoResolution 𝔪 T) :
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, IsTowerIso Φ T' T χ := by
  refine canonicalSegments_isTowerIso_of_length_eq R Φ h𝔪 h𝔫 hEq T' T hT' hT ?_
  rcases lt_trichotomy T'.length T.length with hlt | heq | hgt
  · exfalso
    set r := T.length - T'.length
    have hSplit := head_append_tail T r
    have hSegH : IsCanonicalSegment 𝔪 (R.inv 𝔪) (head T r) :=
      isCanonicalSegment_of_append 𝔪 (R.inv 𝔪) (head T r) (tail T r) (by rw [hSplit]; exact hT)
    have hlenH : T'.length = (head T r).length := by rw [length_head]; omega
    obtain ⟨χ, hIso⟩ := canonicalSegments_isTowerIso_of_length_eq R Φ h𝔪 h𝔫 hEq T' (head T r) hT' hSegH hlenH
    have hCan := isCanonical_of_isCanonicalSegment (𝔪 := 𝔪) (R.inv 𝔪) _ hSegH
    have hPre := (isTowerIso_transport_values R Φ h𝔪 h𝔫 hEq hIso hCan).2.1
    have hCos : (geoTransformAlong 𝔪 (head T r)).cosupp = ∅ := by
      rw [hRes'.2] at hPre
      refine eq_empty_iff_forall_notMem.mpr fun y hy => ?_
      obtain ⟨p, rfl⟩ := χ.toEquiv.surjective y
      have hp : p ∈ χ ⁻¹' (geoTransformAlong 𝔪 (head T r)).cosupp := hy
      rw [← hPre] at hp
      exact hp
    have hZero := length_eq_zero_of_cosupp_eq_empty 𝔪 (R.inv 𝔪) (head T r) hCos (tail T r)
      (by rw [hSplit]; exact hT)
    rw [length_tail] at hZero
    omega
  · exact heq
  · exfalso
    set r := T'.length - T.length
    have hSplit := head_append_tail T' r
    have hSegH : IsCanonicalSegment 𝔫 (R.inv 𝔫) (head T' r) :=
      isCanonicalSegment_of_append 𝔫 (R.inv 𝔫) (head T' r) (tail T' r) (by rw [hSplit]; exact hT')
    have hlenH : (head T' r).length = T.length := by rw [length_head]; omega
    obtain ⟨χ, hIso⟩ := canonicalSegments_isTowerIso_of_length_eq R Φ h𝔪 h𝔫 hEq (head T' r) T hSegH hT hlenH
    have hCan := isCanonical_of_isCanonicalSegment (𝔪 := 𝔪) (R.inv 𝔪) T hT
    have hCos : (geoTransformAlong 𝔫 (head T' r)).cosupp = ∅ := by
      rw [(isTowerIso_transport_values R Φ h𝔪 h𝔫 hEq hIso hCan).2.1, hRes.2, preimage_empty]
    have hZero := length_eq_zero_of_cosupp_eq_empty 𝔫 (R.inv 𝔫) (head T' r) hCos (tail T' r)
      (by rw [hSplit]; exact hT')
    rw [length_tail] at hZero
    omega

end Iso

/-! ### Overlaps of two windows -/

section Overlap

variable (R : ResolutionInvariant.{u, v} n k Λ) {X X' : CMfd.{u} n} {𝔪 : MarkedIdeal n X} {𝔫 : MarkedIdeal n X'}
  (U : Opens X) (U' : Opens X')
  (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)

/-- **The values of two windows agree on the overlap** (G11 route step 2, the compatibility input of the gluing): let
`U ⊆ X`, `U' ⊆ X'` be opens with a biholomorphism `Φ : U' ≅ U` such that `Φ^*(𝔪|_U)` and `𝔫|_{U'}` are restricted-equivalent,
`T` a canonical segment of `𝔪`, `T'` one of `𝔫`, whose restrictions are isomorphic over `Φ` with last-stage biholomorphism
`χ`.  Then for every point `p` of `T'` over `U'` with `χ p` in the cosupport of `𝔪_T`, `p` lies in the cosupport of `𝔫_{T'}`
and `inv 𝔫 T' p = inv 𝔪 T (χ p)` (properties (5), (6), (7)). -/
theorem inv_eq_on_overlap (h𝔪 : IsInvDomain k 𝔪) (h𝔫 : IsInvDomain k 𝔫)
    (hEq : RestrictEquiv (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪))
      (MarkedIdeal.pullback (Subtype.val : U' → X') 𝔫))
    {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    (hcan' : IsCanonical 𝔫 (R.inv 𝔫) T') (hcan : IsCanonical 𝔪 (R.inv 𝔪) T)
    {χ : CMfd.of (n := n) (openPreimage T' U') ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U)}
    (hiso : IsTowerIso Φ (restrict U' T') (restrict U T) χ) (p : openPreimage T' U')
    (hp : ((χ p : openPreimage T U) : Y) ∈ (geoTransformAlong 𝔪 T).cosupp) :
    (p : Y') ∈ (geoTransformAlong 𝔫 T').cosupp ∧ R.inv 𝔫 T' p = R.inv 𝔪 T (χ p) := by
  have hU : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) :=
    InvDomainTowerAlong.isInvDomain_pullback_val U h𝔪
  have hU' : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : U' → X') 𝔫) :=
    InvDomainTowerAlong.isInvDomain_pullback_val U' h𝔫
  have hcanU := Seq.ResolutionInvariantExt.isCanonical_restrict R h𝔪 U T hcan
  have hTt := R.isInvValue.isGeoTestTower_of_isCanonical h𝔪 T hcan
  have hT't := R.isInvValue.isGeoTestTower_of_isCanonical h𝔫 T' hcan'
  have hcosU := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict h𝔪.isWellFormed.isClosedSubmanifold_N
    h𝔪.isWellFormed.isCoherent U T hTt
  have hcosU' := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict h𝔫.isWellFormed.isClosedSubmanifold_N
    h𝔫.isWellFormed.isCoherent U' T' hT't
  obtain ⟨-, hcos, hval⟩ := isTowerIso_transport_values R Φ hU hU' hEq hiso hcanU
  have hχp : χ p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).cosupp := by
    rw [hcosU]; exact hp
  have hpU' : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U' → X') 𝔫) (restrict U' T')).cosupp := by
    rw [hcos]; exact hχp
  have hpc : (p : Y') ∈ (geoTransformAlong 𝔫 T').cosupp := by
    rw [hcosU'] at hpU'; exact hpU'
  refine ⟨hpc, ?_⟩
  rw [← R.isInvValue.restrictOpen 𝔫 h𝔫 U' T' hcan' p hpc, ← R.isInvValue.restrictOpen 𝔪 h𝔪 U T hcan (χ p) hp]
  exact hval p hχp

/-- **Level sets correspond on the overlap**: in the situation of `inv_eq_on_overlap`, for every value `λ`, a point `p` of `T'`
over `U'` lies in the `λ`-level set of `inv 𝔫 T'` on the cosupport iff `χ p` lies in that of `inv 𝔪 T` -- the local centres
cut out by a common value (e.g. the global maximum) are compatible on overlaps. -/
theorem levelSet_preimage_on_overlap (h𝔪 : IsInvDomain k 𝔪) (h𝔫 : IsInvDomain k 𝔫)
    (hEq : RestrictEquiv (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪))
      (MarkedIdeal.pullback (Subtype.val : U' → X') 𝔫))
    {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    (hcan' : IsCanonical 𝔫 (R.inv 𝔫) T') (hcan : IsCanonical 𝔪 (R.inv 𝔪) T)
    {χ : CMfd.of (n := n) (openPreimage T' U') ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U)}
    (hiso : IsTowerIso Φ (restrict U' T') (restrict U T) χ) (l : Λ) :
    (Subtype.val : openPreimage T' U' → Y') ⁻¹'
        {y | y ∈ (geoTransformAlong 𝔫 T').cosupp ∧ R.inv 𝔫 T' y = l} =
      χ ⁻¹' ((Subtype.val : openPreimage T U → Y) ⁻¹'
        {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ R.inv 𝔪 T y = l}) := by
  have hU : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) :=
    InvDomainTowerAlong.isInvDomain_pullback_val U h𝔪
  have hU' : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : U' → X') 𝔫) :=
    InvDomainTowerAlong.isInvDomain_pullback_val U' h𝔫
  have hcanU := Seq.ResolutionInvariantExt.isCanonical_restrict R h𝔪 U T hcan
  have hTt := R.isInvValue.isGeoTestTower_of_isCanonical h𝔪 T hcan
  have hT't := R.isInvValue.isGeoTestTower_of_isCanonical h𝔫 T' hcan'
  have hcosU := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict h𝔪.isWellFormed.isClosedSubmanifold_N
    h𝔪.isWellFormed.isCoherent U T hTt
  have hcosU' := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict h𝔫.isWellFormed.isClosedSubmanifold_N
    h𝔫.isWellFormed.isCoherent U' T' hT't
  obtain ⟨-, hcos, -⟩ := isTowerIso_transport_values R Φ hU hU' hEq hiso hcanU
  ext p
  simp only [mem_preimage]
  constructor
  · rintro ⟨hpc, hpl⟩
    have hpU' : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U' → X') 𝔫) (restrict U' T')).cosupp := by
      rw [hcosU']; exact hpc
    rw [hcos] at hpU'
    have hχp : ((χ p : openPreimage T U) : Y) ∈ (geoTransformAlong 𝔪 T).cosupp := by
      rw [hcosU] at hpU'; exact hpU'
    exact ⟨hχp, (inv_eq_on_overlap R U U' Φ h𝔪 h𝔫 hEq hcan' hcan hiso p hχp).2.symm.trans hpl⟩
  · rintro ⟨hχp, hpl⟩
    obtain ⟨hpc, hval⟩ := inv_eq_on_overlap R U U' Φ h𝔪 h𝔫 hEq hcan' hcan hiso p hχp
    exact ⟨hpc, hval.trans hpl⟩

/-- **The first stage** (no tower): the values of the two windows' records agree at the points of the overlap whose image
lies in the cosupport. -/
theorem inv_refl_eq_on_overlap (h𝔪 : IsInvDomain k 𝔪) (h𝔫 : IsInvDomain k 𝔫)
    (hEq : RestrictEquiv (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪))
      (MarkedIdeal.pullback (Subtype.val : U' → X') 𝔫)) (p : U') (hp : ((Φ p : U) : X) ∈ 𝔪.cosupp) :
    (p : X') ∈ 𝔫.cosupp ∧
      R.inv 𝔫 (BlowupTower.refl : BlowupTower X' X') p = R.inv 𝔪 (BlowupTower.refl : BlowupTower X X) (Φ p) :=
  inv_eq_on_overlap R U U' Φ h𝔪 h𝔫 hEq (T' := .refl) (T := .refl) trivial trivial (χ := Φ) IsTowerIso.refl p hp

end Overlap

/-! ### Vanishing-ideal records -/

section Vanishing

variable (n) in
/-- **The vanishing-ideal record** `(univ, [], I_C, 1)` of a subset `C` of a complex manifold (Włodarczyk 2009: the marked
ideal whose canonical principalization gives the embedded resolution). -/
def vanishingRecord {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] (C : Set M) :
    MarkedIdeal n M :=
  ⟨univ, [], vanishingIdeal (n := n) C, 1⟩

variable {M M' : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **Vanishing-ideal records pull back exactly along open holomorphic embeddings** (in particular biholomorphisms and
inclusions of opens): `b^*(univ, [], I_C, 1) = (univ, [], I_{b⁻¹C}, 1)`. -/
theorem pullback_vanishingRecord (b : M' → M) (hb : HironakaBaseChange.IsOpenHoloEmbedding n b) (C : Set M) :
    MarkedIdeal.pullback b (vanishingRecord n C) = vanishingRecord n (b ⁻¹' C) :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
    (HironakaActualOpenEmbeddingVanishingIdeal.pullback_vanishingIdeal_of_isOpenHoloEmbedding b hb C) rfl

/-- **Vanishing-ideal records of corresponding carriers are restricted-equivalent after transport**: for a biholomorphism
`Φ : M' ≅ M` with `Φ⁻¹C = C'` (and coherent `I_{C'}`), `RestrictEquiv (Φ^*(univ, [], I_C, 1)) (univ, [], I_{C'}, 1)` -- an
equality, so the step-3 comparison of `ROUTE-r1.md` §2 is trivial for these records. -/
theorem restrictEquiv_vanishingRecord (Φ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M) {C : Set M}
    {C' : Set M'} (hC : Φ ⁻¹' C = C') (hcoh : (vanishingIdeal (n := n) C').IsCoherent) :
    RestrictEquiv (MarkedIdeal.pullback Φ (vanishingRecord n C)) (vanishingRecord n C') := by
  have h : MarkedIdeal.pullback Φ (vanishingRecord n C) = vanishingRecord n (Φ ⁻¹' C) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
      (HironakaActualOpenEmbeddingVanishingIdeal.pullback_vanishingIdeal_of_biholomorphism Φ C) rfl
  rw [h, hC]
  exact MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv.refl hcoh

/-- **The values of the vanishing-ideal records of two windows agree on the overlap**: windows `U ⊆ X`, `U' ⊆ X'` with
carriers `C ⊆ X`, `C' ⊆ X'`, a biholomorphism `Φ : U' ≅ U` carrying `C' ∩ U'` onto `C ∩ U`, canonical segments `T`, `T'` of
the two records whose restrictions are isomorphic over `Φ`: the values agree at the points over the overlap
(`inv_eq_on_overlap` with `restrictEquiv_vanishingRecord`). -/
theorem inv_vanishingRecord_eq_on_overlap (R : ResolutionInvariant.{u, v} n k Λ) {X X' : CMfd.{u} n} {C : Set X}
    {C' : Set X'} (h𝔪 : IsInvDomain k (vanishingRecord n C)) (h𝔫 : IsInvDomain k (vanishingRecord n C'))
    (U : Opens X) (U' : Opens X')
    (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)
    (hΦC : ∀ p : U', ((Φ p : U) : X) ∈ C ↔ (p : X') ∈ C')
    {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    (hcan' : IsCanonical (vanishingRecord n C') (R.inv (vanishingRecord n C')) T')
    (hcan : IsCanonical (vanishingRecord n C) (R.inv (vanishingRecord n C)) T)
    {χ : CMfd.of (n := n) (openPreimage T' U') ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U)}
    (hiso : IsTowerIso Φ (restrict U' T') (restrict U T) χ) (p : openPreimage T' U')
    (hp : ((χ p : openPreimage T U) : Y) ∈ (geoTransformAlong (vanishingRecord n C) T).cosupp) :
    (p : Y') ∈ (geoTransformAlong (vanishingRecord n C') T').cosupp ∧
      R.inv (vanishingRecord n C') T' p = R.inv (vanishingRecord n C) T (χ p) := by
  have hU' := InvDomainTowerAlong.isInvDomain_pullback_val U' h𝔫
  have hEq : RestrictEquiv (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → X) (vanishingRecord n C)))
      (MarkedIdeal.pullback (Subtype.val : U' → X') (vanishingRecord n C')) := by
    have h1 := pullback_vanishingRecord (Subtype.val : U → X) (HironakaBaseChange.isOpenHoloEmbedding_val (n := n) U) C
    have h2 := pullback_vanishingRecord (Subtype.val : U' → X') (HironakaBaseChange.isOpenHoloEmbedding_val (n := n) U') C'
    rw [h1, h2]
    refine restrictEquiv_vanishingRecord Φ (ext fun p => hΦC p) ?_
    have hc := hU'.isWellFormed.isCoherent
    rw [h2] at hc
    exact hc
  exact inv_eq_on_overlap R U U' Φ h𝔪 h𝔫 hEq hcan' hcan hiso p hp

end Vanishing

end

end Hironaka.HironakaG11InvTransport
