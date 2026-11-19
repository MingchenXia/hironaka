import Hironaka.Resolution.HironakaG11PresLineState
import Hironaka.Resolution.HironakaG11InvBMClass
import Hironaka.Resolution.HironakaG11InvTransport
import Hironaka.Resolution.HironakaG8LocalPower
import Hironaka.Analytic.PrincipalizationStepOneAssembly

/-!
# Transport of class-functorial invariant values between locally equivalent window records (goal G11, (3b))

Lane G11B's `HironakaG11InvTransport.inv_eq_on_overlap` transports the values of a route invariant between two window
records whose restrictions to an overlap are restricted-equivalent after an ambient biholomorphism (property (7) of the
invariant). The Hilbert–Samuel window records of two windows are not restricted-equivalent (different standard bases), but they
are locally `s(i,ii)`-equivalent (`HironakaG11PresLineState.locWPEquiv_of_nativeHSState`); for a class-functorial invariant
(lane G11B's `HironakaG11InvBMClass.BMInvariant` for G8's `LocWPEquiv`, repair (B')) the same transport holds.

* `pullback_powerMarked`: pullbacks commute with powers of marked ideals (coherent ideal);
* **`inv_eq_on_overlap_of_classFunctorial`**: for `B : BMInvariant LocWPEquiv k Λ`, windows `U ⊆ X`, `U' ⊆ X'`, a biholomorphism
  `Φ : U' ≅ U`, records `𝔪`, `𝔫` in the domain with carrier `univ`, empty boundary and the same mark, whose restrictions are
  `LocWPEquiv` after `Φ`, along canonical towers whose restrictions are isomorphic over `Φ`: the cosupports correspond and the
  values agree (BM08 Thm 7.1, the invariant depends only on the equivalence class; properties (5), (6) of the invariant);
* **`locWPEquiv_overlap_of_native`**: two records in the native Hilbert–Samuel state for `(W, H)`, `(W', H)` with
  `Φ⁻¹(W ∩ U) = W' ∩ U'`, and any powers of them, are `LocWPEquiv` on the overlap after `Φ`, given the named step
  `HironakaG11PresLineState.NativeLineStability` ((3a-lines)).

Nothing here proves or assumes G11. Blueprint: `hironaka-g11-pres-line-state.tex`.
-/

set_option autoImplicit false

open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11PresClassTransport

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealBiholomorphism
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open HironakaG11InvBMClass (BMInvariant SameCarrierDim ExpAgree expAgree_of_nil)
open HironakaG8LocalHistory (LocWPEquiv LocEquiv)
open HironakaActualPowerBoundaryExponents (powerMarked)
open HironakaG11PresLineState (NativeHSState NativeLineStability locWPEquiv_of_nativeHSState)

variable {n : ℕ}

/-- **Pullbacks commute with powers** of marked ideals with coherent ideal. -/
theorem pullback_powerMarked {M M' : CMfd.{u} n} {f : M' → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) (𝔪 : MarkedIdeal n M)
    (h𝔞 : 𝔪.ideal.IsCoherent) (e : ℕ) :
    MarkedIdeal.pullback f (powerMarked 𝔪 e) = powerMarked (MarkedIdeal.pullback f 𝔪) e := by
  show (⟨f ⁻¹' 𝔪.N, 𝔪.E.map (f ⁻¹' ·), GermIdeal.pullback (m := n) f (IdealWeightPowers.idealPow 𝔪.ideal e),
      𝔪.d * e⟩ : MarkedIdeal n M') =
    ⟨f ⁻¹' 𝔪.N, 𝔪.E.map (f ⁻¹' ·), IdealWeightPowers.idealPow (GermIdeal.pullback (m := n) f 𝔪.ideal) e, 𝔪.d * e⟩
  rw [PrincipalizationStepOneAssembly.pullback_idealPow hf h𝔞 e]

section Overlap

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Values of a class-functorial invariant agree on overlaps of locally equivalent window records.** Let `U ⊆ X`, `U' ⊆ X'`
be opens with a biholomorphism `Φ : U' ≅ U`, `𝔪`, `𝔫` marked ideals of the domain with carrier `univ`, empty boundary and the
same mark such that `Φ^*(𝔪|_U)` and `𝔫|_{U'}` are `LocWPEquiv`, `T`, `T'` canonical segments of `𝔪`, `𝔫` whose restrictions are
isomorphic over `Φ` (last-stage biholomorphism `χ`). Then for every point `p` of `T'` over `U'`, `χ p` lies in the cosupport of
`𝔪_T` iff `p` lies in that of `𝔫_{T'}`, and then `inv 𝔫 T' p = inv 𝔪 T (χ p)`. -/
theorem inv_eq_on_overlap_of_classFunctorial (B : BMInvariant n (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
    {X X' : CMfd.{u} n} {𝔪 : MarkedIdeal n X} {𝔫 : MarkedIdeal n X'} (U : Opens X) (U' : Opens X')
    (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)
    (h𝔪 : IsInvDomain k 𝔪) (h𝔫 : IsInvDomain k 𝔫) (hN𝔪 : 𝔪.N = univ) (hN𝔫 : 𝔫.N = univ) (hE𝔪 : 𝔪.E = [])
    (hE𝔫 : 𝔫.E = []) (hd : 𝔪.d = 𝔫.d)
    (hEq : LocWPEquiv (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪))
      (MarkedIdeal.pullback (Subtype.val : U' → X') 𝔫))
    {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    (hcan' : IsCanonical 𝔫 (B.toResolutionInvariant.inv 𝔫) T') (hcan : IsCanonical 𝔪 (B.toResolutionInvariant.inv 𝔪) T)
    {χ : CMfd.of (n := n) (openPreimage T' U') ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U)}
    (hiso : IsTowerIso Φ (restrict U' T') (restrict U T) χ) (p : openPreimage T' U') :
    ((((χ p : openPreimage T U) : Y) ∈ (geoTransformAlong 𝔪 T).cosupp ↔
        (p : Y') ∈ (geoTransformAlong 𝔫 T').cosupp) ∧
      (((χ p : openPreimage T U) : Y) ∈ (geoTransformAlong 𝔪 T).cosupp →
        B.toResolutionInvariant.inv 𝔫 T' p = B.toResolutionInvariant.inv 𝔪 T (χ p))) := by
  set R := B.toResolutionInvariant with hRdef
  let 𝔪U := MarkedIdeal.pullback (Subtype.val : U → X) 𝔪
  let A := MarkedIdeal.pullback Φ 𝔪U
  let B' := MarkedIdeal.pullback (Subtype.val : U' → X') 𝔫
  have hU : IsInvDomain k 𝔪U := InvDomainTowerAlong.isInvDomain_pullback_val U h𝔪
  have hA : IsInvDomain k A := InvDomainTowerAlong.isInvDomain_pullback Φ hU
  have hB' : IsInvDomain k B' := InvDomainTowerAlong.isInvDomain_pullback_val U' h𝔫
  have hcanU : IsCanonical 𝔪U (R.inv 𝔪U) (restrict U T) :=
    Seq.ResolutionInvariantExt.isCanonical_restrict R h𝔪 U T hcan
  have hcanU' : IsCanonical B' (R.inv B') (restrict U' T') :=
    Seq.ResolutionInvariantExt.isCanonical_restrict R h𝔫 U' T' hcan'
  have hcanA : IsCanonical A (R.inv A) (restrict U' T') :=
    Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R hU Φ hiso hcanU
  have hTt := R.isInvValue.isGeoTestTower_of_isCanonical h𝔪 T hcan
  have hT't := R.isInvValue.isGeoTestTower_of_isCanonical h𝔫 T' hcan'
  have hTUt := R.isInvValue.isGeoTestTower_of_isCanonical hU (restrict U T) hcanU
  have hTAt := R.isInvValue.isGeoTestTower_of_isCanonical hA (restrict U' T') hcanA
  have hcosU := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict h𝔪.isWellFormed.isClosedSubmanifold_N
    h𝔪.isWellFormed.isCoherent U T hTt
  have hcosU' := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict h𝔫.isWellFormed.isClosedSubmanifold_N
    h𝔫.isWellFormed.isCoherent U' T' hT't
  have hcosA : (geoTransformAlong A (restrict U' T')).cosupp =
      χ ⁻¹' (geoTransformAlong 𝔪U (restrict U T)).cosupp :=
    IsTowerIso.cosupp_geoTransformAlong Φ hU.isWellFormed.isClosedSubmanifold_N hU.isWellFormed.isCoherent hiso hTUt
  have hcosAB : (geoTransformAlong A (restrict U' T')).cosupp = (geoTransformAlong B' (restrict U' T')).cosupp :=
    ((LocEquiv.wEquiv hEq).2 (restrict U' T')).2 hTAt
  have hiff : ((χ p : openPreimage T U) : Y) ∈ (geoTransformAlong 𝔪 T).cosupp ↔
      p ∈ (geoTransformAlong A (restrict U' T')).cosupp := by
    rw [hcosA, mem_preimage, hcosU]
    rfl
  have hiff' : p ∈ (geoTransformAlong B' (restrict U' T')).cosupp ↔ (p : Y') ∈ (geoTransformAlong 𝔫 T').cosupp := by
    rw [hcosU']
    rfl
  have hmid : p ∈ (geoTransformAlong A (restrict U' T')).cosupp ↔
      p ∈ (geoTransformAlong B' (restrict U' T')).cosupp := by
    rw [hcosAB]
  refine ⟨hiff.trans (hmid.trans hiff'), fun hp => ?_⟩
  have hpA : p ∈ (geoTransformAlong A (restrict U' T')).cosupp := hiff.mp hp
  have hpB : p ∈ (geoTransformAlong B' (restrict U' T')).cosupp := by rw [← hcosAB]; exact hpA
  have hpc : (p : Y') ∈ (geoTransformAlong 𝔫 T').cosupp := hiff'.mp hpB
  have hχU : χ p ∈ (geoTransformAlong 𝔪U (restrict U T)).cosupp := by
    rw [hcosA] at hpA
    exact hpA
  have hNA : A.N = univ := by
    change Φ ⁻¹' ((Subtype.val : U → X) ⁻¹' 𝔪.N) = univ
    rw [hN𝔪, preimage_univ, preimage_univ]
  have hNB : B'.N = univ := by
    change (Subtype.val : U' → X') ⁻¹' 𝔫.N = univ
    rw [hN𝔫, preimage_univ]
  have hEA : A.E = [] := by
    change (𝔪.E.map ((Subtype.val : U → X) ⁻¹' ·)).map (Φ ⁻¹' ·) = []
    rw [hE𝔪]
    rfl
  have hEB : B'.E = [] := by
    change 𝔫.E.map ((Subtype.val : U' → X') ⁻¹' ·) = []
    rw [hE𝔫]
    rfl
  have hval := B.classFunctorial.inv_eq A B' hA hB' hEq hd (hEA.trans hEB.symm)
    (SameCarrierDim.of_N_eq (hNA.trans hNB.symm)) (expAgree_of_nil hEA) (restrict U' T') hcanA p hpA
  rw [← R.isInvValue.restrictOpen 𝔫 h𝔫 U' T' hcan' p hpc, ← R.isInvValue.restrictOpen 𝔪 h𝔪 U T hcan (χ p) hp,
    ← hval]
  exact R.isInvValue.towerIso Φ 𝔪U hU (restrict U' T') (restrict U T) χ hiso hcanU p hχU

end Overlap

/-! ### Native records on overlaps -/

/-- **Native records, and their powers, are locally equivalent on overlaps** (given (3a-lines)): for records `𝔪` on `X`,
`𝔫` on `X'` (domain of index `k`, empty boundary) in the native state for `(W, H)`, `(W', H)`, opens `U ⊆ X`, `U' ⊆ X'` and a
biholomorphism `Φ : U' ≅ U` with `Φ⁻¹(W ∩ U) = W' ∩ U'`, and exponents `e, f ≥ 1`, the marked ideals `Φ^*((𝔪^e)|_U)` and
`(𝔫^f)|_{U'}` are `LocWPEquiv`. -/
theorem locWPEquiv_overlap_of_native (hL : NativeLineStability) {X X' : CMfd.{0} n} {𝔪 : MarkedIdeal n X}
    {𝔫 : MarkedIdeal n X'} {W : Set X} {W' : Set X'} {H : ℕ → ℕ} {k : ℕ} (h𝔪 : IsInvDomain k 𝔪) (h𝔫 : IsInvDomain k 𝔫)
    (hE𝔪 : 𝔪.E = []) (hE𝔫 : 𝔫.E = []) (hs𝔪 : NativeHSState 𝔪 W H) (hs𝔫 : NativeHSState 𝔫 W' H)
    (U : Opens X) (U' : Opens X')
    (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)
    (hW : Φ ⁻¹' ((Subtype.val : U → X) ⁻¹' W) = (Subtype.val : U' → X') ⁻¹' W') {e f : ℕ} (he : 1 ≤ e)
    (hf : 1 ≤ f) :
    LocWPEquiv (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → X) (powerMarked 𝔪 e)))
      (MarkedIdeal.pullback (Subtype.val : U' → X') (powerMarked 𝔫 f)) := by
  let A := MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
  let B' := MarkedIdeal.pullback (Subtype.val : U' → X') 𝔫
  have hU : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) :=
    InvDomainTowerAlong.isInvDomain_pullback_val U h𝔪
  have hA : IsInvDomain k A := InvDomainTowerAlong.isInvDomain_pullback Φ hU
  have hB' : IsInvDomain k B' := InvDomainTowerAlong.isInvDomain_pullback_val U' h𝔫
  have hsA : NativeHSState (X := CMfd.of (n := n) U') A ((Subtype.val : U' → X') ⁻¹' W') H := by
    rw [← hW]
    exact (hs𝔪.restrict U).pullback Φ
  have hsB : NativeHSState (X := CMfd.of (n := n) U') B' ((Subtype.val : U' → X') ⁻¹' W') H := hs𝔫.restrict U'
  have hE : B'.E = A.E := by
    change 𝔫.E.map ((Subtype.val : U' → X') ⁻¹' ·) = (𝔪.E.map ((Subtype.val : U → X) ⁻¹' ·)).map (Φ ⁻¹' ·)
    rw [hE𝔪, hE𝔫]
    rfl
  have hAB : LocWPEquiv A B' := locWPEquiv_of_nativeHSState hL hsA hsB hE
  have e1 : MarkedIdeal.pullback (Subtype.val : U → X) (powerMarked 𝔪 e) =
      powerMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) e :=
    pullback_powerMarked (M := X) (M' := CMfd.of (n := n) U) contMDiff_subtype_val 𝔪 h𝔪.isWellFormed.isCoherent e
  have e2 : MarkedIdeal.pullback Φ (powerMarked (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) e) = powerMarked A e :=
    pullback_powerMarked (M := CMfd.of (n := n) U) (M' := CMfd.of (n := n) U') Φ.contMDiff _
      hU.isWellFormed.isCoherent e
  have e3 : MarkedIdeal.pullback (Subtype.val : U' → X') (powerMarked 𝔫 f) =
      powerMarked (X := CMfd.of (n := n) U') B' f :=
    pullback_powerMarked (M := X') (M' := CMfd.of (n := n) U') contMDiff_subtype_val 𝔫 h𝔫.isWellFormed.isCoherent f
  rw [e1, e2, e3]
  exact HironakaG8LocalPower.locEquiv_pow rfl hAB hA hB' he hf

end

end Hironaka.HironakaG11PresClassTransport
