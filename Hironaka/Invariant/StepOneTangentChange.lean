/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ContactMarkedCanonical
import Hironaka.Invariant.StepOneRegime
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerSplitIso
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.Invariant.ContactStageTail
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Blowup.GlueingTrivialAction
import Hironaka.MarkedIdeal.HomogenizedGlueingAlongTower
import Hironaka.MarkedIdeal.HomogenizedGlueingLiftAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.MaximalOrderStepOneB
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1b's value under a change of tangent direction, on arbitrary open sets

The change of tangent direction in Step 1b of the Step 1 value function on the masks of two points, with hypotheses
on those masks only, not on the glueing neighbourhoods. Source: Włodarczyk 2005 (arXiv `hiron.tex`), Step 1bb: by
the Glueing Lemma `le:homo` the value does not depend on the hypersurface of maximal contact (`φ_{pu}^*(..) =
φ_{pv}^*(..)` along the resolution after the hypersurface is chosen).

In the canonical-tail theorem of Step 1 the value at a nearby point `p` is computed with the tangent direction
chosen at the base point of `p` and on the mask of `p`, while the reference point uses its own tangent direction and
mask. tail form of the glueing lifts (`BlowupTowerIsoTail.exists_isTowerIso_tail_coeffHom`) gives an isomorphism of
the tails restricted to the glueing neighbourhoods `T₀⁻¹U'`, `T₀⁻¹U` over the lift `Φ₀`; this module restricts it to
the open set `V` of the points of `W' ∩ T₀⁻¹U'` mapped into `W` by `Φ₀` and to its image, which contain every point
of the cosupport over `U' ∩ U` (fixed by `Φ₀`), and compares the two values through properties (5) and (6) of the
inductive invariant.

## Main results

* `diffeoOpens`, `isTowerIso_mem_openPreimage_iff`, **`isTowerIso_restrictOpens`** (generic): an isomorphism of towers over a
  biholomorphism `Φ` of the bases restricts to open sets `V'`, `V` of the bases with `q ∈ V' ↔ Φ q ∈ V`, over the restricted
  biholomorphism, with the restricted last-stage map;
* `pullback_pullback_of_comp` (generic): `b^*(a^*𝔫) = d^*𝔫` for `a ∘ b = d`, `𝔫` coherent;
* `exists_tail_iso_opens`: the restricted isomorphism of tails around a point of the cosupport, inside two given open sets;
  `inv_eq_of_tail_iso` (generic): values on two open sets compared through it;
* `pullback_val_restrictedCoeffHom_eq`: on an open set missing the original members, Step 1b's restricted marked ideal with the
  divisor of `𝔍` kept is the one with the original members deleted, preceded by `#𝔍.E` empty members;
* **`inv_restrictedCoeffHom_eq_of_opens`** (divisor kept and masked): the same for `(𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩
  V(u))_{T₀}})|_W` with `J̄ = 𝓒_N(𝓗_N(𝔍))` carrying the divisor of `𝔍`, for open sets `W`, `W'` meeting no original
  member; `inv_restrictedCoeffHom_eq_of_opens_disjoint` with the masks stated as disjointness.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneTangentChange

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction HomogenizedIdealAlong MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupTowerIsomorphism ResolutionInvariantExt MaxLocusLocal HomogenizedGlueingAlongTower
open HomogenizedGlueingTower (strictAlong)
open MaximalOrderStepOneB (stepOneMarked contactMarked)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Isomorphisms of towers on open sets -/

section RestrictIso

variable {X X' : CMfd.{u} n}

/-- **A biholomorphism restricted to open sets with matching points**: for `Φ : X' ≅ X` and opens `V' ⊆ X'`, `V ⊆ X` with
`q ∈ V' ↔ Φ q ∈ V`, the biholomorphism `V' ≅ V`, `q ↦ Φ q`. -/
def diffeoOpens (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (V' : Opens X') (V : Opens X)
    (h : ∀ q, q ∈ V' ↔ Φ q ∈ V) :
    CMfd.of (n := n) V' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V where
  toFun q := ⟨Φ q.1, (h q.1).mp q.2⟩
  invFun p := ⟨Φ.symm p.1, (h _).mpr (by rw [Diffeomorph.apply_symm_apply]; exact p.2)⟩
  left_inv q := Subtype.ext (Φ.symm_apply_apply q.1)
  right_inv p := Subtype.ext (Φ.apply_symm_apply p.1)
  contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk (Φ.contMDiff.comp contMDiff_subtype_val)
    fun q => (h q.1).mp q.2
  contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk (Φ.symm.contMDiff.comp contMDiff_subtype_val)
    fun p => (h _).mpr (by
      show Φ (Φ.symm p.1) ∈ V
      rw [Diffeomorph.apply_symm_apply]
      exact p.2)

@[simp] theorem coe_diffeoOpens_apply (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (V' : Opens X')
    (V : Opens X) (h : ∀ q, q ∈ V' ↔ Φ q ∈ V) (q : V') : ((diffeoOpens Φ V' V h q : V) : X) = Φ q := rfl

variable {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X} {V' : Opens X'} {V : Opens X}

/-- Along an isomorphism of towers, the open preimages of matching open sets of the bases match. -/
theorem isTowerIso_mem_openPreimage_iff {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (h : IsTowerIso Φ T' T χ)
    (hV : ∀ q, q ∈ V' ↔ Φ q ∈ V) (p : Y') : p ∈ openPreimage T' V' ↔ χ p ∈ openPreimage T V := by
  show T'.proj p ∈ V' ↔ T.proj (χ p) ∈ V
  rw [hV, h.proj_comm]

/-- **An isomorphism of towers restricts to open sets with matching points**: if `T' ≅ T` over `Φ : X' ≅ X` with last-stage
map `χ`, and `V' ⊆ X'`, `V ⊆ X` are open with `q ∈ V' ↔ Φ q ∈ V`, then `T'|_{V'} ≅ T|_V` over the restriction of `Φ`, with the
restriction of `χ` as last-stage map. -/
theorem isTowerIso_restrictOpens (hV : ∀ q, q ∈ V' ↔ Φ q ∈ V) :
    ∀ {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
      {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}, IsTowerIso Φ T' T χ →
      ∀ hV₁ : (∀ p, p ∈ openPreimage T' V' ↔ χ p ∈ openPreimage T V),
        IsTowerIso (diffeoOpens Φ V' V hV) (restrict V' T') (restrict V T)
          (diffeoOpens χ (openPreimage T' V') (openPreimage T V) hV₁) := by
  intro Y' Y T' T χ h
  induction h with
  | refl => exact fun _ => BlowupTowerSplitIso.IsTowerIso.congr_last IsTowerIso.refl fun _ => rfl
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro hV₁
    refine IsTowerIso.step (ih (isTowerIso_mem_openPreimage_iff h hV)) _ _ _ (fun p => Subtype.ext (hcomm p.1)) ?_
    ext p
    show χ p.1 ∈ C ↔ p.1 ∈ C'
    rw [← hC]
    rfl

end RestrictIso

/-! ### Pullbacks along a factorization -/

section Generic

variable {P Q Y : Type u} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [TopologicalSpace Q] [ChartedSpace (ComplexModel n) Q] [IsComplexManifold n Q]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Pullback along a composite**: for holomorphic `a : P → Y`, `b : Q → P`, `d : Q → Y` with `a ∘ b = d` and `𝔫` with
coherent ideal, `b^*(a^*𝔫) = d^*𝔫`. -/
theorem pullback_pullback_of_comp {𝔫 : MarkedIdeal n Y} (h𝔫 : 𝔫.ideal.IsCoherent) {a : P → Y} {b : Q → P} {d : Q → Y}
    (ha : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ a)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b) (h : ∀ q, a (b q) = d q) :
    MarkedIdeal.pullback b (MarkedIdeal.pullback a 𝔫) = MarkedIdeal.pullback d 𝔫 := by
  have hfun : a ∘ b = d := funext h
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
  · show b ⁻¹' (a ⁻¹' 𝔫.N) = d ⁻¹' 𝔫.N
    rw [← preimage_comp, hfun]
  · show (𝔫.E.map (a ⁻¹' ·)).map (b ⁻¹' ·) = 𝔫.E.map (d ⁻¹' ·)
    rw [List.map_map]
    refine List.map_congr_left fun S _ => ?_
    show b ⁻¹' (a ⁻¹' S) = d ⁻¹' S
    rw [← preimage_comp, hfun]
  · show GermIdeal.pullback (m := n) b (GermIdeal.pullback (m := n) a 𝔫.ideal) = GermIdeal.pullback (m := n) d 𝔫.ideal
    rw [← GermIdealTotalTransform.pullback_comp ha hb h𝔫, hfun]

/-- **Pullback of empty members put in front**: `ψ^*` of `𝔪` with `k` empty members prepended to its divisor is `ψ^*𝔪` with
`k` empty members prepended. -/
theorem pullback_replicate_empty (ψ : Q → Y) (𝔪 : MarkedIdeal n Y) (k : ℕ) :
    MarkedIdeal.pullback ψ ({ 𝔪 with E := List.replicate k ∅ ++ 𝔪.E } : MarkedIdeal n Y) =
      { MarkedIdeal.pullback ψ 𝔪 with E := List.replicate k ∅ ++ (MarkedIdeal.pullback ψ 𝔪).E } := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
  show (List.replicate k ∅ ++ 𝔪.E).map (ψ ⁻¹' ·) = List.replicate k ∅ ++ 𝔪.E.map (ψ ⁻¹' ·)
  rw [List.map_append, List.map_replicate, preimage_empty]

end Generic

/-! ### The restricted isomorphism of tails, and the comparison of values through it -/

section Core

/-- **Values on two open sets, compared through an isomorphism of restricted tails** (properties (5) and (6)): let `𝔫u`, `𝔫v`
be marked ideals on a stage `Y` with coherent ideals, `W`, `W'` open with `𝔫u|_W`, `𝔫v|_{W'}` in the domain of `R` and
`T₁|_W`, `T₁|_{W'}` canonical segments of them, and `Vu ⊆ W`, `Vv ⊆ W'` open with an isomorphism `T₁|_{Vv} ≅ T₁|_{Vu}` over
`ψ : Vv ≅ Vu`, `ψ^*(𝔫u|_{Vu}) = 𝔫v|_{Vv}`, whose last-stage map fixes a point `z` of the two cosupports.  Then the values at
`z` agree. -/
theorem inv_eq_of_tail_iso {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
    {Y Z : CMfd.{u} n} {𝔫u 𝔫v : MarkedIdeal n Y} (hcu : 𝔫u.ideal.IsCoherent) (hcv : 𝔫v.ideal.IsCoherent)
    {W W' Vu Vv : Opens Y} (hVuW : Vu ≤ W) (hVvW' : Vv ≤ W') (T₁ : BlowupTower Y Z)
    (hdomu : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫u))
    (hcanu : IsCanonical (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫u)
      (R.inv (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫u)) (restrict W T₁))
    (hdomv : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W' → Y) 𝔫v))
    (hcanv : IsCanonical (MarkedIdeal.pullback (Subtype.val : W' → Y) 𝔫v)
      (R.inv (MarkedIdeal.pullback (Subtype.val : W' → Y) 𝔫v)) (restrict W' T₁))
    {ψ : CMfd.of (n := n) Vv ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) Vu}
    {ξ : CMfd.of (n := n) (openPreimage T₁ Vv) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T₁ Vu)}
    (hI : IsTowerIso ψ (restrict Vv T₁) (restrict Vu T₁) ξ)
    (hψS : MarkedIdeal.pullback ψ (MarkedIdeal.pullback (Subtype.val : Vu → Y) 𝔫u) =
      MarkedIdeal.pullback (Subtype.val : Vv → Y) 𝔫v)
    (z : Z) (hzu : T₁.proj z ∈ Vu) (hzv : T₁.proj z ∈ Vv) (hξ : ξ ⟨z, hzv⟩ = ⟨z, hzu⟩)
    (hcosu : (⟨z, hzu⟩ : openPreimage T₁ Vu) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : Vu → Y) 𝔫u) (restrict Vu T₁)).cosupp)
    (hcosv : (⟨z, hzv⟩ : openPreimage T₁ Vv) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : Vv → Y) 𝔫v) (restrict Vv T₁)).cosupp) :
    R.inv (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫u) (restrict W T₁) ⟨z, hVuW hzu⟩ =
      R.inv (MarkedIdeal.pullback (Subtype.val : W' → Y) 𝔫v) (restrict W' T₁) ⟨z, hVvW' hzv⟩ := by
  obtain ⟨hdomVu, hcanVu, hvalu⟩ := restrict_nestedOpens R hcu hVuW hdomu T₁ hcanu
  obtain ⟨-, -, hvalv⟩ := restrict_nestedOpens R hcv hVvW' hdomv T₁ hcanv
  have h1 := hvalu ⟨z, hzu⟩ hcosu
  have h3 := hvalv ⟨z, hzv⟩ hcosv
  have h2 := R.towerIso ψ _ hdomVu _ _ _ hI hcanVu ⟨z, hzv⟩ (by rw [hξ]; exact hcosu)
  rw [hξ, hψS] at h2
  rw [← h1, ← h2, h3]

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The restricted isomorphism of tails** (the glueing lifts on two given open sets): for tangent directions `u` on
`U₁ ∋ x`, `v` on `U₂ ∋ x` of `(𝔞|_N, μ)` at `x ∈ cosupp` there is an open `O ∋ x` such that for every multiple test blow-up
`T₀ T₁` of `J̄`, all open sets `W`, `W'` of the stage `T₀` and every point `z` of `cosupp J̄_{T₀ T₁}` over `W ∩ W' ∩ T₀⁻¹O`
there are open sets `Vu ⊆ W`, `Vv ⊆ W'` over which `z` lies, a biholomorphism `ψ : Vv ≅ Vu` and an isomorphism
`T₁|_{Vv} ≅ T₁|_{Vu}` over `ψ` whose last-stage map fixes `z`, with `ψ^*(contactMarked N 𝔞 μ u T₀ Vu) =
contactMarked N 𝔞 μ v T₀ Vv`. -/
theorem exists_tail_iso_opens {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) {x : M} (hx : x ∈ cosupport n N 𝔞 μ) {u v : M → ℂ} {U₁ U₂ : Set M}
    (hu : IsTangentDirectionAlong N 𝔞 μ U₁ u) (hxU₁ : x ∈ U₁)
    (hv : IsTangentDirectionAlong N 𝔞 μ U₂ v) (hxU₂ : x ∈ U₂) :
    ∃ O : Opens M, x ∈ O ∧ ∀ {Y Z : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y) (T₁ : BlowupTower Y Z),
      IsGeoTestTower (stepOneMarked N 𝔞 μ) (T₀.append T₁) →
      ∀ (W W' : Opens Y) (z : Z), T₁.proj z ∈ W → T₁.proj z ∈ W' → T₀.proj (T₁.proj z) ∈ O →
        z ∈ (geoTransformAlong (stepOneMarked N 𝔞 μ) (T₀.append T₁)).cosupp →
        ∃ (Vu Vv : Opens Y) (hzu : T₁.proj z ∈ Vu) (hzv : T₁.proj z ∈ Vv)
          (ψ : CMfd.of (n := n) Vv ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) Vu)
          (ξ : CMfd.of (n := n) (openPreimage T₁ Vv) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
            CMfd.of (n := n) (openPreimage T₁ Vu)),
          Vu ≤ W ∧ Vv ≤ W' ∧ IsTowerIso ψ (restrict Vv T₁) (restrict Vu T₁) ξ ∧ ξ ⟨z, hzv⟩ = ⟨z, hzu⟩ ∧
            MarkedIdeal.pullback ψ (contactMarked N 𝔞 μ u T₀ Vu) = contactMarked N 𝔞 μ v T₀ Vv := by
  obtain ⟨G, hxW, htriv⟩ := HomogenizedGlueingLiftAlong.exists_glueingDataAlong_trivial h𝔞 hN hμ hx hu hxU₁ hv hxU₂
  obtain ⟨hxd, hxc⟩ := G.mem_dom_and_mem_cod hxW hx
  refine ⟨G.dom ⊓ G.cod, ⟨hxd, hxc⟩, ?_⟩
  intro Y Z T₀ T₁ hT W W' z hzW hzW' hzO hzcos
  -- the full-stage marked ideals and their coherence
  have hT₀ : IsGeoTestTower (stepOneMarked N 𝔞 μ) T₀ := ((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1
  obtain ⟨hJN, hJc, -⟩ := ContactIndependenceAlong.coeffHom_basic (μ := μ) h𝔞 hN
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T₀ hT₀
  set D : Opens Y := openPreimage T₀ G.dom with hDdef
  set C : Opens Y := openPreimage T₀ G.cod with hCdef
  set 𝔫u : MarkedIdeal n Y := withN (coeffMarkedAlong (geoTransformAlong (stepOneMarked N 𝔞 μ) T₀))
    (strictAlong T₀ (N ∩ {x | u x = 0})) with h𝔫udef
  set 𝔫v : MarkedIdeal n Y := withN (coeffMarkedAlong (geoTransformAlong (stepOneMarked N 𝔞 μ) T₀))
    (strictAlong T₀ (N ∩ {x | v x = 0})) with h𝔫vdef
  have hcu : 𝔫u.ideal.IsCoherent := isCoherent_coeffMarkedAlong hcT hNT
  have hcv : 𝔫v.ideal.IsCoherent := isCoherent_coeffMarkedAlong hcT hNT
  obtain ⟨Φ₀, χ, -, -, hχ, -, hS₀', -, -, hfix⟩ :=
    BlowupTowerIsoTail.exists_isTowerIso_tail_coeffHom G h𝔞 hN hμ htriv T₀ T₁ hT
  have hS₀ : MarkedIdeal.pullback Φ₀ (MarkedIdeal.pullback (Subtype.val : C → Y) 𝔫u) =
      MarkedIdeal.pullback (Subtype.val : D → Y) 𝔫v := hS₀'
  -- the image of `z` at the stage `T₀` is fixed by `Φ₀`
  set z₀ : Y := T₁.proj z with hz₀def
  have hz₀D : z₀ ∈ D := hzO.1
  have hz₀C : z₀ ∈ C := hzO.2
  have hχz : (χ ⟨z, hz₀D⟩ : Z) = z := hfix ⟨z, hz₀D⟩ hzcos
  have hΦz₀ : Φ₀ ⟨z₀, hz₀D⟩ = ⟨z₀, hz₀C⟩ := by
    have h1 := hχ.proj_comm ⟨z, hz₀D⟩
    have h2 : (restrict D T₁).proj ⟨z, hz₀D⟩ = ⟨z₀, hz₀D⟩ := Subtype.ext (proj_restrict D T₁ _)
    rw [h2] at h1
    rw [h1]
    exact Subtype.ext ((proj_restrict C T₁ _).trans (congrArg T₁.proj hχz))
  -- the open sets `Vv ⊆ W' ∩ D` and `Vu = Φ₀(Vv) ⊆ W ∩ C`
  have hSv : IsOpen {d : D | (d : Y) ∈ W' ∧ ((Φ₀ d : C) : Y) ∈ W} :=
    (W'.isOpen.preimage continuous_subtype_val).inter
      (W.isOpen.preimage (continuous_subtype_val.comp Φ₀.continuous))
  have hSu : IsOpen {c : C | (c : Y) ∈ W ∧ ((Φ₀.symm c : D) : Y) ∈ W'} :=
    (W.isOpen.preimage continuous_subtype_val).inter
      (W'.isOpen.preimage (continuous_subtype_val.comp Φ₀.symm.continuous))
  let Vv : Opens Y := ⟨Subtype.val '' {d : D | (d : Y) ∈ W' ∧ ((Φ₀ d : C) : Y) ∈ W},
    D.isOpen.isOpenMap_subtype_val _ hSv⟩
  let Vu : Opens Y := ⟨Subtype.val '' {c : C | (c : Y) ∈ W ∧ ((Φ₀.symm c : D) : Y) ∈ W'},
    C.isOpen.isOpenMap_subtype_val _ hSu⟩
  have hmemVv : ∀ d : D, (d : Y) ∈ Vv ↔ (d : Y) ∈ W' ∧ ((Φ₀ d : C) : Y) ∈ W := fun d =>
    ⟨fun ⟨d', hd', he⟩ => (Subtype.ext he : d' = d) ▸ hd', fun hd => ⟨d, hd, rfl⟩⟩
  have hmemVu : ∀ c : C, (c : Y) ∈ Vu ↔ (c : Y) ∈ W ∧ ((Φ₀.symm c : D) : Y) ∈ W' := fun c =>
    ⟨fun ⟨c', hc', he⟩ => (Subtype.ext he : c' = c) ▸ hc', fun hc => ⟨c, hc, rfl⟩⟩
  have hVvD : Vv ≤ D := by
    rintro y ⟨d, -, rfl⟩
    exact d.2
  have hVuC : Vu ≤ C := by
    rintro y ⟨c, -, rfl⟩
    exact c.2
  have hVvW' : Vv ≤ W' := by
    rintro y ⟨d, hd, rfl⟩
    exact hd.1
  have hVuW : Vu ≤ W := by
    rintro y ⟨c, hc, rfl⟩
    exact hc.1
  have hmatch : ∀ d : D, d ∈ nestedOpens D Vv ↔ Φ₀ d ∈ nestedOpens C Vu := by
    intro d
    show (d : Y) ∈ Vv ↔ ((Φ₀ d : C) : Y) ∈ Vu
    rw [hmemVv, hmemVu, Diffeomorph.symm_apply_apply]
    exact and_comm
  have hz₀Vv : z₀ ∈ Vv := (hmemVv ⟨z₀, hz₀D⟩).mpr ⟨hzW', by rw [hΦz₀]; exact hzW⟩
  have hz₀Vu : z₀ ∈ Vu := by
    refine (hmemVu ⟨z₀, hz₀C⟩).mpr ⟨hzW, ?_⟩
    rw [← hΦz₀, Diffeomorph.symm_apply_apply]
    exact hzW'
  -- the isomorphism of the restricted tails over `ψ : Vv ≅ Vu`
  have hI := ((isTowerIso_restrict_nestedOpens (X := Y) hVvD T₁).symm.trans
    (isTowerIso_restrictOpens hmatch hχ (isTowerIso_mem_openPreimage_iff hχ hmatch))).trans
    (isTowerIso_restrict_nestedOpens (X := Y) hVuC T₁)
  let ψ : CMfd.of (n := n) Vv ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) Vu :=
    ((nestedOpensDiffeo (n := n) hVvD).symm.trans
      (diffeoOpens Φ₀ (nestedOpens D Vv) (nestedOpens C Vu) hmatch)).trans (nestedOpensDiffeo (n := n) hVuC)
  refine ⟨Vu, Vv, hz₀Vu, hz₀Vv, ψ, _, hVuW, hVvW', hI, Subtype.ext hχz, ?_⟩
  -- `ψ^* 𝓢_u|_{Vu} = 𝓢_v|_{Vv}`
  have hι : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun y : Vv => (⟨(y : Y), hVvD y.2⟩ : D)) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val fun y => hVvD y.2
  have hκ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun y : Vu => (⟨(y : Y), hVuC y.2⟩ : C)) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val fun y => hVuC y.2
  have hpullC : (MarkedIdeal.pullback (Subtype.val : C → Y) 𝔫u).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcu
  have e1 : MarkedIdeal.pullback (fun y : Vu => (⟨(y : Y), hVuC y.2⟩ : C))
      (MarkedIdeal.pullback (Subtype.val : C → Y) 𝔫u) = MarkedIdeal.pullback (Subtype.val : Vu → Y) 𝔫u :=
    pullback_pullback_of_comp hcu contMDiff_subtype_val hκ fun _ => rfl
  have e3 : MarkedIdeal.pullback (fun y : Vv => (⟨(y : Y), hVvD y.2⟩ : D))
      (MarkedIdeal.pullback (Subtype.val : D → Y) 𝔫v) = MarkedIdeal.pullback (Subtype.val : Vv → Y) 𝔫v :=
    pullback_pullback_of_comp hcv contMDiff_subtype_val hι fun _ => rfl
  show MarkedIdeal.pullback ψ (MarkedIdeal.pullback (Subtype.val : Vu → Y) 𝔫u) =
    MarkedIdeal.pullback (Subtype.val : Vv → Y) 𝔫v
  rw [← e1, pullback_pullback_of_comp hpullC hκ ψ.contMDiff
      (d := fun y : Vv => Φ₀ ⟨(y : Y), hVvD y.2⟩) fun _ => rfl,
    ← pullback_pullback_of_comp hpullC Φ₀.contMDiff hι fun _ => rfl, hS₀, e3]

end Core

/-! ### The change of tangent direction: the divisor kept and masked -/

section TangentChangeKept

variable {X : CMfd.{u} n}

/-- **Step 1b's restricted marked ideal with the divisor kept, on an open set missing the original members**: if no point of
the open `W` of the stage `T₀` lies on the first `#𝔍.E` members of the divisor of `J̄_{T₀}` (`J̄ = 𝓒_N(𝓗_N(𝔍))`, the strict
transforms of the original members), then `(𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(w))_{T₀}})|_W` is `contactMarked 𝔍.N 𝔍.ideal 𝔍.d w T₀ W`
(the original members deleted) with `#𝔍.E` empty members put in front of its divisor. -/
theorem pullback_val_restrictedCoeffHom_eq (𝔍 : MarkedIdeal n X) {Y : CMfd.{u} n} (T₀ : BlowupTower X Y) (w : X → ℂ)
    (W : Opens Y) (hmask : ∀ H ∈ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).E.take 𝔍.E.length,
      ∀ y ∈ W, y ∉ H) :
    MarkedIdeal.pullback (Subtype.val : W → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | w x = 0}))) =
      { contactMarked 𝔍.N 𝔍.ideal 𝔍.d w T₀ W with
        E := List.replicate 𝔍.E.length ∅ ++ (contactMarked 𝔍.N 𝔍.ideal 𝔍.d w T₀ W).E } := by
  set G := geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀ with hGdef
  have hdrop : geoTransformAlong (stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d) T₀ = { G with E := G.E.drop 𝔍.E.length } :=
    StepOneRegime.geoTransformAlong_coeffHom_dropE 𝔍 T₀
  have hlen : 𝔍.E.length ≤ G.E.length := by
    rw [hGdef, length_E_geoTransformAlong]
    show 𝔍.E.length ≤ 𝔍.E.length + T₀.length
    omega
  have htake : (G.E.take 𝔍.E.length).map ((Subtype.val : W → Y) ⁻¹' ·) = List.replicate 𝔍.E.length ∅ := by
    refine List.eq_replicate_iff.mpr ⟨by rw [List.length_map, List.length_take]; omega, fun S hS => ?_⟩
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hS
    exact eq_empty_iff_forall_notMem.mpr fun y hy => hmask H hH y y.2 hy
  unfold contactMarked
  rw [hdrop]
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
  show G.E.map ((Subtype.val : W → Y) ⁻¹' ·) =
    List.replicate 𝔍.E.length ∅ ++ (G.E.drop 𝔍.E.length).map ((Subtype.val : W → Y) ⁻¹' ·)
  rw [← htake, ← List.map_append, List.take_append_drop]

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Step 1b's value does not depend on the tangent direction, on arbitrary open sets, with the divisor kept and masked**
(the form for the Step 1bb lower marked ideal `(𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(w))_{T₀}})|_W`, `J̄ = 𝓒_N(𝓗_N(𝔍))` carrying the
divisor of `𝔍`, on masks missing the original members): let `𝔍` have coherent ideal, `N` a closed submanifold and `d ≥ 1`, and
`u` on `U₁ ∋ x`, `v` on `U₂ ∋ x` tangent directions of `(𝔍.ideal|_N, d)` at a point `x` of the cosupport.  There is an open
`O ∋ x` such that for every multiple test blow-up `T₀ T₁` of `J̄` and all open sets `W ⊆ T₀⁻¹U₁`, `W' ⊆ T₀⁻¹U₂` of the stage
`T₀` meeting none of the first `#𝔍.E` members of `E_{T₀}`: if the two restricted marked ideals lie in the domain of `R` and the
restrictions of `T₁` to `W`, `W'` are canonical segments of them, then at every point of `cosupp J̄_{T₀ T₁}` over
`W ∩ W' ∩ T₀⁻¹O` the two values agree. -/
theorem inv_restrictedCoeffHom_eq_of_opens (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X)
    (h𝔞 : 𝔍.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔍.N) (hd : 1 ≤ 𝔍.d) {x : X}
    (hx : x ∈ cosupport n 𝔍.N 𝔍.ideal 𝔍.d) {u v : X → ℂ} {U₁ U₂ : Set X}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U₁ u) (hxU₁ : x ∈ U₁)
    (hv : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U₂ v) (hxU₂ : x ∈ U₂) :
    ∃ O : Opens X, x ∈ O ∧ ∀ {Y Z : CMfd.{u} n} (T₀ : BlowupTower X Y) (T₁ : BlowupTower Y Z),
      IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T₁) →
      ∀ (W W' : Opens Y), (W : Set Y) ⊆ T₀.proj ⁻¹' U₁ → (W' : Set Y) ⊆ T₀.proj ⁻¹' U₂ →
      (∀ H ∈ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).E.take 𝔍.E.length, ∀ y ∈ W, y ∉ H) →
      (∀ H ∈ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).E.take 𝔍.E.length, ∀ y ∈ W', y ∉ H) →
      IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) →
      IsCanonical (MarkedIdeal.pullback (Subtype.val : W → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}))))
        (R.inv (MarkedIdeal.pullback (Subtype.val : W → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}))))) (restrict W T₁) →
      IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W' → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | v x = 0})))) →
      IsCanonical (MarkedIdeal.pullback (Subtype.val : W' → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | v x = 0}))))
        (R.inv (MarkedIdeal.pullback (Subtype.val : W' → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | v x = 0}))))) (restrict W' T₁) →
      ∀ (p : openPreimage T₁ W) (q : openPreimage T₁ W'), (p : Z) = q → T₀.proj (T₁.proj p) ∈ O →
        (p : Z) ∈ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T₁)).cosupp →
        R.inv (MarkedIdeal.pullback (Subtype.val : W → Y)
            (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
              (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) (restrict W T₁) p =
          R.inv (MarkedIdeal.pullback (Subtype.val : W' → Y)
            (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
              (strictAlong T₀ (𝔍.N ∩ {x | v x = 0})))) (restrict W' T₁) q := by
  obtain ⟨O, hxO, hO⟩ := exists_tail_iso_opens (M := X) h𝔞 hN hd hx hu hxU₁ hv hxU₂
  refine ⟨O, hxO, ?_⟩
  intro Y Z T₀ T₁ hT W W' hWU hW'U hmW hmW' hdomu hcanu hdomv hcanv p q hpq hpO hpcos
  have hT' : IsGeoTestTower (stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d) (T₀.append T₁) :=
    StepOneRegime.isGeoTestTower_stepOneMarked_of_coeffHom 𝔍 _ hT
  have hpcos' : (p : Z) ∈ (geoTransformAlong (stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d) (T₀.append T₁)).cosupp := by
    rw [StepOneRegime.cosupp_geoTransformAlong_stepOneMarked]
    exact hpcos
  have hzW' : T₁.proj (p : Z) ∈ W' := by
    rw [hpq]
    exact q.2
  obtain ⟨Vu, Vv, hzu, hzv, ψ, ξ, hVuW, hVvW', hI, hξ, hψS⟩ := hO T₀ T₁ hT' W W' p p.2 hzW' hpO hpcos'
  have hT₀ : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀ := ((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T₀ hT₀
  -- `ψ^*` of the kept form on `Vu` is the kept form on `Vv` (both miss the original members)
  have hψS' : MarkedIdeal.pullback ψ (MarkedIdeal.pullback (Subtype.val : Vu → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) =
      MarkedIdeal.pullback (Subtype.val : Vv → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | v x = 0}))) := by
    rw [pullback_val_restrictedCoeffHom_eq 𝔍 T₀ u Vu fun H hH y hy => hmW H hH y (hVuW hy),
      pullback_val_restrictedCoeffHom_eq 𝔍 T₀ v Vv fun H hH y hy => hmW' H hH y (hVvW' hy),
      pullback_replicate_empty, hψS]
  have hcosu : (⟨(p : Z), hzu⟩ : openPreimage T₁ Vu) ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : Vu → Y)
      (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
        (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) (restrict Vu T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 hN h𝔞 hd ⟨U₁, hu.isOpen⟩ hu T₀ T₁ hT Vu
      fun y hy => hWU (hVuW hy)).2]
    exact hpcos
  have hcosv : (⟨(p : Z), hzv⟩ : openPreimage T₁ Vv) ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : Vv → Y)
      (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
        (strictAlong T₀ (𝔍.N ∩ {x | v x = 0})))) (restrict Vv T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 hN h𝔞 hd ⟨U₂, hv.isOpen⟩ hv T₀ T₁ hT Vv
      fun y hy => hW'U (hVvW' hy)).2]
    exact hpcos
  have key := inv_eq_of_tail_iso R
    (𝔫u := withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
      (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))
    (𝔫v := withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
      (strictAlong T₀ (𝔍.N ∩ {x | v x = 0})))
    (isCoherent_coeffMarkedAlong hcT hNT) (isCoherent_coeffMarkedAlong hcT hNT)
    hVuW hVvW' T₁ hdomu hcanu hdomv hcanv hI hψS' (p : Z) hzu hzv hξ hcosu hcosv
  have hp : (⟨(p : Z), hVuW hzu⟩ : openPreimage T₁ W) = p := rfl
  have hq : (⟨(p : Z), hVvW' hzv⟩ : openPreimage T₁ W') = q := Subtype.ext hpq
  rw [hp, hq] at key
  exact key

/-- **`inv_restrictedCoeffHom_eq_of_opens` with the masks stated as disjointness**: the open sets `W`, `W'` are
disjoint from the first `#𝔍.E` members of `E_{T₀}`. -/
theorem inv_restrictedCoeffHom_eq_of_opens_disjoint (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X)
    (h𝔞 : 𝔍.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔍.N) (hd : 1 ≤ 𝔍.d) {x : X}
    (hx : x ∈ cosupport n 𝔍.N 𝔍.ideal 𝔍.d) {u v : X → ℂ} {U₁ U₂ : Set X}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U₁ u) (hxU₁ : x ∈ U₁)
    (hv : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U₂ v) (hxU₂ : x ∈ U₂) :
    ∃ O : Opens X, x ∈ O ∧ ∀ {Y Z : CMfd.{u} n} (T₀ : BlowupTower X Y) (T₁ : BlowupTower Y Z),
      IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T₁) →
      ∀ (W W' : Opens Y), (W : Set Y) ⊆ T₀.proj ⁻¹' U₁ → (W' : Set Y) ⊆ T₀.proj ⁻¹' U₂ →
      (∀ H ∈ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).E.take 𝔍.E.length, Disjoint (W : Set Y) H) →
      (∀ H ∈ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).E.take 𝔍.E.length, Disjoint (W' : Set Y) H) →
      IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) →
      IsCanonical (MarkedIdeal.pullback (Subtype.val : W → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}))))
        (R.inv (MarkedIdeal.pullback (Subtype.val : W → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}))))) (restrict W T₁) →
      IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W' → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | v x = 0})))) →
      IsCanonical (MarkedIdeal.pullback (Subtype.val : W' → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | v x = 0}))))
        (R.inv (MarkedIdeal.pullback (Subtype.val : W' → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | v x = 0}))))) (restrict W' T₁) →
      ∀ (p : openPreimage T₁ W) (q : openPreimage T₁ W'), (p : Z) = q → T₀.proj (T₁.proj p) ∈ O →
        (p : Z) ∈ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T₁)).cosupp →
        R.inv (MarkedIdeal.pullback (Subtype.val : W → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) (restrict W T₁) p =
          R.inv (MarkedIdeal.pullback (Subtype.val : W' → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | v x = 0})))) (restrict W' T₁) q := by
  obtain ⟨O, hxO, hO⟩ := inv_restrictedCoeffHom_eq_of_opens R 𝔍 h𝔞 hN hd hx hu hxU₁ hv hxU₂
  exact ⟨O, hxO, fun T₀ T₁ hT W W' hWU hW'U hmW hmW' => hO T₀ T₁ hT W W' hWU hW'U
    (fun H hH y hy => Set.disjoint_left.mp (hmW H hH) hy) (fun H hH y hy => Set.disjoint_left.mp (hmW' H hH) hy)⟩

end TangentChangeKept

end

end Hironaka.StepOneTangentChange
