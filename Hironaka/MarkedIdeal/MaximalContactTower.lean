import Hironaka.MarkedIdeal.LocalGiraudTransform
import Hironaka.MarkedIdeal.MaximalContactBlowup
import Hironaka.MarkedIdeal.DerivativeIdealTower
import Hironaka.MarkedIdeal.HomogenizedGlueingTower

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Hypersurfaces of maximal contact along multiple test blow-ups (Giraud)

Hironaka phase H3 (TN23-ENVELOPES); blueprint `mc:strict-transform-local`, `mc:giraud-tower`
(`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005, §2.7, Lemma `le:Giraud` (from Lemma `le:Gi`):
if `u` is a tangent direction of `(𝔞, μ)` on `U`, then along every multiple test blow-up the cosupports of the
transforms lie in the strict transforms of `V(u)` over `U`.

Built on TN23's `le:Gi` (1) (`MaximalContactBlowup`: the controlled transform of a germ of `T(𝔞)` is a germ of
`T(σ^c(𝔞))`), TN3's `le:Gi` (2)–(3) on an open set (`LocalGiraudTransform`, 51249aa4 / 8051723b: the controlled
transform has multiplicity one on, and cuts out, the strict transform of `V(u) ∩ U`), and TN-CLASSICAL's
transform `geoTransformAlong` / `IsGeoTestTower`.

* `geoStrictTransform_inter_preimage`: strict transforms are local over open sets of the base.
* `exists_tangentDirection_along` (**tangent directions persist**): for `𝔪 = (X, X, E, 𝔞, μ)` with `𝔞` coherent and
  `μ ≥ 1`, a tangent direction `u` of `(𝔞, μ)` on `U`, and a multiple test blow-up `T` of `𝔪`, every point `z` over `U`
  has an open neighbourhood `O` (over `U`) with a tangent direction `w` of the transform `(𝔞_T, μ)` on `O` such that
  `V(w) ∩ O` is the strict transform of `V(u) ∩ U` along `T`, intersected with `O`.
* `cosupp_subset_strictAlong` (**Włodarczyk `le:Giraud`**): `cosupp(𝔪_T) ∩ T⁻¹(U) ⊆ (V(u) ∩ U)_T`;
  `centre_subset_strictAlong`: in particular the next centre, over `U`, lies in the strict transform.

Maximal order is not needed (in the source it only serves to provide tangent directions).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MaximalContactTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal
  IdealWeightPowers BlowupControlledTransform BlowupFunctionTransform BlowupStrictSubmanifold BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedGlueingTower

noncomputable section

/-- **Strict transforms are local over open subsets of the base**: if `A` and `B` agree on the open set `O`, their
strict transforms agree on `π⁻¹ O`. -/
theorem geoStrictTransform_inter_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {π : Y → X} (hπ : Continuous π) {O : Set X} (hO : IsOpen O) {C A B : Set X} (hAB : A ∩ O = B ∩ O) :
    geoStrictTransform π C A ∩ π ⁻¹' O = geoStrictTransform π C B ∩ π ⁻¹' O := by
  have key : ∀ {A B : Set X}, A ∩ O = B ∩ O →
      geoStrictTransform π C A ∩ π ⁻¹' O ⊆ geoStrictTransform π C B := by
    intro A B hAB y ⟨hy, hyO⟩
    have h1 : y ∈ closure (π ⁻¹' O ∩ π ⁻¹' (A \ C)) :=
      (hO.preimage hπ).inter_closure ⟨hyO, hy⟩
    refine closure_mono ?_ h1
    rintro x ⟨hxO, hxA, hxC⟩
    have : π x ∈ B ∩ O := hAB ▸ ⟨hxA, hxO⟩
    exact ⟨this.1, hxC⟩
  exact Subset.antisymm (fun y hy => ⟨key hAB hy, hy.2⟩) (fun y hy => ⟨key hAB.symm hy, hy.2⟩)

section Tower

variable {n : ℕ} {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
  (hμ : 1 ≤ 𝔪.d) {U : Set X} {u : X → ℂ} (hu : MaximalContact.IsTangentDirection 𝔪.ideal 𝔪.d U u)
include hN h𝔞 hμ hu

/-- **Tangent directions persist along multiple test blow-ups** (Włodarczyk `le:Gi`, iterated): every point `z` of
the last stage over `U` has an open neighbourhood `O` over `U` carrying a tangent direction `w` of the transform
`(𝔞_T, μ)` whose zero set in `O` is the strict transform of `V(u) ∩ U` along `T`. -/
theorem exists_tangentDirection_along :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      ∀ z : Y, T.proj z ∈ U → ∃ (O : Set Y) (w : Y → ℂ), z ∈ O ∧ O ⊆ T.proj ⁻¹' U ∧
        MaximalContact.IsTangentDirection (geoTransformAlong 𝔪 T).ideal 𝔪.d O w ∧
        ∀ y ∈ O, (w y = 0 ↔ y ∈ strictAlong T ({x | u x = 0} ∩ U))
  | _, .refl, _, z, hz => ⟨U, u, hz, fun _ hy => hy, hu, fun y hy =>
      ⟨fun h0 => ⟨h0, hy⟩, fun h => h.1⟩⟩
  | _, .step T C π hπ, hT, z', hz' => by
      obtain ⟨hT0, hC⟩ := hT
      obtain ⟨-, hNT, -, -, hcoh, -, -⟩ :=
        DerivativeIdealTower.inclusions_tower 𝔪 hN h𝔞 (Nat.zero_le _) T hT0
      have hd : (geoTransformAlong 𝔪 T).d = 𝔪.d := d_geoTransformAlong 𝔪 T
      obtain ⟨O, w, hzO, hOU, hw, hwA⟩ := exists_tangentDirection_along T hT0 (π z') hz'
      have hCcos : C ⊆ cosupport n univ (geoTransformAlong 𝔪 T).ideal 𝔪.d := by
        intro y hy
        have := hC.2.1 hy
        rwa [MarkedIdeal.cosupp, hNT, hd] at this
      have hhol : ∀ x g, (geoTransformAlong 𝔪 T).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
        RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg
      obtain ⟨hOo, hwhol, hw1, hCw⟩ :=
        LocalGiraudTransform.IsTangentDirection.giraud_hypotheses hhol hμ hw hCcos
      obtain ⟨Uh, h, hz'h, hh⟩ := exists_isLocalEquation hπ z'
      obtain ⟨μ', hμ'⟩ : ∃ μ', 𝔪.d = μ' + 1 := ⟨𝔪.d - 1, by omega⟩
      have hle : (geoTransformAlong 𝔪 T).ideal.Le (idealPow (vanishingIdeal (n := n) C) (μ' + 1)) := by
        rw [← hμ', ← hd]
        exact HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hNT hcoh hC
      have hwmem : ∀ x ∈ O, (iterDerivIdeal (geoTransformAlong 𝔪 T).ideal μ').mem x w := fun x hx => by
        have := hw.mem x hx
        rwa [hμ', Nat.add_sub_cancel] at this
      obtain ⟨w', hw'z, heq, -⟩ :=
        MaximalContactBlowup.exists_controlledTransform_mem_iterDerivIdeal hcoh hle hh hz'h (hwmem _ hzO)
      have hπO : ∀ᶠ y in 𝓝 z', π y ∈ O :=
        (hOo.preimage hπ.contMDiff.continuous).eventually_mem hzO
      have hev : ∀ᶠ y in 𝓝 z', (y ∈ Uh ∧ π y ∈ O) ∧ HolomorphicAt n w' y ∧
          ((w ∘ π) =ᶠ[𝓝 y] fun y => h y * w' y) :=
        ((hh.isOpen.eventually_mem hz'h).and hπO).and
          ((HolomorphicAt.eventually_holomorphicAt hw'z).and heq.eventually_nhds)
      obtain ⟨O', hO'sub, hO'o, hz'O'⟩ := mem_nhds_iff.mp hev
      have hT'ideal : (geoTransformAlong 𝔪 (.step T C π hπ)).ideal =
          controlledTransform hπ (geoTransformAlong 𝔪 T).ideal (μ' + 1) := by
        rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hNT hcoh hπ, hd, hμ']
      refine ⟨O', w', hz'O', fun y hy => hOU (hO'sub hy).1.2, ⟨hO'o, fun y hy => ?_, fun y hy hy0 => ?_⟩,
        fun y hy => ?_⟩
      · obtain ⟨⟨hyh, hyO⟩, hw'y, heqy⟩ := hO'sub hy
        have h1 := MaximalContactBlowup.mem_iterDerivIdeal_controlledTransform hcoh hle hh hyh
          (hwmem _ hyO) hw'y heqy
        rw [hT'ideal, hμ', Nat.add_sub_cancel]
        exact h1
      · obtain ⟨⟨hyh, hyO⟩, hw'y, heqy⟩ := hO'sub hy
        have hyN := (LocalGiraudTransform.mem_geoStrictTransform_iff_eq_zero_of_open hh hOo hwhol hw1 hCw
          hyh hyO hw'y heqy).mpr hy0
        exact LocalGiraudTransform.exists_chartDeriv_ne_zero_controlledTransform_of_open hh hOo hwhol hw1
          hCw hyh hyO hw'y heqy hyN
      · obtain ⟨⟨hyh, hyO⟩, hw'y, heqy⟩ := hO'sub hy
        rw [← LocalGiraudTransform.mem_geoStrictTransform_iff_eq_zero_of_open hh hOo hwhol hw1 hCw hyh hyO
          hw'y heqy, strictAlong_step]
        have hAB : ({x | w x = 0} ∩ O) ∩ O = strictAlong T ({x | u x = 0} ∩ U) ∩ O := by
          ext x
          constructor
          · rintro ⟨⟨hx0, hxO⟩, -⟩
            exact ⟨(hwA x hxO).mp hx0, hxO⟩
          · rintro ⟨hxA, hxO⟩
            exact ⟨⟨(hwA x hxO).mpr hxA, hxO⟩, hxO⟩
        have hloc := geoStrictTransform_inter_preimage (C := C) hπ.contMDiff.continuous hOo hAB
        constructor
        · intro hy'
          have : y ∈ geoStrictTransform π C ({x | w x = 0} ∩ O) ∩ π ⁻¹' O := ⟨hy', hyO⟩
          rw [hloc] at this
          exact this.1
        · intro hy'
          have : y ∈ geoStrictTransform π C (strictAlong T ({x | u x = 0} ∩ U)) ∩ π ⁻¹' O := ⟨hy', hyO⟩
          rw [← hloc] at this
          exact this.1

/-- **Włodarczyk, Lemma `le:Giraud`**: let `𝔪 = (X, X, E, 𝔞, μ)` with `𝔞` coherent and `μ ≥ 1`, and `u` a tangent
direction of `(𝔞, μ)` on `U`.  For every multiple test blow-up `T` of `𝔪`, the cosupport of the transform `𝔪_T`
over `U` lies in the strict transform of `V(u) ∩ U` along `T`. -/
theorem cosupp_subset_strictAlong {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    (geoTransformAlong 𝔪 T).cosupp ∩ T.proj ⁻¹' U ⊆ strictAlong T ({x | u x = 0} ∩ U) := by
  rintro z ⟨hzc, hzU⟩
  obtain ⟨-, hNT, -, -, hcoh, -, -⟩ := DerivativeIdealTower.inclusions_tower 𝔪 hN h𝔞 (Nat.zero_le _) T hT
  obtain ⟨O, w, hzO, -, hw, hwA⟩ := exists_tangentDirection_along 𝔪 hN h𝔞 hμ hu T hT z hzU
  have hz : z ∈ cosupport n univ (geoTransformAlong 𝔪 T).ideal 𝔪.d := by
    have := hzc
    rwa [MarkedIdeal.cosupp, hNT, d_geoTransformAlong] at this
  refine (hwA z hzO).mp ?_
  exact MaximalContact.apply_eq_zero_of_mem_cosupport
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg) hμ hz
    (hw.mem z hzO)

/-- **Admissible centres lie in the strict transform of `V(u)` over `U`** (the hypersurface of maximal contact
keeps containing the centres). -/
theorem centre_subset_strictAlong {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) {C : Set Y}
    (hC : (geoTransformAlong 𝔪 T).IsAdmissibleCentre C) :
    C ∩ T.proj ⁻¹' U ⊆ strictAlong T ({x | u x = 0} ∩ U) := fun _ hz =>
  cosupp_subset_strictAlong 𝔪 hN h𝔞 hμ hu T hT ⟨hC.2.1 hz.1, hz.2⟩

end Tower

end

end Hironaka.MaximalContactTower
