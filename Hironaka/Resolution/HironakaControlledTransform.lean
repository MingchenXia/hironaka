import Hironaka.Resolution.HironakaPrincipalizationBoundary
import Hironaka.Resolution.FactorizationFromResolution

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Controlled transforms with mark one, and relative principalization in two stages (Hironaka, design lemmas)

Blueprint `hir:h5a-controlled-transform`, `hir:h5a-first-stage`, `hir:h5a-second-stage`, `hir:h5a-assembly`
(`blueprint/src/hironaka.tex`; TN.5, the remaining open Hironaka design lemmas, formalized as stated).  Sources:
Bierstone--Milman 2008 (`bierstone-milman08-functoriality`) and Włodarczyk 2005 (`wlodarczyk05-hironaka`), the controlled
transform; Copy-4 (`transcendental-nakamaye-copy4-20260911`, `lem:relative-principalization`), the two stages.

**Controlled transforms.**  For a tower `T` and an ideal `𝔞` on its base, the controlled transforms are the iterated colon
ideals `𝔞^c_0 = 𝔞`, `𝔞^c_i = (σ_i^* 𝔞^c_{i-1} : 𝓘_{D_i})` with `D_i` the exceptional divisor of the `i`-th blowup
(`controlledTransformAlong`), ideals on the whole of each stage.  Along a multiple test blow-up of a well-formed marked ideal
`(M, N, E, 𝔞, 1)` with mark one they are the ideals of the transforms of the ambient marked ideal `(M, M, E, 𝔞, 1)`
(`controlledTransformAlong_eq`), which gives the statements of `hir:h5a-controlled-transform`: `σ_i^* 𝔞^c_{i-1} = 𝓘_{D_i} · 𝔞^c_i`,
`f^* 𝔞 = 𝓘_{H_r} · 𝔞^c_r`, `f^* 𝓘_N = 𝓘_{H_r} · 𝓘_{N_r}`, the restrictions of `𝔞^c_r` and of the ideal of the transform to `N_r`
agree, and `𝔞^c_r` is the unit ideal near `N_r` once the final cosupport is empty.  The two stages and the assembly of relative
principalization (`hir:h5a-first-stage`, `-second-stage`, `-assembly`) then follow from the formalized route
(`FactorizationFromResolution`), in which the ambient transform is used in place of the colon ideals.

## Main results

* `controlledTransformAlong`, `controlledTransformAlong_eq`, `pullback_controlledTransformAlong_step`,
  `pullback_controlledTransformAlong_step_of_isGeoTestTower`,
  `pullback_eq_mul_controlledTransformAlong`, `pullback_vanishingIdeal_N_eq_mul`, `mem_one_of_notMem_zeroLocus`;
* **`controlled_transform`** (`hir:h5a-controlled-transform`);
* **`first_stage`**, `exists_first_stage` (`hir:h5a-first-stage`);
* **`second_stage`**, `second_stage_of_first_stage` (`hir:h5a-second-stage`);
* **`assembly`** (`hir:h5a-assembly`).

Import discipline (standalone Hironaka library): this module imports `HironakaPrincipalizationBoundary` and
`FactorizationFromResolution` (already in its closure) only; it does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaControlledTransform

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.GermIdealOrder
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.BlowupControlledTransform Hironaka.BlowupExceptionalDivisor
  Hironaka.InvertibleIdealQuotient Hironaka.IdealWeightPowers
  Hironaka.RestrictEmptyTower Hironaka.FactorizationFromResolution
  Hironaka.HironakaAdmissibleSequence
open Hironaka.ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {n : ℕ}

/-! ### Controlled transforms as iterated colon ideals -/

section Controlled

variable {X : CMfd.{u} n}

/-- **The controlled transforms along a tower** (mark one): `𝔞^c = 𝔞` on the base and, after a blowup `π` with exceptional
divisor `D`, `(π^* 𝔞^c : 𝓘_D)`. -/
def controlledTransformAlong (𝔞 : GermIdeal n X) : {Y : CMfd.{u} n} → BlowupTower X Y → GermIdeal n Y
  | _, .refl => 𝔞
  | _, .step T _ π hπ =>
      colon (GermIdeal.pullback (m := n) π (controlledTransformAlong 𝔞 T)) (exceptionalDivisor hπ).ideal

@[simp] theorem controlledTransformAlong_refl (𝔞 : GermIdeal n X) :
    controlledTransformAlong 𝔞 (BlowupTower.refl : BlowupTower X X) = 𝔞 := rfl

theorem controlledTransformAlong_step (𝔞 : GermIdeal n X) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y)
    (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    controlledTransformAlong 𝔞 (.step T C π hπ) =
      colon (GermIdeal.pullback (m := n) π (controlledTransformAlong 𝔞 T)) (exceptionalDivisor hπ).ideal := rfl

/-- **The controlled transforms are the ideals of the ambient transforms**: along a multiple test blow-up `T` of the ambient
marked ideal `(X, X, E, 𝔞, 1)` (`𝔞` coherent), `𝔞^c_T` is the ideal of its transform. -/
theorem controlledTransformAlong_eq (𝔪 : MarkedIdeal n X) (hd : 𝔪.d = 1) (h𝔞 : 𝔪.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (ambient 𝔪) T →
      controlledTransformAlong 𝔪.ideal T = (geoTransformAlong (ambient 𝔪) T).ideal
  | _, .refl, _ => rfl
  | _, .step T C π hπ, hT => by
      obtain ⟨hTT, -⟩ := (isGeoTestTower_step_iff (ambient 𝔪) T C π hπ).mp hT
      obtain ⟨hNT, hcohT, -⟩ := pullback_eq_mul_geoTransformAlong (ambient 𝔪) rfl h𝔞 T hTT
      have ih := controlledTransformAlong_eq 𝔪 hd h𝔞 T hTT
      rw [controlledTransformAlong_step, ih, geoTransformAlong_step,
        geoTransform_ideal_eq_controlledTransform hNT hcohT hπ, d_geoTransformAlong, ambient_d, hd]
      show _ = colon _ (idealPow (exceptionalDivisor hπ).ideal 1)
      rw [idealPow_one_of_isCoherent (isCoherent_ideal (exceptionalDivisor hπ))]

/-- **One blowup: `σ^* 𝔞^c_{i-1} = 𝓘_D · 𝔞^c_i`** along a multiple test blow-up of `(X, X, E, 𝔞, 1)` (the centre lies in the
zero locus of `𝔞^c_{i-1}`, the Hadamard bridge, and the cancellation of the principal ideal of `D`). -/
theorem pullback_controlledTransformAlong_step (𝔪 : MarkedIdeal n X) (hd : 𝔪.d = 1) (h𝔞 : 𝔪.ideal.IsCoherent)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower (ambient 𝔪) (.step T C π hπ)) :
    GermIdeal.pullback (m := n) π (controlledTransformAlong 𝔪.ideal T) =
      (exceptionalDivisor hπ).ideal.mul (controlledTransformAlong 𝔪.ideal (.step T C π hπ)) := by
  obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff (ambient 𝔪) T C π hπ).mp hT
  obtain ⟨hNT, hcohT, -⟩ := pullback_eq_mul_geoTransformAlong (ambient 𝔪) rfl h𝔞 T hTT
  have hdT : (geoTransformAlong (ambient 𝔪) T).d = 1 := by rw [d_geoTransformAlong, ambient_d, hd]
  have hsub : C ⊆ cosupport n univ (geoTransformAlong (ambient 𝔪) T).ideal 1 := by
    have h := hC.2.1
    rw [MarkedIdeal.cosupp, hNT, hdT] at h
    exact h
  have hpb := HadamardBridge.pullback_eq_mul_controlledTransform_of_subset_cosupport hπ hcohT hsub
  rw [idealPow_one_of_isCoherent (isCoherent_ideal (exceptionalDivisor hπ))] at hpb
  rw [controlledTransformAlong_eq 𝔪 hd h𝔞 T hTT, controlledTransformAlong_eq 𝔪 hd h𝔞 _ hT, geoTransformAlong_step,
    geoTransform_ideal_eq_controlledTransform hNT hcohT hπ, hdT]
  exact hpb

/-- **`f^* 𝔞 = 𝓘_{H_r} · 𝔞^c_r`** along a multiple test blow-up of `(X, X, E, 𝔞, 1)`, `H_r` the exceptional divisor of the
tower. -/
theorem pullback_eq_mul_controlledTransformAlong (𝔪 : MarkedIdeal n X) (hd : 𝔪.d = 1) (h𝔞 : 𝔪.ideal.IsCoherent)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (ambient 𝔪) T) :
    GermIdeal.pullback (m := n) T.proj 𝔪.ideal =
      (BlowupTowerTransforms.exceptionalDivisor T).ideal.mul (controlledTransformAlong 𝔪.ideal T) := by
  obtain ⟨-, -, hpb⟩ := pullback_eq_mul_geoTransformAlong (ambient 𝔪) rfl h𝔞 T hT
  rw [controlledTransformAlong_eq 𝔪 hd h𝔞 T hT, ← idealPow_one_of_isCoherent (isCoherent_ideal
    (BlowupTowerTransforms.exceptionalDivisor T))]
  rw [ambient_d, hd] at hpb
  exact hpb

/-- **`f^* 𝓘_N = 𝓘_{H_r} · 𝓘_{N_r}`** along a multiple test blow-up of a marked ideal whose `N` is a closed submanifold and whose
ideal is coherent (each centre lies in the current `N`; the blowup of a submanifold along a submanifold of it). -/
theorem pullback_vanishingIdeal_N_eq_mul (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
      GermIdeal.pullback (m := n) T.proj (vanishingIdeal (n := n) 𝔪.N) =
        (BlowupTowerTransforms.exceptionalDivisor T).ideal.mul (vanishingIdeal (n := n) (geoTransformAlong 𝔪 T).N)
  | _, .refl, _ => by
      rw [BlowupTowerTransforms.exceptionalDivisor_refl_ideal, BlowupTower.proj_refl, geoTransformAlong_refl,
        unitIdeal_mul (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)]
      exact BlowupControlledTransform.pullback_id (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
  | _, .step T C π hπ, hT => by
      obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      have ih := pullback_vanishingIdeal_N_eq_mul 𝔪 hN h𝔞 T hTT
      obtain ⟨hNT, -⟩ := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hTT
      obtain ⟨hNT', -⟩ := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 _ hT
      have hN'eq : (geoTransformAlong 𝔪 (.step T C π hπ)).N =
          BlowupStrictSubmanifold.geoStrictTransform π C (geoTransformAlong 𝔪 T).N := rfl
      rw [hN'eq] at hNT' ⊢
      exact GermIdealTotalTransform.pullback_comp_eq_mul T.contMDiff_proj hπ.contMDiff
        (interior_exceptionalLocus_eq_empty hπ) (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
        (VanishingIdealCoherent.isCoherent_vanishingIdeal hNT)
        (VanishingIdealCoherent.isCoherent_vanishingIdeal hNT') (BlowupTowerTransforms.exceptionalDivisor T)
        (exceptionalDivisor hπ) ih (BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul hπ hNT hC.subset_N)

end Controlled

/-- **A coherent ideal contains `1` at every point off its zero locus**: some germ `b` of it does not vanish at the point, and
`1 = b⁻¹ · b`. -/
theorem mem_one_of_notMem_zeroLocus {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) {x : M} (hx : x ∉ 𝔟.zeroLocus) :
    𝔟.mem x (fun _ => (1 : ℂ)) := by
  obtain ⟨b, hb, hbx⟩ : ∃ b, 𝔟.mem x b ∧ b x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx hcon
  have hbhol : HolomorphicAt n b x := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hb
  have hinv : HolomorphicAt n (fun y => (b y)⁻¹) x := RelativePrincipalizationSpan.holomorphicAt_inv hbhol hbx
  refine GermIdealTotalTransform.mem_of_isInSpanAt_mem h𝔟
    (isInSpanAt_of_eq_mul hb (holomorphicAt_const 1) hinv ?_)
  filter_upwards [hbhol.continuousAt.eventually_ne hbx] with y hy
  show (1 : ℂ) = (b y)⁻¹ * b y
  field_simp

/-! ### `hir:h5a-controlled-transform` -/

section Lemma

variable {X : CMfd.{u} n}

/-- **The controlled transform with mark one** (`hir:h5a-controlled-transform`): let `𝔪 = (M, N, E, 𝔞, 1)` be well formed and
`T` a multiple test blow-up of it, with controlled transforms `𝔞^c_i` and exceptional divisor `H_r = E_T` of the composite
`f`.  Then `T` is a multiple test blow-up of `(M, M, E, 𝔞, 1)`, `f^* 𝔞 = 𝓘_{H_r} · 𝔞^c_r`, `f^* 𝓘_N = 𝓘_{H_r} · 𝓘_{N_r}`; the
restrictions to `N_r` of `𝔞^c_r` and of the ideal `𝔞_r` of `𝔪_T` agree; and if `cosupp 𝔪_T = ∅`, then `𝔞^c_r` is the unit
ideal on an open neighbourhood of `N_r`.  (The one-blowup identities `σ_i^* 𝔞^c_{i-1} = 𝓘_{D_i} · 𝔞^c_i` are
`pullback_controlledTransformAlong_step`, for every prefix of `T`.) -/
theorem controlled_transform (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed) (hd : 𝔪.d = 1) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    IsGeoTestTower (ambient 𝔪) T ∧
      GermIdeal.pullback (m := n) T.proj 𝔪.ideal =
        (BlowupTowerTransforms.exceptionalDivisor T).ideal.mul (controlledTransformAlong 𝔪.ideal T) ∧
      GermIdeal.pullback (m := n) T.proj (vanishingIdeal (n := n) 𝔪.N) =
        (BlowupTowerTransforms.exceptionalDivisor T).ideal.mul (vanishingIdeal (n := n) (geoTransformAlong 𝔪 T).N) ∧
      RestrictedIdealWeight.RestrictLe (geoTransformAlong 𝔪 T).N (controlledTransformAlong 𝔪.ideal T) (geoTransformAlong 𝔪 T).ideal ∧
      RestrictedIdealWeight.RestrictLe (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (controlledTransformAlong 𝔪.ideal T) ∧
      ((geoTransformAlong 𝔪 T).cosupp = ∅ →
        ∃ U : Set Y, IsOpen U ∧ (geoTransformAlong 𝔪 T).N ⊆ U ∧
          ∀ y ∈ U, (controlledTransformAlong 𝔪.ideal T).mem y (fun _ => (1 : ℂ))) := by
  have hN := h𝔪.isClosedSubmanifold_N
  have h𝔞 := h𝔪.isCoherent
  obtain ⟨hT', hEq⟩ := isGeoTestTower_and_restrictEquiv hd hN h𝔞 T hT
  obtain ⟨-, hcoh'T, -⟩ := pullback_eq_mul_geoTransformAlong (ambient 𝔪) rfl h𝔞 T hT'
  have hcT := controlledTransformAlong_eq 𝔪 hd h𝔞 T hT'
  refine ⟨hT', pullback_eq_mul_controlledTransformAlong 𝔪 hd h𝔞 T hT',
    pullback_vanishingIdeal_N_eq_mul 𝔪 hN h𝔞 T hT, ?_, ?_, fun hcos => ?_⟩
  · rw [hcT]
    exact hEq.ge
  · rw [hcT]
    exact hEq.le
  · -- `N_T` misses the zero locus of the ambient transform, which is closed
    have h := cosupp_geoTransformAlong_eq hd hN h𝔞 T hT
    rw [hcos] at h
    have hZc : IsClosed (geoTransformAlong (ambient 𝔪) T).ideal.zeroLocus :=
      OrderTaylor.isClosed_zeroLocus_of_isCoherent hcoh'T
    refine ⟨((geoTransformAlong (ambient 𝔪) T).ideal.zeroLocus)ᶜ, hZc.isOpen_compl, fun y hy hyZ => ?_,
      fun y hy => ?_⟩
    · have : y ∈ (geoTransformAlong 𝔪 T).N ∩ (geoTransformAlong (ambient 𝔪) T).ideal.zeroLocus := ⟨hy, hyZ⟩
      rw [← h] at this
      exact this
    · rw [hcT]
      exact mem_one_of_notMem_zeroLocus hcoh'T hy

/-- **`σ_i^* 𝔞^c_{i-1} = 𝓘_{D_i} · 𝔞^c_i` for every step** of a multiple test blow-up of a well-formed marked ideal
`(M, N, E, 𝔞, 1)` with mark one (`hir:h5a-controlled-transform` (1)): the `i`-th step of a tower is the last step of its prefix
`.step T C π hπ`, itself a multiple test blow-up of `(M, N, E, 𝔞, 1)`. -/
theorem pullback_controlledTransformAlong_step_of_isGeoTestTower (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed)
    (hd : 𝔪.d = 1) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower 𝔪 (.step T C π hπ)) :
    GermIdeal.pullback (m := n) π (controlledTransformAlong 𝔪.ideal T) =
      (exceptionalDivisor hπ).ideal.mul (controlledTransformAlong 𝔪.ideal (.step T C π hπ)) :=
  pullback_controlledTransformAlong_step 𝔪 hd h𝔪.isCoherent T C π hπ (controlled_transform 𝔪 h𝔪 hd _ hT).1

end Lemma

/-! ### `hir:h5a-first-stage` -/

section Stages

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Relative principalization, first stage** (`hir:h5a-first-stage`): let `Y` be a compact connected complex manifold,
`W ⊊ Y` a closed connected submanifold of dimension `k` and `𝔞` a coherent ideal with `𝔞 ⊄ 𝓘_W`, and let `T_A` be a multiple test
blow-up of `(Y, W, ∅, 𝔞, 1)` with empty final cosupport, with composite `f_A`, exceptional divisor `H_A` and controlled transform
`𝔞_t = 𝔞^c`.  Then `f_A` is a sequence of blowups adapted to `W`; the strict transform `W_t` is a closed connected submanifold of
dimension `k`; `Y_t` is compact and connected; `f_A^* 𝓘_W = 𝓘_{H_A} · 𝓘_{W_t}`, `f_A^* 𝔞 = 𝓘_{H_A} · 𝔞_t`; the support of `H_A` lies
in the exceptional locus; and `𝔞_t` is coherent, the unit ideal on an open neighbourhood of `W_t`, and not the zero ideal. -/
theorem first_stage [CompactSpace Y] [ConnectedSpace Y] (W : Set Y) (k : ℕ) (hW : IsClosedConnectedSubmanifold n W k)
    (hWY : W ≠ univ) (𝔞 : GermIdeal n Y) (h𝔞 : 𝔞.IsCoherent) (hres : ¬ 𝔞.Le (vanishingIdeal (n := n) W))
    {Y₁ : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) Y) Y₁)
    (hT : IsGeoResolution (⟨W, [], 𝔞, 1⟩ : MarkedIdeal n (CMfd.of (n := n) Y)) T) :
    IsAdaptedBlowupSequence n Y W Y₁ T.proj ∧
      IsClosedConnectedSubmanifold n (strictTransform n T.proj W) k ∧
      CompactSpace Y₁ ∧ ConnectedSpace Y₁ ∧
      GermIdeal.pullback (m := n) T.proj (vanishingIdeal (n := n) W) =
        (BlowupTowerTransforms.exceptionalDivisor T).ideal.mul (vanishingIdeal (n := n) (strictTransform n T.proj W)) ∧
      GermIdeal.pullback (m := n) T.proj 𝔞 =
        (BlowupTowerTransforms.exceptionalDivisor T).ideal.mul (controlledTransformAlong 𝔞 T) ∧
      (BlowupTowerTransforms.exceptionalDivisor T).support ⊆ exceptionalLocus n T.proj ∧
      (controlledTransformAlong 𝔞 T).IsCoherent ∧
      (∃ U : Set Y₁, IsOpen U ∧ strictTransform n T.proj W ⊆ U ∧
        ∀ y ∈ U, (controlledTransformAlong 𝔞 T).mem y (fun _ => (1 : ℂ))) ∧
      ¬ (controlledTransformAlong 𝔞 T).Le (vanishingIdeal (n := n) (univ : Set Y₁)) := by
  set 𝔪 : MarkedIdeal n (CMfd.of (n := n) Y) := ⟨W, [], 𝔞, 1⟩ with h𝔪
  have : CompactSpace (CMfd.of (n := n) Y) := ‹CompactSpace Y›
  have : ConnectedSpace (CMfd.of (n := n) Y) := ‹ConnectedSpace Y›
  have hkn : k < n := lt_of_ne_univ hW hWY
  have hdom : IsInvDomain k 𝔪 := FactorizationDomain.isInvDomain_of_not_le hW le_rfl h𝔞 hres
  obtain ⟨hconn, hst, hadapt, hpb, hsupp⟩ := tower_data hdom rfl hW hkn T hT.1
  obtain ⟨hT', hpbA, -, -, -, hunit⟩ := controlled_transform 𝔪 hdom.isWellFormed rfl T hT.1
  obtain ⟨-, hcoh'T, -⟩ := pullback_eq_mul_geoTransformAlong (ambient 𝔪) rfl h𝔞 T hT'
  have hcT := controlledTransformAlong_eq 𝔪 rfl h𝔞 T hT'
  have hst' : (geoTransformAlong 𝔪 T).N = strictTransform n T.proj W := hst
  obtain ⟨U, hUo, hNU, hU⟩ := hunit hT.2
  rw [hst'] at hNU hconn hpb
  have hcoh : (controlledTransformAlong 𝔞 T).IsCoherent := by
    show (controlledTransformAlong 𝔪.ideal T).IsCoherent
    rw [hcT]
    exact hcoh'T
  refine ⟨hadapt, hconn, ResolutionDriver.compactSpace_of_tower T,
    BlowupConnected.connectedSpace_of_isBlowupSequence T.proj T.isBlowupSequence, hpb, hpbA, hsupp, hcoh,
    ⟨U, hUo, hNU, hU⟩, fun hle => ?_⟩
  obtain ⟨x, hx⟩ := hconn.2.1.nonempty
  have h1 := hU x (hNU hx)
  exact one_ne_zero ((hle x _ h1).2.self_of_nhds (mem_univ x))

/-- **The first stage exists** on a compact connected manifold: the canonical resolution of `(Y, W, ∅, 𝔞, 1)`, which lies in the
domain (`mc:factorization-domain`). -/
theorem exists_first_stage [CompactSpace Y] [ConnectedSpace Y] (W : Set Y) (k : ℕ)
    (hW : IsClosedConnectedSubmanifold n W k) (hWY : W ≠ univ) (𝔞 : GermIdeal n Y) (h𝔞 : 𝔞.IsCoherent)
    (hres : ¬ 𝔞.Le (vanishingIdeal (n := n) W)) :
    ∃ (Y₁ : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) Y) Y₁),
      IsGeoResolution (⟨W, [], 𝔞, 1⟩ : MarkedIdeal n (CMfd.of (n := n) Y)) T := by
  have : CompactSpace (CMfd.of (n := n) Y) := ‹CompactSpace Y›
  have hkn : k < n := lt_of_ne_univ hW hWY
  obtain ⟨Y₁, T, -, hres'⟩ := ResolutionInvariantSeq.exists_isGeoResolution_isCanonical
    (CanonicalCentres.canonicalInvariant.{u} n)
    (FactorizationDomain.isInvDomain_of_not_le (M := CMfd.of (n := n) Y) hW hkn.le h𝔞 hres)
  exact ⟨Y₁, T, hres'⟩

end Stages

/-! ### `hir:h5a-second-stage` -/

section Second

variable {X : CMfd.{u} n}

/-- **Relative principalization, second stage** (`hir:h5a-second-stage`, in the generality of its proof): let `𝔟` be a coherent
ideal on `X`, `A` a closed connected submanifold of dimension `k` disjoint from `Z(𝔟)` (for `𝔟 = 𝔞_t`, `A = W_t` of the first
stage: `𝔞_t` is the unit ideal near `W_t`), and `S` a multiple test blow-up of `(X, X, ∅, 𝔟, 1)` with empty final cosupport, with
composite `g` and exceptional divisor `H'`.  Then every centre of `S` lies over `Z(𝔟)`, hence misses the preimage of the open
neighbourhood `X \ Z(𝔟)` of `A`; `g` is an isomorphism over `X \ Z(𝔟)`, in particular near `A`; `g^* 𝔟 = 𝓘_{H'}`; the strict transform
`A'` of `A` is `g⁻¹ A`, a closed connected submanifold of dimension `k`; `H'` is disjoint from `A'`; and `g^* 𝓘_A = 𝓘_{A'}`. -/
theorem second_stage {𝔟 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent) {A : Set X} {k : ℕ}
    (hA : IsClosedConnectedSubmanifold n A k) (hAB : Disjoint A 𝔟.zeroLocus) {Y : CMfd.{u} n} (S : BlowupTower X Y)
    (hS : IsGeoResolution (⟨univ, [], 𝔟, 1⟩ : MarkedIdeal n X) S) :
    CentresOver 𝔟.zeroLocus S ∧
      CentresAvoid ⟨(𝔟.zeroLocus)ᶜ, (OrderTaylor.isClosed_zeroLocus_of_isCoherent h𝔟).isOpen_compl⟩ S ∧
      IsIsomorphismOver n S.proj (𝔟.zeroLocus)ᶜ ∧
      GermIdeal.pullback (m := n) S.proj 𝔟 = (BlowupTowerTransforms.exceptionalDivisor S).ideal ∧
      strictTransform n S.proj A = S.proj ⁻¹' A ∧
      IsClosedConnectedSubmanifold n (S.proj ⁻¹' A) k ∧
      Disjoint (BlowupTowerTransforms.exceptionalDivisor S).support (S.proj ⁻¹' A) ∧
      GermIdeal.pullback (m := n) S.proj (vanishingIdeal (n := n) A) = vanishingIdeal (n := n) (S.proj ⁻¹' A) := by
  set 𝔪 : MarkedIdeal n X := ⟨univ, [], 𝔟, 1⟩ with h𝔪
  obtain ⟨hconn, hst, hdisj, hpbA⟩ := second_data (𝔪 := 𝔪) rfl rfl h𝔟 hA hAB S hS.1
  have hpb : GermIdeal.pullback (m := n) S.proj 𝔟 = (BlowupTowerTransforms.exceptionalDivisor S).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution 𝔪 rfl h𝔟 rfl S hS
  have hN : IsClosedSubmanifold n 𝔪.N :=
    ⟨isClosed_univ, fun x _ => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩
  have hover : CentresOver 𝔟.zeroLocus S := by
    have h := centresOver_cosupp 𝔪 hN h𝔟 S hS.1
    rwa [cosupp_univ_one h𝔟] at h
  have hsuppZ : (BlowupTowerTransforms.exceptionalDivisor S).support = S.proj ⁻¹' 𝔟.zeroLocus := by
    rw [EffectiveDivisor.support, ← hpb, zeroLocus_pullback S.contMDiff_proj h𝔟]
  refine ⟨hover, centresAvoid_of_centresOver _ disjoint_compl_left S hover, ?_, hpb, hst, hconn, hdisj, hpbA⟩
  refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset S.isBlowupSequence ?_
  rintro x ⟨z, hz, rfl⟩
  have hz' := HironakaPrincipalization.exceptionalLocus_subset_support S hz
  rw [hsuppZ] at hz'
  exact hz'

end Second

section SecondOfFirst

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **The second stage after the first** (`hir:h5a-second-stage` as stated): let `Y`, `W`, `k`, `𝔞` and `T_A` be as in
`first_stage`, with strict transform `W_t` of `W` and controlled transform `𝔞_t`, and let `T_B` be a multiple test blow-up of
`(Y_t, Y_t, ∅, 𝔞_t, 1)` with empty final cosupport, with composite `g` and exceptional divisor `H'`.  Then `W_t` misses
`Z(𝔞_t)`; every centre of `T_B` lies over `Z(𝔞_t)` and misses the preimage of the open neighbourhood `U = Y_t \ Z(𝔞_t)` of
`W_t`, over which `g` is an isomorphism; `g^* 𝔞_t = 𝓘_{H'}`; the strict transform `W'` of `W_t` is `g⁻¹ W_t`, a closed connected
submanifold of dimension `k`; `H'` is disjoint from `W'`; and `g^* 𝓘_{W_t} = 𝓘_{W'}`. -/
theorem second_stage_of_first_stage [CompactSpace Y] [ConnectedSpace Y] (W : Set Y) (k : ℕ)
    (hW : IsClosedConnectedSubmanifold n W k) (hWY : W ≠ univ) (𝔞 : GermIdeal n Y) (h𝔞 : 𝔞.IsCoherent)
    (hres : ¬ 𝔞.Le (vanishingIdeal (n := n) W)) {Y₁ : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) Y) Y₁)
    (hT : IsGeoResolution (⟨W, [], 𝔞, 1⟩ : MarkedIdeal n (CMfd.of (n := n) Y)) T) {Y₂ : CMfd.{u} n}
    (S : BlowupTower Y₁ Y₂)
    (hS : IsGeoResolution (⟨univ, [], controlledTransformAlong 𝔞 T, 1⟩ : MarkedIdeal n Y₁) S) :
    Disjoint (strictTransform n T.proj W) (controlledTransformAlong 𝔞 T).zeroLocus ∧
      CentresOver (controlledTransformAlong 𝔞 T).zeroLocus S ∧
      (∃ U : Opens Y₁, (U : Set Y₁) = ((controlledTransformAlong 𝔞 T).zeroLocus)ᶜ ∧
        strictTransform n T.proj W ⊆ U ∧ CentresAvoid U S ∧ IsIsomorphismOver n S.proj (U : Set Y₁)) ∧
      GermIdeal.pullback (m := n) S.proj (controlledTransformAlong 𝔞 T) =
        (BlowupTowerTransforms.exceptionalDivisor S).ideal ∧
      strictTransform n S.proj (strictTransform n T.proj W) = S.proj ⁻¹' strictTransform n T.proj W ∧
      IsClosedConnectedSubmanifold n (S.proj ⁻¹' strictTransform n T.proj W) k ∧
      Disjoint (BlowupTowerTransforms.exceptionalDivisor S).support (S.proj ⁻¹' strictTransform n T.proj W) ∧
      GermIdeal.pullback (m := n) S.proj (vanishingIdeal (n := n) (strictTransform n T.proj W)) =
        vanishingIdeal (n := n) (S.proj ⁻¹' strictTransform n T.proj W) := by
  obtain ⟨-, hconn, -, -, -, -, -, hcoh, ⟨U, -, hWU, hU⟩, -⟩ := first_stage W k hW hWY 𝔞 h𝔞 hres T hT
  have hdisj : Disjoint (strictTransform n T.proj W) (controlledTransformAlong 𝔞 T).zeroLocus := by
    refine Set.disjoint_left.mpr fun y hy hyZ => ?_
    exact one_ne_zero (hyZ _ (hU y (hWU hy)))
  obtain ⟨hover, havoid, hiso, hpb, hst, hconn', hdisj', hpbA⟩ := second_stage hcoh hconn hdisj S hS
  exact ⟨hdisj, hover, ⟨_, rfl, fun y hy => Set.disjoint_left.mp hdisj hy, havoid, hiso⟩, hpb, hst, hconn', hdisj',
    hpbA⟩

end SecondOfFirst

/-! ### `hir:h5a-assembly` -/

section Assembly

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Relative principalization from two resolutions** (`hir:h5a-assembly`): let `Y` be connected, `W ⊊ Y` a closed connected
submanifold of dimension `k` and `𝔞` coherent with `𝔞 ⊄ 𝓘_W`.  If `T_A` resolves `(Y, W, ∅, 𝔞, 1)` and `T_B` resolves
`(Y_t, Y_t, ∅, 𝔞_t, 1)`, `𝔞_t` the controlled transform of `𝔞` along `T_A`, then with `f = f_A ∘ g`, `H = g^* H_A` (`H_A` the
exceptional divisor of `T_A`) and `H'` the exceptional divisor of `T_B`: `f` is a sequence of blowups adapted to `W`, its strict
transform `W'` of `W` is connected and regular of dimension `k` at each of its points, `supp H ⊆ Exc f`, `H' ∩ W' = ∅`,
`f^* 𝓘_W = 𝓘_H · 𝓘_{W'}` and `f^* 𝔞 = 𝓘_H · 𝓘_{H'}` (the factorization data of `ana:relative-principalization-from-core`). -/
theorem assembly [ConnectedSpace Y] (W : Set Y) (k : ℕ) (hW : IsClosedConnectedSubmanifold n W k) (hWY : W ≠ univ)
    (𝔞 : GermIdeal n Y) (h𝔞 : 𝔞.IsCoherent) (hres : ¬ 𝔞.Le (vanishingIdeal (n := n) W))
    {Y₁ : CMfd.{u} n} (T₁ : BlowupTower (CMfd.of (n := n) Y) Y₁)
    (h₁ : IsGeoResolution (⟨W, [], 𝔞, 1⟩ : MarkedIdeal n (CMfd.of (n := n) Y)) T₁) {Y₂ : CMfd.{u} n}
    (T₂ : BlowupTower Y₁ Y₂)
    (h₂ : IsGeoResolution (⟨univ, [], controlledTransformAlong 𝔞 T₁, 1⟩ : MarkedIdeal n Y₁) T₂) :
    IsAdaptedBlowupSequence n Y W Y₂ (T₁.proj ∘ T₂.proj) ∧
      IsConnected (strictTransform n (T₁.proj ∘ T₂.proj) W) ∧
      (∀ x ∈ strictTransform n (T₁.proj ∘ T₂.proj) W,
        RegularAtDim (n := n) (strictTransform n (T₁.proj ∘ T₂.proj) W) x k) ∧
      (pullDivisor T₂ (BlowupTowerTransforms.exceptionalDivisor T₁)).support ⊆
        exceptionalLocus n (T₁.proj ∘ T₂.proj) ∧
      Disjoint (BlowupTowerTransforms.exceptionalDivisor T₂).support (strictTransform n (T₁.proj ∘ T₂.proj) W) ∧
      GermIdeal.pullback (m := n) (T₁.proj ∘ T₂.proj) (vanishingIdeal (n := n) W) =
        (pullDivisor T₂ (BlowupTowerTransforms.exceptionalDivisor T₁)).ideal.mul
          (vanishingIdeal (n := n) (strictTransform n (T₁.proj ∘ T₂.proj) W)) ∧
      GermIdeal.pullback (m := n) (T₁.proj ∘ T₂.proj) 𝔞 =
        (pullDivisor T₂ (BlowupTowerTransforms.exceptionalDivisor T₁)).ideal.mul
          (BlowupTowerTransforms.exceptionalDivisor T₂).ideal := by
  set 𝔪 : MarkedIdeal n (CMfd.of (n := n) Y) := ⟨W, [], 𝔞, 1⟩ with h𝔪
  have hkn : k < n := lt_of_ne_univ hW hWY
  have hdom : IsInvDomain k 𝔪 := FactorizationDomain.isInvDomain_of_not_le hW le_rfl h𝔞 hres
  have hWs := FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hW
  obtain ⟨hconn₁, hst₁, hadapt₁, hpb₁, hsupp₁⟩ := tower_data hdom rfl hW hkn T₁ h₁.1
  obtain ⟨hT₁', -⟩ := isGeoTestTower_and_restrictEquiv (𝔪 := 𝔪) rfl hWs h𝔞 T₁ h₁.1
  obtain ⟨-, hcohB, hpbB₁⟩ := pullback_eq_mul_geoTransformAlong (ambient 𝔪) rfl h𝔞 T₁ hT₁'
  have hcT : controlledTransformAlong 𝔞 T₁ = (geoTransformAlong (ambient 𝔪) T₁).ideal :=
    controlledTransformAlong_eq 𝔪 rfl h𝔞 T₁ hT₁'
  rw [hcT] at h₂
  set N₁ := (geoTransformAlong 𝔪 T₁).N with hN₁
  set B := (geoTransformAlong (ambient 𝔪) T₁).ideal with hBdef
  have hdisjB : Disjoint N₁ B.zeroLocus := by
    have h := cosupp_geoTransformAlong_eq (𝔪 := 𝔪) rfl hWs h𝔞 T₁ h₁.1
    rw [h₁.2] at h
    exact Set.disjoint_iff_inter_eq_empty.mpr h.symm
  set 𝔪₂ : MarkedIdeal n Y₁ := ⟨univ, [], B, 1⟩ with h𝔪₂
  obtain ⟨hconn₂, hst₂, hdisj₂, hpb₂⟩ := second_data (𝔪 := 𝔪₂) rfl rfl hcohB hconn₁ hdisjB T₂ h₂.1
  have hpbB₂ : GermIdeal.pullback (m := n) T₂.proj B = (BlowupTowerTransforms.exceptionalDivisor T₂).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution 𝔪₂ rfl hcohB rfl T₂ h₂
  have hT₁c := T₁.contMDiff_proj
  have hstf : strictTransform n (T₁.proj ∘ T₂.proj) W = T₂.proj ⁻¹' N₁ := by
    rw [StrictTransformComposition.strictTransform_comp hT₁c T₂.contMDiff_proj, ← hst₁]
    exact hst₂
  set E₁ := BlowupTowerTransforms.exceptionalDivisor T₁ with hE₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isAdaptedBlowupSequence_comp hadapt₁ hconn₁ hst₁.symm (𝔪 := 𝔪₂) rfl rfl hcohB hdisjB T₂ h₂.1
  · rw [hstf]
    exact hconn₂.2.1
  · rw [hstf]
    exact hconn₂.2.2
  · rw [support_pullDivisor, exceptionalLocus_comp (hT₁c.mdifferentiable (by simp))
      (T₂.contMDiff_proj.mdifferentiable (by simp))]
    exact fun z hz => Or.inr (hsupp₁ hz)
  · rw [hstf]
    exact hdisj₂
  · have hIW := VanishingIdealCoherent.isCoherent_vanishingIdeal hWs
    have hIN := VanishingIdealCoherent.isCoherent_vanishingIdeal
      (FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hconn₁)
    rw [hstf, pullDivisor_ideal, GermIdealTotalTransform.pullback_comp hT₁c T₂.contMDiff_proj hIW]
    rw [show (𝔪.N : Set Y) = W from rfl] at hpb₁
    rw [hpb₁, GermIdealTotalTransform.pullback_mul T₂.contMDiff_proj (isCoherent_ideal _) hIN, hpb₂]
  · rw [pullDivisor_ideal, GermIdealTotalTransform.pullback_comp hT₁c T₂.contMDiff_proj h𝔞]
    have hpb₁' : GermIdeal.pullback (m := n) T₁.proj 𝔞 = E₁.ideal.mul B := by
      rw [← idealPow_one_of_isCoherent (isCoherent_ideal E₁)]
      exact hpbB₁
    rw [hpb₁', GermIdealTotalTransform.pullback_mul T₂.contMDiff_proj (isCoherent_ideal _) hcohB, hpbB₂]

end Assembly

end

end Hironaka.HironakaControlledTransform
