import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupControlledTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Blowup towers: restriction to open sets, exceptional divisor, and principalization from a
resolution of `(X, X, E, 𝔞, 1)`

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.1 (resolution of a marked ideal;
extensions arise when passing to open subsets), §2.2 (controlled transforms along a multiple test
blow-up), §2.3 (Hironaka resolution principle (1) ⟹ (2): a resolution of `(X, 𝓘, ∅, 1)` is a
principalization of `𝓘`); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), §2 and
the paragraph after Theorem 1.3; blueprint `bcalc:tower-restrict`, `bcalc:tower-exceptional`,
`bcalc:transform-ambient`, `bcalc:principalization` (chapter `blowup-calculus.tex`).

Built on the shared tower and marked-ideal types of `Hironaka.BlowupTowers` /
`Hironaka.MarkedIdeals` (TN-CLASSICAL, Hironaka phase H1).

* `restrict U T` — **the restriction of a tower `T` over `X` to an open `U ⊆ X`**: a tower over
  `U` ending at the open preimage `openPreimage T U` of `U`, whose centres are the traces of those
  of `T` (`BlowupRestrictOpen.isBlowupAlong_restrict` at each step); `proj_restrict`.
* `exceptionalDivisor T` — the exceptional divisor of the composite: `0` for the empty tower,
  `π^*E + D` after a blowup `π` with exceptional divisor `D`.
* `strictTransform_univ`, `restrictOn_univ`, `transform_ideal_eq_controlledTransform` — for
  `N = X` the transform of a marked ideal (`MarkedIdeal.transform`, a colon along the strict
  transform) is the controlled transform `σ^c(𝔞, d)` of `BlowupControlledTransform`, and `N`
  stays the whole space.
* `pullback_eq_mul_transformAlong` — along a multiple test blow-up `T` of `(X, X, E, 𝔞, 1)` with
  `𝔞` coherent: `T^*𝔞 = 𝒪(-E_T) · 𝔞_T`, with `𝔞_T` the (coherent) transform.
* `pullback_eq_exceptionalDivisor_of_isResolution` — **resolution gives principalization**:
  if `T` resolves `(X, X, E, 𝔞, 1)`, then `T^*𝔞 = 𝒪(-E_T)` is invertible.

With the mark `1` the admissibility of a centre `C` (`C ⊆ cosupp = Z(𝔞)`) already gives
`𝔞 ⊆ 𝓘_C` (`le_vanishingIdeal_of_subset_zeroLocus`), so nothing from the local algebra of orders
beyond `GermIdealOrder.cosupport_one` is used.

Everything here is sorry-free, and outside the import closure of the two Hironaka statements.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupTowerTransforms

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  GermIdealTotalTransform GermIdealPullbackCalculus IdealWeightPowers InvertibleIdealQuotient
  RelativePrincipalizationSpan BlowupExceptionalDivisor BlowupControlledTransform
  BlowupRestrictOpen BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  RestrictedIdealExtension RestrictedIdealQuotient

noncomputable section

/-! ### Ideal lemmas -/

section Ideals

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`𝔞|_X = 𝔞`**: restricting a coherent ideal to the whole space changes nothing. -/
theorem restrictOn_univ {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) : restrictOn n univ 𝔞 = 𝔞 := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · obtain ⟨hghol, N, s, a, hs, ha, hsum⟩ := hg
    exact mem_of_isInSpanAt_mem h𝔞
      ⟨hghol, N, s, a, hs, ha, hsum.mono fun y hy => hy (mem_univ y)⟩
  · exact le_restrictOn h𝔞 x g hg

/-- **A coherent ideal vanishing on `C` lies in `𝓘_C`.** -/
theorem le_vanishingIdeal_of_subset_zeroLocus {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    {C : Set M} (hC : C ⊆ 𝔞.zeroLocus) : 𝔞.Le (vanishingIdeal (n := n) C) := by
  intro x g hg
  refine ⟨GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg, ?_⟩
  obtain ⟨U, hU, hxU, N, s, hs, hgen⟩ := h𝔞 x
  obtain ⟨-, K, t, a, ht, ha, hsum⟩ := (hgen x hxU g).mp hg
  -- near `x`, the same combination exhibits `g` as a germ of `𝔞` at every nearby point
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U ∧ (∀ i, HolomorphicAt n (a i) y) ∧
      HolomorphicAt n g y ∧ g =ᶠ[𝓝 y] fun z => ∑ i, a i z * t i z := by
    filter_upwards [hU.mem_nhds hxU, eventually_all.mpr fun i => (ha i).eventually,
      (GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg).eventually, hsum.eventually_nhds]
      with y hyU hya hyg hysum
    exact ⟨hyU, hya, hyg, hysum⟩
  filter_upwards [hev] with y ⟨hyU, hya, hyg, hysum⟩ hyC
  have hmem : 𝔞.mem y g := (hgen y hyU g).mpr ⟨hyg, K, t, a, ht, hya, hysum⟩
  exact hC hyC g hmem

/-- **A coherent ideal with empty zero locus is the unit ideal.** -/
theorem eq_unitIdeal_of_zeroLocus_eq_empty {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    (h : 𝔞.zeroLocus = ∅) : 𝔞 = unitIdeal n M := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · exact mem_unitIdeal_iff.mpr (isInSpanAt_of_eq_mul (s := fun _ => (1 : ℂ)) (a := g) ⟨0, rfl⟩
      (GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) (GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg)
      (Eventually.of_forall fun _ => by simp))
  · have hx : x ∉ 𝔞.zeroLocus := by rw [h]; exact notMem_empty x
    obtain ⟨b, hb, hbx⟩ : ∃ b, 𝔞.mem x b ∧ b x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx hcon
    have hbhol : HolomorphicAt n b x := GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hb
    have hghol : HolomorphicAt n g x := (mem_unitIdeal_iff.mp hg).holomorphicAt
    have hinv : HolomorphicAt n (fun y => (b y)⁻¹) x := holomorphicAt_inv hbhol hbx
    refine mem_of_isInSpanAt_mem h𝔞 (isInSpanAt_of_eq_mul hb hghol (hghol.mul hinv) ?_)
    filter_upwards [hbhol.continuousAt.eventually_ne hbx] with y hy
    show g y = g y * (b y)⁻¹ * b y
    field_simp

end Ideals

/-! ### Restriction of a tower to an open subset -/

section Restrict

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The open preimage of `U ⊆ X` in the last space of a tower. -/
def openPreimage (T : BlowupTower X Y) (U : Opens X) : Opens Y :=
  ⟨T.proj ⁻¹' (U : Set X), U.isOpen.preimage T.contMDiff_proj.continuous⟩

/-- **The restriction of a tower to an open subset `U` of its base**: the tower over `U` whose
spaces are the open preimages of `U` and whose centres are the traces of the centres. -/
def restrict (U : Opens X) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
    BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) (openPreimage T U))
  | _, .refl => .refl
  | _, .step T C _ hπ =>
      .step (restrict U T) ((↑) ⁻¹' C : Set (openPreimage T U)) _
        (isBlowupAlong_restrict hπ (openPreimage T U)
          ((openPreimage T U).isOpen.preimage hπ.contMDiff.continuous))

/-- The restricted tower projects like the tower. -/
theorem proj_restrict (U : Opens X) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
    ∀ p : openPreimage T U, (((restrict U T).proj p : U) : X) = T.proj p.1
  | _, .refl, _ => rfl
  | _, .step T _ π _, p => proj_restrict U T ⟨π p.1, p.2⟩

/-- The restricted tower has the same length. -/
theorem length_restrict (U : Opens X) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
    (restrict U T).length = T.length
  | _, .refl => rfl
  | _, .step T _ _ _ => congrArg (· + 1) (length_restrict U T)

end Restrict

/-! ### The exceptional divisor of a tower -/

section Exceptional

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- **The exceptional divisor of a tower**: `0` for the empty tower and `π^*E + D` after a
further blowup `π` with exceptional divisor `D`; so `E_T = Σᵢ` (total transform of `Dᵢ`). -/
def exceptionalDivisor : {Y : CMfd.{u} n} → BlowupTower X Y → EffectiveDivisor n Y
  | _, .refl => ⟨unitIdeal n X, isInvertible_unitIdeal⟩
  | _, .step T _ _ hπ =>
      EffectiveDivisor.add (totalTransform hπ (exceptionalDivisor T))
        (BlowupExceptionalDivisor.exceptionalDivisor hπ)

@[simp] theorem exceptionalDivisor_refl_ideal :
    (exceptionalDivisor (BlowupTower.refl : BlowupTower X X)).ideal = unitIdeal n X := rfl

theorem exceptionalDivisor_step_ideal (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) :
    (exceptionalDivisor (.step T C π hπ)).ideal =
      (GermIdeal.pullback (m := n) π (exceptionalDivisor T).ideal).mul
        (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) := rfl

end Exceptional

/-! ### Transforms with `N = X` -/

section Ambient

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **The strict transform of the whole space is the whole space.** -/
theorem strictTransform_univ (hπ : IsBlowupAlong n C π) : strictTransform n π univ = univ := by
  rw [strictTransform, preimage_univ, ← compl_eq_univ_sdiff, closure_compl,
    interior_exceptionalLocus_eq_empty hπ, compl_empty]

/-- **For `N = X` the transform of a marked ideal is the controlled transform**, and `N` stays
the whole space. -/
theorem transform_ideal_eq_controlledTransform (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hπ : IsBlowupAlong n C π) :
    (𝔪.transform C π).ideal = controlledTransform hπ 𝔪.ideal 𝔪.d := by
  show colonAlong n (closure (π ⁻¹' (𝔪.N \ C))) _ _ = _
  rw [hN, preimage_sdiff, preimage_univ, ← compl_eq_univ_sdiff, closure_compl,
    ExceptionalFibres.interior_preimage_eq_empty hπ, compl_empty]
  show colon (restrictOn n univ (GermIdeal.pullback (m := n) π 𝔪.ideal)) _ = _
  rw [restrictOn_univ (isCoherent_pullback hπ.contMDiff h𝔞)]
  rfl

theorem transform_N_eq_univ (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ)
    (hπ : IsBlowupAlong n C π) : (𝔪.transform C π).N = univ := by
  show closure (π ⁻¹' (𝔪.N \ C)) = univ
  rw [hN, preimage_sdiff, preimage_univ, ← compl_eq_univ_sdiff, closure_compl,
    ExceptionalFibres.interior_preimage_eq_empty hπ, compl_empty]

end Ambient

/-! ### Principalization from a resolution with the mark `1` -/

section Principalization

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **Along a multiple test blow-up of `(X, X, E, 𝔞, 1)`** with `𝔞` coherent, the transform
keeps `N = X`, its ideal `𝔞_T` is coherent, and `T^*𝔞 = 𝒪(-E_T) · 𝔞_T`. -/
theorem pullback_eq_mul_transformAlong (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ)
    (hd : 𝔪.d = 1) (h𝔞 : 𝔪.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsTestTower 𝔪 T →
      (transformAlong 𝔪 T).N = univ ∧ (transformAlong 𝔪 T).ideal.IsCoherent ∧
      GermIdeal.pullback (m := n) T.proj 𝔪.ideal =
        (exceptionalDivisor T).ideal.mul (transformAlong 𝔪 T).ideal
  | _, .refl, _ => by
      refine ⟨hN, h𝔞, ?_⟩
      rw [exceptionalDivisor_refl_ideal, BlowupTower.proj_refl, transformAlong_refl,
        unitIdeal_mul h𝔞]
      exact pullback_id h𝔞
  | _, .step T C π hπ, hT => by
      obtain ⟨hTT, hC⟩ := (isTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hNT, hcohT, hpb⟩ := pullback_eq_mul_transformAlong 𝔪 hN hd h𝔞 T hTT
      set 𝔫 := transformAlong 𝔪 T with h𝔫
      have hd𝔫 : 𝔫.d = 1 := by rw [h𝔫, d_transformAlong, hd]
      -- the admissible centre lies in the zero locus of `𝔞_T`, hence `𝔞_T ⊆ 𝓘_C`
      have hCz : C ⊆ 𝔫.ideal.zeroLocus := by
        intro x hx
        have hx' := hC.2.1 hx
        rw [MarkedIdeal.cosupp, hd𝔫,
          cosupport_one fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcohT hg] at hx'
        exact hx'.2
      have hle : 𝔫.ideal.Le (idealPow (vanishingIdeal (n := n) C) 1) := by
        rw [idealPow_succ, idealPow_zero,
          unitIdeal_mul (VanishingIdealCoherent.isCoherent_vanishingIdeal hπ.1)]
        exact le_vanishingIdeal_of_subset_zeroLocus hcohT hCz
      have htr : (𝔫.transform C π).ideal = controlledTransform hπ 𝔫.ideal 1 := by
        rw [transform_ideal_eq_controlledTransform 𝔫 hNT hcohT hπ, hd𝔫]
      have hD : (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal.IsCoherent :=
        isCoherent_ideal _
      have hE : (exceptionalDivisor T).ideal.IsCoherent := isCoherent_ideal _
      have hπE : (GermIdeal.pullback (m := n) π (exceptionalDivisor T).ideal).IsCoherent :=
        isCoherent_pullback hπ.contMDiff hE
      have hcon := isCoherent_controlledTransform hπ hcohT hle
      refine ⟨?_, ?_, ?_⟩
      · rw [transformAlong_step]
        exact transform_N_eq_univ 𝔫 hNT hπ
      · rw [transformAlong_step, htr]
        exact hcon
      · rw [transformAlong_step, htr, BlowupTower.proj_step,
          pullback_comp T.contMDiff_proj hπ.contMDiff h𝔞, hpb,
          pullback_mul hπ.contMDiff hE hcohT,
          pullback_eq_mul_controlledTransform hπ hcohT hle, idealPow_succ, idealPow_zero,
          unitIdeal_mul hD, exceptionalDivisor_step_ideal,
          ← mul_assoc hπE hD hcon]
        rfl

/-- **Resolution gives principalization** (Wlodarczyk §2.3, (1) ⟹ (2)): if `T` resolves the
marked ideal `(X, X, E, 𝔞, 1)` with `𝔞` coherent, then `T^*𝔞 = 𝒪(-E_T)`. -/
theorem pullback_eq_exceptionalDivisor_of_isResolution (𝔪 : MarkedIdeal n X)
    (hN : 𝔪.N = univ) (hd : 𝔪.d = 1) (h𝔞 : 𝔪.ideal.IsCoherent) (T : BlowupTower X Y)
    (hT : IsResolution 𝔪 T) :
    GermIdeal.pullback (m := n) T.proj 𝔪.ideal = (exceptionalDivisor T).ideal := by
  obtain ⟨hNT, hcohT, hpb⟩ := pullback_eq_mul_transformAlong 𝔪 hN hd h𝔞 T hT.1
  have hz : (transformAlong 𝔪 T).ideal.zeroLocus = ∅ := by
    have h2 := hT.2
    rw [MarkedIdeal.cosupp, d_transformAlong, hd, hNT,
      cosupport_one fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcohT hg,
      univ_inter] at h2
    exact h2
  rw [hpb, eq_unitIdeal_of_zeroLocus_eq_empty hcohT hz,
    RestrictLeCalculus.mul_unitIdeal (isCoherent_ideal _)]

/-- The principalized total transform is invertible. -/
theorem isInvertible_pullback_of_isResolution (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ)
    (hd : 𝔪.d = 1) (h𝔞 : 𝔪.ideal.IsCoherent) (T : BlowupTower X Y) (hT : IsResolution 𝔪 T) :
    (GermIdeal.pullback (m := n) T.proj 𝔪.ideal).IsInvertible := by
  rw [pullback_eq_exceptionalDivisor_of_isResolution 𝔪 hN hd h𝔞 T hT]
  exact (exceptionalDivisor T).isInvertible

end Principalization

end

end Hironaka.BlowupTowerTransforms
