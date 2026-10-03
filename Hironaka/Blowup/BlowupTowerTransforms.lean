/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Blowup towers: restriction to open sets, exceptional divisor, and principalization from a
resolution of `(X, X, E, 𝔞, 1)`

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.1 (resolution of a marked ideal; extensions arise when passing
to open subsets), §2.2 (controlled transforms along a multiple test blow-up), §2.3 (Hironaka resolution principle
(1) ⟹ (2): a resolution of `(X, 𝓘, ∅, 1)` is a principalization of `𝓘`); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), §2 and the paragraph after Theorem 1.3.

Built on the shared tower and marked-ideal types of `Hironaka.BlowupTowers` / `Hironaka.MarkedIdeals`.

* `restrict U T` — **the restriction of a tower `T` over `X` to an open `U ⊆ X`**: a tower over
  `U` ending at the open preimage `openPreimage T U` of `U`, whose centres are the traces of those
  of `T` (`BlowupRestrictOpen.isBlowupAlong_restrict` at each step); `proj_restrict`.
* `exceptionalDivisor T` — the exceptional divisor of the composite: `0` for the empty tower,
  `π^*E + D` after a blowup `π` with exceptional divisor `D`.

With the mark `1` the admissibility of a centre `C` (`C ⊆ cosupp = Z(𝔞)`) already gives `𝔞 ⊆ 𝓘_C`, so nothing from
the local algebra of orders beyond `GermIdealOrder.cosupport_one` is used.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupTowerTransforms

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealTotalTransform GermIdealPullbackCalculus IdealWeightPowers InvertibleIdealQuotient RelativePrincipalizationSpan BlowupExceptionalDivisor BlowupControlledTransform BlowupRestrictOpen BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder RestrictedIdealExtension RestrictedIdealQuotient

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

end

end Hironaka.BlowupTowerTransforms
