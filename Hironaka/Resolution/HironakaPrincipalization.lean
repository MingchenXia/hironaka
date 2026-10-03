/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Blowup.BlowupSequenceIsomorphismOff
import Hironaka.Resolution.FactorizationDomain
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Blowup.ExceptionalLocus
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticIrreducibleComponents
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.MarkedIdeal.RestrictLeCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Principalization of a coherent ideal (Hironaka)

Sources: Włodarczyk 2005 (`hiron.tex`), §2.3, "(1) ⟹ (2)": a resolution of the marked ideal `(X, X, ∅, 𝔞, 1)`
principalizes `𝔞`; Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Theorem 1.3 (principalization,
functorial form); Kollár 2007, Theorem 3.26.

**Statement.**  Let `X` be a compact complex manifold and `𝔞` a coherent ideal sheaf on `X` which vanishes identically on no
nonempty open set (at every point some germ of `𝔞` is not identically zero nearby).  Then there is a finite sequence of blowups
with smooth centres `f : X' → X` and an effective divisor `D` on `X'` such that

* `f^*𝔞 = 𝒪_{X'}(-D)`: the total transform of `𝔞` is invertible;
* the support of `D` is `f⁻¹ Z(𝔞)`, and it is the union of the members of a divisor with simple normal crossings;
* `f` is an isomorphism over `X \ Z(𝔞)` (every centre lies over the zero locus of `𝔞`).

**Route.** The canonical resolution invariant in dimension `≤ n` (`CanonicalCentres.canonicalInvariant`) resolves
the marked ideal `(X, X, [], 𝔞, 1)`; a resolution with mark `1` and `N = X` principalizes
(`MarkedIdeal.pullback_eq_exceptionalDivisor_of_isGeoResolution`: `T^*𝔞 = 𝒪(-E_T)` for the exceptional divisor `E_T`
of the tower). New here: the support of `E_T` is the union of the members of the transformed divisor of the marked
ideal (`support_exceptionalDivisor_eq_biUnion`), which has simple normal crossings because the transforms stay well
formed; and the exceptional locus of the tower lies in the support of `E_T`.

## Main results

* `isClosed_of_mem_E_geoTransformAlong`, `support_exceptionalDivisor_eq_biUnion`, `exceptionalLocus_subset_support`:
  the members of the transformed divisor are closed; for a marked ideal with `E = []` the support of the exceptional divisor of
  any tower is the union of the members of the transformed divisor; the exceptional locus of a tower lies in that support;
* `isInvDomain_univ`: `(X, X, [], 𝔞, 1)` lies in the domain of the invariants in dimension `≤ n` when `𝔞` is coherent and
  nonzero at every point (no connectedness needed);
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.HironakaPrincipalization

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings Hironaka.BlowupStrictSubmanifold Hironaka.DivisorExponentAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {n : ℕ}

/-! ### The support of the exceptional divisor of a tower -/

section Support

variable {X : CMfd.{u} n}

/-- **The members of the transformed divisor are closed** (along any tower, if those of `𝔪` are): the transformed members are
closures of preimages, and the new member `π⁻¹ C` is the preimage of a closed centre. -/
theorem isClosed_of_mem_E_geoTransformAlong (𝔪 : MarkedIdeal n X) (h𝔪 : ∀ H ∈ 𝔪.E, IsClosed H) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), ∀ H ∈ (geoTransformAlong 𝔪 T).E, IsClosed H
  | _, .refl => fun H hH => h𝔪 H (by simpa using hH)
  | _, .step T C π hπ => by
      intro H hH
      rw [geoTransformAlong_step, geoTransform_E, List.mem_append, List.mem_map, List.mem_singleton] at hH
      rcases hH with ⟨H₀, -, rfl⟩ | rfl
      · exact isClosed_closure
      · exact hπ.1.1.preimage hπ.contMDiff.continuous

/-- The zero locus of a product contains the zero locus of the left factor. -/
theorem zeroLocus_left_subset_mul {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (𝔞 𝔟 : GermIdeal n M) : 𝔞.zeroLocus ⊆ (𝔞.mul 𝔟).zeroLocus := by
  rw [RestrictLeCalculus.mul_comm']
  exact RestrictLeCalculus.zeroLocus_right_subset_mul 𝔟 𝔞

/-- The support of a sum of effective divisors is the union of the supports. -/
theorem support_add {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D D' : EffectiveDivisor n M) :
    (GermIdealTotalTransform.EffectiveDivisor.add D D').support = D.support ∪ D'.support := by
  refine Subset.antisymm (fun x hx => ?_) ?_
  · by_contra h
    rw [mem_union, not_or] at h
    exact RestrictLeCalculus.notMem_zeroLocus_mul (BlowupExceptionalDivisor.isCoherent_ideal D)
      (BlowupExceptionalDivisor.isCoherent_ideal D') h.1 h.2 hx
  rintro x (hx | hx)
  · exact zeroLocus_left_subset_mul D.ideal D'.ideal hx
  · exact RestrictLeCalculus.zeroLocus_right_subset_mul D.ideal D'.ideal hx

/-- **The support of the exceptional divisor of a tower is the union of the transformed members** (for a marked ideal with
`E = []`): `supp E_T = ⋃ H ∈ E(𝔪_T), H`.  After a blowup `π` along `C` the support is `π⁻¹(supp E_T) ∪ π⁻¹ C`, and the members are
the strict transforms `closure (π⁻¹ (H \ C))` of the old members and `π⁻¹ C`; a point of `π⁻¹ H` lies in `π⁻¹ C` or in
`π⁻¹ (H \ C)`, and `closure (π⁻¹ (H \ C)) ⊆ π⁻¹ H` for `H` closed. -/
theorem support_exceptionalDivisor_eq_biUnion (𝔪 : MarkedIdeal n X) (hE : 𝔪.E = []) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (BlowupTowerTransforms.exceptionalDivisor T).support = ⋃ H ∈ (geoTransformAlong 𝔪 T).E, H
  | _, .refl => by
      rw [geoTransformAlong_refl, hE]
      ext x
      simp only [List.not_mem_nil, iUnion_of_empty, iUnion_empty, mem_empty_iff_false, iff_false]
      intro hx
      exact one_ne_zero (hx (fun _ => (1 : ℂ)) (holomorphicAt_const 1))
  | _, .step T C π hπ => by
      have ih := support_exceptionalDivisor_eq_biUnion 𝔪 hE T
      have hcl := isClosed_of_mem_E_geoTransformAlong 𝔪 (by simp [hE]) T
      show (GermIdealTotalTransform.EffectiveDivisor.add
          (BlowupExceptionalDivisor.totalTransform hπ (BlowupTowerTransforms.exceptionalDivisor T))
          (BlowupExceptionalDivisor.exceptionalDivisor hπ)).support = _
      rw [support_add, BlowupExceptionalDivisor.support_totalTransform,
        BlowupExceptionalDivisor.support_exceptionalDivisor, ih, geoTransformAlong_step, geoTransform_E]
      ext z
      simp only [mem_union, mem_preimage, mem_iUnion, List.mem_append, List.mem_map, List.mem_singleton,
        exists_prop]
      constructor
      · rintro (⟨H, hH, hzH⟩ | hzC)
        · by_cases hzC : π z ∈ C
          · exact ⟨π ⁻¹' C, Or.inr rfl, hzC⟩
          · exact ⟨geoStrictTransform π C H, Or.inl ⟨H, hH, rfl⟩, subset_closure ⟨hzH, hzC⟩⟩
        · exact ⟨π ⁻¹' C, Or.inr rfl, hzC⟩
      · rintro ⟨H', (⟨H, hH, rfl⟩ | rfl), hz⟩
        · left
          refine ⟨H, hH, ?_⟩
          have hsub : geoStrictTransform π C H ⊆ π ⁻¹' H :=
            closure_minimal (fun w hw => hw.1) ((hcl H hH).preimage hπ.contMDiff.continuous)
          exact hsub hz
        · exact Or.inr hz

/-- **The exceptional locus of a tower lies in the support of its exceptional divisor**: the exceptional locus of a blowup
lies over its centre, `Exc (T ∘ π) = Exc π ∪ π⁻¹ Exc T`, and the support after `π` is `π⁻¹(supp E_T) ∪ π⁻¹ C`. -/
theorem exceptionalLocus_subset_support :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      exceptionalLocus n T.proj ⊆ (BlowupTowerTransforms.exceptionalDivisor T).support
  | _, .refl => by
      rw [BlowupTower.proj_refl, exceptionalLocus_id]
      exact empty_subset _
  | _, .step T C π hπ => by
      have ih := exceptionalLocus_subset_support T
      show exceptionalLocus n (T.proj ∘ π) ⊆ (GermIdealTotalTransform.EffectiveDivisor.add
          (BlowupExceptionalDivisor.totalTransform hπ (BlowupTowerTransforms.exceptionalDivisor T))
          (BlowupExceptionalDivisor.exceptionalDivisor hπ)).support
      rw [exceptionalLocus_comp (T.contMDiff_proj.mdifferentiable (by simp)) (hπ.contMDiff.mdifferentiable (by simp)),
        support_add, BlowupExceptionalDivisor.support_totalTransform,
        BlowupExceptionalDivisor.support_exceptionalDivisor]
      rintro z (hz | hz)
      · exact Or.inr (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ hz)
      · exact Or.inl (ih hz)

end Support

/-! ### The domain and the principalization -/

section Principalization

/-- **`(X, X, [], 𝔞, 1)` lies in the domain in dimension `≤ n`** for a coherent `𝔞` that is nonzero at every point (no
connectedness needed). -/
theorem isInvDomain_univ {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x) :
    IsInvDomain n (⟨univ, [], 𝔞, 1⟩ : MarkedIdeal n M) where
  isWellFormed :=
    ⟨⟨isClosed_univ, fun x _ => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩, h𝔞, isSNCDivisor_nil,
      isTransverse_nil_of_isClosedSubmanifold
        ⟨isClosed_univ, fun x _ => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩⟩
  dimLE := fun x _ => ⟨n, le_rfl, AnalyticIrreducibleComponents.regularAtDim_univ x⟩
  one_le_d := le_rfl
  isNonzeroAlongAt := fun x _ => hne x

end Principalization

end

end Hironaka.HironakaPrincipalization
