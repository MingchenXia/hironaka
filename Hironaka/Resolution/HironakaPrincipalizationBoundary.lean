/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaRelativelyCompact
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticIrreducibleComponents
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Resolution.HironakaPrincipalization
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Blowup.SimultaneousNormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Principalization relative to a simple normal crossings boundary (Hironaka)

Sources: Kollár 2007 (`kollar07-resolution`), "Principalization, III" (an ideal on a manifold with a simple normal
crossings divisor `E₀`: the centres have simple normal crossings with the accumulated divisor and the final divisor,
containing the birational transform of `E₀`, has simple normal crossings); Bierstone--Milman 1997
(`bierstone-milman97-invent-math`), Theorem 1.10 and (1.9); Włodarczyk 2005 (`wlodarczyk05-hironaka`), §2.3.

**Statement.**  Let `X` be a complex manifold, `E₀` a divisor with simple normal crossings on `X`, and `𝔞` a coherent ideal sheaf,
nonzero at every point, whose zero locus is compact (e.g. `X` compact).  There are an admissible blowup sequence `f : X' → X`
of `(X, E₀)` with centres over `Z(𝔞)` (`HironakaAdmissibleSequence.IsAdmissibleBlowupSequence`), with accumulated divisor `E`,
and an effective divisor `D` on `X'` such that `E` has simple normal crossings (its first members are the strict transforms of
the members of `E₀`), `f^*𝔞 = 𝒪(-D)`, `supp D` is the union of the members of `E` created by the blowups (the members after
the first `|E₀|`), `supp D = f⁻¹ Z(𝔞)`, and `f` is an isomorphism over `X \ Z(𝔞)`.

**Route.**  `(X, X, E₀, 𝔞, 1)` lies in the domain (`E₀` is transverse to `X`); its canonical resolution (compact cosupport,
`HironakaAdmissibleSequence.exists_isGeoResolution_isCanonical_of_isCompact`) principalizes `𝔞` with the exceptional divisor of the
tower (`pullback_eq_exceptionalDivisor_of_isGeoResolution`, which does not need `E₀ = []`), whose support is the union of the
new members (`support_exceptionalDivisor_eq_biUnion_drop`, the form of `HironakaPrincipalization.support_exceptionalDivisor_eq_biUnion`
for a nonempty initial divisor).

## Main results

* `isInvDomain_univ_of_isSNCDivisor`, `support_exceptionalDivisor_eq_biUnion_drop`;
* **`exists_principalization_boundary`** (compact zero locus) and `exists_principalization_boundary_of_compactSpace`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaPrincipalizationBoundary

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings Hironaka.DivisorExponentAlong Hironaka.BlowupTowerTransforms Hironaka.HironakaAdmissibleSequence Hironaka.BlowupStrictSubmanifold
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-- **`(X, X, E₀, 𝔞, 1)` lies in the domain in dimension `≤ n`** for a divisor `E₀` with simple normal crossings and a coherent
`𝔞` nonzero at every point: `E₀` is transverse to `X` (`SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor`). -/
theorem isInvDomain_univ_of_isSNCDivisor {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x)
    {E₀ : List (Set M)} (hE₀ : IsSNCDivisor n E₀) :
    IsInvDomain n (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n M) where
  isWellFormed :=
    ⟨⟨isClosed_univ, fun x _ => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩, h𝔞, hE₀,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE₀⟩
  dimLE := fun x _ => ⟨n, le_rfl, AnalyticIrreducibleComponents.regularAtDim_univ x⟩
  one_le_d := le_rfl
  isNonzeroAlongAt := fun x _ => hne x

/-- **The support of the exceptional divisor of a tower is the union of the members created by the blowups**: for a marked
ideal with closed members, `supp E_T = ⋃ H ∈ E(𝔪_T).drop |E(𝔪)|, H` (the members after the strict transforms of the initial
ones; `HironakaPrincipalization.support_exceptionalDivisor_eq_biUnion` is the case `E(𝔪) = []`). -/
theorem support_exceptionalDivisor_eq_biUnion_drop {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)
    (h𝔪 : ∀ H ∈ 𝔪.E, IsClosed H) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (BlowupTowerTransforms.exceptionalDivisor T).support =
        ⋃ H ∈ (geoTransformAlong 𝔪 T).E.drop 𝔪.E.length, H
  | _, .refl => by
      rw [geoTransformAlong_refl, List.drop_length]
      ext x
      simp only [List.not_mem_nil, iUnion_of_empty, iUnion_empty, mem_empty_iff_false, iff_false]
      intro hx
      exact one_ne_zero (hx (fun _ => (1 : ℂ)) (holomorphicAt_const 1))
  | _, .step T C π hπ => by
      have ih := support_exceptionalDivisor_eq_biUnion_drop 𝔪 h𝔪 T
      have hcl := HironakaPrincipalization.isClosed_of_mem_E_geoTransformAlong 𝔪 h𝔪 T
      have hle : 𝔪.E.length ≤ ((geoTransformAlong 𝔪 T).E.map (geoStrictTransform π C)).length := by
        rw [List.length_map, length_E_geoTransformAlong]
        omega
      show (GermIdealTotalTransform.EffectiveDivisor.add
          (BlowupExceptionalDivisor.totalTransform hπ (BlowupTowerTransforms.exceptionalDivisor T))
          (BlowupExceptionalDivisor.exceptionalDivisor hπ)).support = _
      rw [HironakaPrincipalization.support_add, BlowupExceptionalDivisor.support_totalTransform,
        BlowupExceptionalDivisor.support_exceptionalDivisor, ih, geoTransformAlong_step, geoTransform_E,
        List.drop_append_of_le_length hle, ← List.map_drop]
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
            closure_minimal (fun w hw => hw.1)
              ((hcl H (List.mem_of_mem_drop hH)).preimage hπ.contMDiff.continuous)
          exact hsub hz
        · exact Or.inr hz

/-- **Principalization relative to a simple normal crossings boundary** (Hironaka; `hir:principalization-boundary`): let `X` be
any complex manifold, `E₀` a divisor on `X` with simple normal crossings, and `𝔞` a coherent ideal sheaf on `X`, nonzero at every
point, with compact zero locus.  There are an admissible blowup sequence `f : X' → X` of `(X, E₀)` with centres over `Z(𝔞)`, with
accumulated divisor `E`, and an effective divisor `D` on `X'` such that `E` has simple normal crossings, `f^*𝔞 = 𝒪(-D)`,
`supp D` is the union of the members of `E` created by the blowups, `supp D = f⁻¹ Z(𝔞)`, and `f` is an isomorphism over
`X \ Z(𝔞)`. -/
theorem exists_principalization_boundary {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x)
    (hZ : IsCompact 𝔞.zeroLocus) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (D : EffectiveDivisor n X') (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ 𝔞.zeroLocus X' f E ∧
      IsSNCDivisor n E ∧
      GermIdeal.pullback (m := n) f 𝔞 = D.ideal ∧
      D.support = ⋃ H ∈ E.drop E₀.length, H ∧
      D.support = f ⁻¹' 𝔞.zeroLocus ∧
      IsIsomorphismOver n f 𝔞.zeroLocusᶜ := by
  set 𝔪 : MarkedIdeal n (CMfd.of (n := n) X) := ⟨univ, E₀, 𝔞, 1⟩ with h𝔪
  have hdom : IsInvDomain n 𝔪 := isInvDomain_univ_of_isSNCDivisor (M := CMfd.of (n := n) X) h𝔞 hne hE₀
  have hcos : 𝔪.cosupp = 𝔞.zeroLocus := by
    show GermIdealOrder.cosupport n univ 𝔞 1 = 𝔞.zeroLocus
    rw [GermIdealOrder.cosupport_one
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg), univ_inter]
  obtain ⟨Y, T, -, hres⟩ := exists_isGeoResolution_isCanonical_of_isCompact
    (CanonicalCentres.canonicalInvariant.{u} n) hdom (by rw [hcos]; exact hZ)
  have hpb : GermIdeal.pullback (m := n) T.proj 𝔞 = (BlowupTowerTransforms.exceptionalDivisor T).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution 𝔪 rfl h𝔞 rfl T hres
  have hsuppZ : (BlowupTowerTransforms.exceptionalDivisor T).support = T.proj ⁻¹' 𝔞.zeroLocus := by
    rw [EffectiveDivisor.support, ← hpb, BlowupExceptionalDivisor.zeroLocus_pullback T.contMDiff_proj h𝔞]
  have hadm := isAdmissibleBlowupSequence_proj 𝔪 _ T hres.1
    (centresOver_cosupp 𝔪 hdom.isWellFormed.isClosedSubmanifold_N h𝔞 T hres.1)
  rw [hcos] at hadm
  refine ⟨Y, inferInstance, inferInstance, inferInstance, T.proj, BlowupTowerTransforms.exceptionalDivisor T, _, hadm,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom T hres.1).isWellFormed.isSNCDivisor, hpb,
    support_exceptionalDivisor_eq_biUnion_drop 𝔪 hE₀.1 T, hsuppZ, ?_⟩
  refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset T.isBlowupSequence ?_
  rintro x ⟨z, hz, rfl⟩
  have hz' := HironakaPrincipalization.exceptionalLocus_subset_support T hz
  rw [hsuppZ] at hz'
  exact hz'

/-- **Principalization relative to a simple normal crossings boundary, compact base.** -/
theorem exists_principalization_boundary_of_compactSpace {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] {𝔞 : GermIdeal n X}
    (h𝔞 : 𝔞.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (D : EffectiveDivisor n X') (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ 𝔞.zeroLocus X' f E ∧
      IsSNCDivisor n E ∧
      GermIdeal.pullback (m := n) f 𝔞 = D.ideal ∧
      D.support = ⋃ H ∈ E.drop E₀.length, H ∧
      D.support = f ⁻¹' 𝔞.zeroLocus ∧
      IsIsomorphismOver n f 𝔞.zeroLocusᶜ := by
  have hdom := HironakaPrincipalization.isInvDomain_univ (M := CMfd.of (n := n) X) h𝔞 hne
  have hclosed : IsClosed 𝔞.zeroLocus := by
    rw [← cosupp_univ_one (X := CMfd.of (n := n) X) h𝔞]
    exact GiraudAlong.isClosed_cosupport_along hdom.isWellFormed.isCoherent hdom.isWellFormed.isClosedSubmanifold_N _
  exact exists_principalization_boundary h𝔞 hne hclosed.isCompact hE₀

end

end Hironaka.HironakaPrincipalizationBoundary
