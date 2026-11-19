import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.GlobalAnalyticSingularities
import Hironaka.Analytic.NumericalRestrictedVolume
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.NonKahlerLocusPoleSet
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Blowup.BlowupConnected
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.Resolution.RelativePrincipalizationIsomorphismOpen
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Resolution.HironakaFromSeqInvariant

set_option autoImplicit false

/-!
# Relative principalization

Source: Copy-4, `lem:relative-principalization` and the preceding paragraph on
sequences of blowups adapted to a submanifold
(`transcendental-nakamaye-copy4-20260911`); blueprint
`ana:relative-principalization`.

Let `Y` be a connected compact complex manifold, `W ⊊ Y` a nonempty closed connected
submanifold, and `𝔞 ⊆ 𝒪_Y` a coherent ideal with `𝔞 ⊄ 𝓘_W` (equivalently
`Res_W 𝔞 ≠ 0`).  There is a sequence of blowups `f : Y' → Y` adapted to `W`, with
smooth connected strict transform `W'`, an isomorphism over a nonempty open
subset of `W`, and effective divisors `H, H'` with `H` exceptional, `H'` disjoint
from `W'`, no component of `H` containing `W'`, and

* `𝓘_W 𝒪_{Y'} = 𝒪_{Y'}(-H) 𝓘_{W'}`,
* `𝔞 𝒪_{Y'} = 𝒪_{Y'}(-H-H')`,
* `(Res_W 𝔞) 𝒪_{W'} = 𝒪_{W'}(-H|_{W'})`.

Encoding notes.  `𝒪(-H-H')` is the product ideal `𝒪(-H) 𝒪(-H')`.  Since `W'`
is connected (hence analytically irreducible), no component of `H` contains `W'`
exactly when `W' ⊄ supp H`.  An ideal of `𝒪_{W'}` is determined by which ambient
holomorphic germs restrict into it, because every holomorphic germ on a closed
submanifold is the restriction of an ambient germ; `(Res_W 𝔞) 𝒪_{W'}` is generated
by the restrictions of `a ∘ f` for germs `a` of `𝔞`, and `𝒪_{W'}(-H|_{W'})` by the
restrictions of the germs of `𝒪(-H)`.  "An isomorphism over a nonempty open
subset of `W`" is `IsIsomorphismOver f U` for an open `U ⊆ Y` meeting `W`.
Connectedness of `Y` is the manuscript's standing situation (every application
has `Y` connected) and is needed: for `Y = Y₁ ⊔ Y₂` with `W ⊆ Y₁` and `𝔞 = 0` on
`Y₂`, no blowup sequence makes `𝔞 𝒪_{Y'}` invertible; and for `Y = ℙ¹ ⊔ ℙ¹`,
`W` the first copy, `𝔞` the ideal of a point of `W`, the conclusion fails as well.
With `Y` connected, `W ≠ Y` forces `k < n`.  The conclusion records that `Y'` is
again connected and compact, which the manuscript uses when it applies the lemma
a second time.

The geometric core `exists_factorizationData` is proved from the canonical resolution
invariant (`CanonicalCentres.canonicalInvariant`) through
`HironakaFromSeqInvariant.factorizationData_of_seq`; the rest of the file derives the full
statement from it.
-/

open Set Filter

universe u

namespace Hironaka.RelativePrincipalization

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.GlobalAnalyticSingularities Hironaka.NumericalRestrictedVolumeScaffold
  Hironaka.PositiveClasses Hironaka.NonKahlerLocus Hironaka.NumericalRestrictedVolume
  NonKahlerLocusPoleSet RelativePrincipalizationSpan

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/- An analytic singularity type whose potential is finite at one point of `W`
has a coherent ideal whose restriction to `W` is nonzero.

This supplies exactly the ideal-theoretic input of relative principalization:
at a finite point, one local generator is nonzero, hence that generator cannot
vanish identically along `W`. -/
omit [IsComplexManifold n Y] in
theorem analyticSingularityType_not_le_vanishingIdeal_of_not_pole
    {φ : Y → EReal} {c : ℚ} {𝔞 : GermIdeal n Y}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    {W : Set Y} {x : Y} (hxW : x ∈ W) (hxP : x ∉ poleSet φ) :
    ¬ 𝔞.Le (vanishingIdeal (n := n) W) := by
  rcases hφ with ⟨hcQ, hcoh, hlocal⟩
  obtain ⟨U, hU, hxU, N, g, hgDiff, hgMem, R, C, hRC, hformula⟩ := hlocal x
  have hc : 0 < (c : ℝ) := by exact_mod_cast hcQ
  change φ x ≠ ⊥ at hxP
  have hnonzero : ∃ j, g j x ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hxP
    rw [hformula x hxU]
    exact (scaled_generatorLog_add_eq_bot_iff g x hc (R x)).mpr hzero
  rcases hnonzero with ⟨j, hj⟩
  intro hle
  have hgj : HolomorphicAt n (g j) x := by
    rw [HolomorphicAt]
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact (hgDiff j y hy).mdifferentiableAt (hU.mem_nhds hy)
  have hone : HolomorphicAt n (fun _ : Y => (1 : ℂ)) x := by
    rw [HolomorphicAt]
    filter_upwards with y
    exact mdifferentiableAt_const (c := (1 : ℂ))
  have hmem : 𝔞.mem x (g j) := (hgMem x hxU (g j)).mpr (by
    refine ⟨hgj, 1, fun _ => g j, fun _ => 1, ?_, ?_, ?_⟩
    · intro i
      exact ⟨j, rfl⟩
    · intro i
      exact hone
    · filter_upwards with y
      simp)
  rcases hle x (g j) hmem with ⟨-, hzero⟩
  exact hj (hzero.self_of_nhds hxW)

/- A potential with analytic singularities that is finite somewhere on `W`
therefore supplies a coherent ideal admissible for relative principalization. -/
omit [IsComplexManifold n Y] in
theorem exists_coherentIdeal_not_le_vanishingIdeal_of_hasAnalyticSingularities
    {φ : Y → EReal} (hφ : HasAnalyticSingularities (n := n) φ)
    {W : Set Y} {x : Y} (hxW : x ∈ W) (hxP : x ∉ poleSet φ) :
    ∃ 𝔞 : GermIdeal n Y, 𝔞.IsCoherent ∧ ¬ 𝔞.Le (vanishingIdeal (n := n) W) := by
  rcases hφ with ⟨c, 𝔞, hφ⟩
  exact ⟨𝔞, hφ.2.1,
    analyticSingularityType_not_le_vanishingIdeal_of_not_pole hφ hxW hxP⟩

/- A positive numerical restricted volume puts the subvariety off `E_nn`.
This is the formal contrapositive of the zero-volume convention. -/
theorem not_subset_nonNefLocus_of_numericalRestrictedVolume_pos
    (omega : KahlerBackground n Y) (alpha : RealBottChern n Y)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hvolume : 0 < numericalRestrictedVolume omega alpha W) :
    ¬ W.carrier ⊆ nonNefLocus omega alpha := by
  intro hW
  exact (ne_of_gt hvolume)
    (numericalRestrictedVolume_eq_zero_of_subset_nonNefLocus omega alpha W hW)

/- Off the non-nef locus, a big class supplies a coherent ideal whose
restriction to the chosen set is nonzero.  The only non-elementary input here
is the existing analytic Kähler-current regularization theorem, used for a
positive Kähler perturbation of the class. -/
theorem exists_coherentIdeal_not_le_vanishingIdeal_of_not_subset_nonNefLocus
    [CompactSpace Y] (hn : 0 < n) (omega : KahlerBackground n Y)
    (alpha : RealBottChern n Y) (hbig : IsBigClass alpha)
    {W : Set Y} (hWnn : ¬ W ⊆ nonNefLocus omega alpha) :
    ∃ 𝔞 : GermIdeal n Y, 𝔞.IsCoherent ∧ ¬ 𝔞.Le (vanishingIdeal (n := n) W) := by
  obtain ⟨x, hxW, hxnn⟩ := Set.not_subset.mp hWnn
  let ε : PositiveError := ⟨1, one_pos⟩
  have hxNK : x ∉ nonKahlerLocus
      (alpha + (ε : ℝ) • RealBottChern.ofRepresentative omega.form) := by
    intro hx
    exact hxnn (mem_nonNefLocus.mpr ⟨ε, hx⟩)
  obtain ⟨T⟩ := hbig
  have hbigε : IsBigClass
      (alpha + (ε : ℝ) • RealBottChern.ofRepresentative omega.form) :=
    ⟨T.addSmulKahler omega ε.2⟩
  obtain ⟨S, hS, -, hSpole⟩ :=
    exists_kahlerCurrent_poleSet_eq_nonKahlerLocus hn _ hbigε
  exact exists_coherentIdeal_not_le_vanishingIdeal_of_hasAnalyticSingularities hS hxW (by
    rwa [hSpole])

/- Thus the positive restricted-volume hypothesis provides the exact coherent
ideal input required by `exists_relativePrincipalization`. -/
theorem exists_coherentIdeal_not_le_vanishingIdeal_of_numericalRestrictedVolume_pos
    [CompactSpace Y] (hn : 0 < n) (omega : KahlerBackground n Y)
    (alpha : RealBottChern n Y) (hbig : IsBigClass alpha)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hvolume : 0 < numericalRestrictedVolume omega alpha W) :
    ∃ 𝔞 : GermIdeal n Y, 𝔞.IsCoherent ∧
      ¬ 𝔞.Le (vanishingIdeal (n := n) W.carrier) :=
  exists_coherentIdeal_not_le_vanishingIdeal_of_not_subset_nonNefLocus hn omega alpha hbig
    (not_subset_nonNefLocus_of_numericalRestrictedVolume_pos omega alpha W hvolume)

/-- The geometric factorization output of relative principalization, before the
formal comparison of restricted ideal spans is attached. -/
def FactorizationData (W : Set Y) (k : ℕ) (𝔞 : GermIdeal n Y) : Prop :=
  ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y')
    (_ : IsComplexManifold n Y') (f : Y' → Y),
    IsAdaptedBlowupSequence n Y W Y' f ∧
    IsConnected (strictTransform n f W) ∧
    (∀ x ∈ strictTransform n f W,
      RegularAtDim (n := n) (strictTransform n f W) x k) ∧
    ∃ H H' : EffectiveDivisor n Y',
      H.support ⊆ exceptionalLocus n f ∧
      Disjoint H'.support (strictTransform n f W) ∧
      GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) W) =
        H.ideal.mul (vanishingIdeal (n := n) (strictTransform n f W)) ∧
      GermIdeal.pullback (m := n) f 𝔞 = H.ideal.mul H'.ideal

/-- **Relative principalization, geometric core** (Copy-4,
`lem:relative-principalization`).  This is the part of the lemma that is
Hironaka's: the adapted modification, its connected regular strict transform, and
its divisor factorizations.  It is proved from the canonical resolution invariant
`CanonicalCentres.canonicalInvariant n` through
`HironakaFromSeqInvariant.factorizationData_of_seq`.  Closedness of the strict transform and the local
isomorphism open set are reconstructed below from the sequence.  The restricted
span comparison is reconstructed from the same data. -/
theorem exists_factorizationData [CompactSpace Y] [ConnectedSpace Y]
    (W : Set Y) (k : ℕ) (hW : IsClosedConnectedSubmanifold n W k) (hWY : W ≠ univ)
    (𝔞 : GermIdeal n Y) (h𝔞 : 𝔞.IsCoherent) (hres : ¬ 𝔞.Le (vanishingIdeal (n := n) W)) :
    FactorizationData W k 𝔞 := by
  exact HironakaFromSeqInvariant.factorizationData_of_seq (CanonicalCentres.canonicalInvariant n) le_rfl W k hW hWY 𝔞 h𝔞 hres

/-- The local span algebra upgrades factorization-only relative
principalization to the original statement. -/
theorem exists_relativePrincipalization_of_factorizationData [CompactSpace Y] [ConnectedSpace Y]
    (W : Set Y) (k : ℕ) (𝔞 : GermIdeal n Y) (h𝔞 : 𝔞.IsCoherent)
    (hdata : FactorizationData W k 𝔞) :
    ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y')
      (_ : IsComplexManifold n Y') (f : Y' → Y),
      IsAdaptedBlowupSequence n Y W Y' f ∧ CompactSpace Y' ∧ ConnectedSpace Y' ∧
      IsClosedConnectedSubmanifold n (strictTransform n f W) k ∧
      (∃ U : Set Y, IsOpen U ∧ (U ∩ W).Nonempty ∧ IsIsomorphismOver n f U) ∧
      ∃ H H' : EffectiveDivisor n Y',
        H.support ⊆ exceptionalLocus n f ∧
        Disjoint H'.support (strictTransform n f W) ∧
        ¬ strictTransform n f W ⊆ H.support ∧
        GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) W) =
          H.ideal.mul (vanishingIdeal (n := n) (strictTransform n f W)) ∧
        GermIdeal.pullback (m := n) f 𝔞 = H.ideal.mul H'.ideal ∧
        ∀ y ∈ strictTransform n f W, ∀ g : Y' → ℂ, HolomorphicAt n g y →
          (IsInSpanOnAt (n := n) (strictTransform n f W)
              (fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f) y g ↔
            IsInSpanOnAt (n := n) (strictTransform n f W) (H.ideal.mem y) y g) := by
  obtain ⟨Y', instTop, instChart, instComplex, f, hseq, hWconn,
    hWreg, H, H', hHexc, hH'disj, hvanish, hideal⟩ := hdata
  have hcompact : CompactSpace Y' :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective
      hseq.isBlowupSequence).1
  have hconnected : ConnectedSpace Y' :=
    BlowupConnected.connectedSpace_of_isBlowupSequence f hseq.isBlowupSequence
  have hW' : IsClosedConnectedSubmanifold n (strictTransform n f W) k :=
    ⟨isClosed_closure, hWconn, hWreg⟩
  obtain ⟨U, hUopen, hUW, hUiso⟩ :=
    RelativePrincipalizationIsomorphismOpen.exists_open_meets_isIsomorphismOver_of_strictTransform_nonempty
      hseq.isBlowupSequence hWconn.nonempty
  obtain ⟨x, hxU, hxW⟩ := hUW
  obtain ⟨y, hyU, hyfx⟩ := hUiso.1.surjOn hxU
  have hyW : y ∈ f ⁻¹' W := by
    change f y ∈ W
    rwa [hyfx]
  have hyExc : y ∉ exceptionalLocus n f := by
    intro hyExc
    exact Set.disjoint_left.mp hUiso.2 hyU hyExc
  have hyStrict : y ∈ strictTransform n f W := by
    change y ∈ closure (f ⁻¹' W \ exceptionalLocus n f)
    exact subset_closure ⟨hyW, hyExc⟩
  have hHnot : ¬ strictTransform n f W ⊆ H.support := by
    intro hsub
    exact hyExc (hHexc (hsub hyStrict))
  refine ⟨Y', instTop, instChart, instComplex, f, hseq, hcompact, hconnected, hW',
    ⟨U, hUopen, ⟨x, hxU, hxW⟩, hUiso⟩, H, H', hHexc, hH'disj, hHnot, hvanish, hideal, ?_⟩
  intro y hy g _
  exact isInSpanOnAt_pullback_iff_divisor_of_factorization hseq.contMDiff h𝔞 hideal hH'disj hy

/-- **Relative principalization** (Copy-4, `lem:relative-principalization`).
This compatibility theorem retains the original public conclusion; it is derived
from the factorization-only Hironaka core above. -/
theorem exists_relativePrincipalization [CompactSpace Y] [ConnectedSpace Y]
    (W : Set Y) (k : ℕ) (hW : IsClosedConnectedSubmanifold n W k) (hWY : W ≠ univ)
    (𝔞 : GermIdeal n Y) (h𝔞 : 𝔞.IsCoherent) (hres : ¬ 𝔞.Le (vanishingIdeal (n := n) W)) :
    ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y')
      (_ : IsComplexManifold n Y') (f : Y' → Y),
      IsAdaptedBlowupSequence n Y W Y' f ∧ CompactSpace Y' ∧ ConnectedSpace Y' ∧
      IsClosedConnectedSubmanifold n (strictTransform n f W) k ∧
      (∃ U : Set Y, IsOpen U ∧ (U ∩ W).Nonempty ∧ IsIsomorphismOver n f U) ∧
      ∃ H H' : EffectiveDivisor n Y',
        H.support ⊆ exceptionalLocus n f ∧
        Disjoint H'.support (strictTransform n f W) ∧
        ¬ strictTransform n f W ⊆ H.support ∧
        GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) W) =
          H.ideal.mul (vanishingIdeal (n := n) (strictTransform n f W)) ∧
        GermIdeal.pullback (m := n) f 𝔞 = H.ideal.mul H'.ideal ∧
        ∀ y ∈ strictTransform n f W, ∀ g : Y' → ℂ, HolomorphicAt n g y →
          (IsInSpanOnAt (n := n) (strictTransform n f W)
              (fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f) y g ↔
            IsInSpanOnAt (n := n) (strictTransform n f W) (H.ideal.mem y) y g) :=
  exists_relativePrincipalization_of_factorizationData W k 𝔞 h𝔞
    (exists_factorizationData W k hW hWY 𝔞 h𝔞 hres)

end

end Hironaka.RelativePrincipalization
