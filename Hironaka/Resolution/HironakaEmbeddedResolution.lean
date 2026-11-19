import Hironaka.Resolution.HironakaPrincipalization
import Hironaka.Resolution.HironakaFromSeqInvariant
import Hironaka.Coherence.CartanIrreducible

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Embedded resolution with a normal-crossings exceptional divisor (Hironaka)

Blueprint `hir:embedded-resolution-snc` (`blueprint/src/hironaka.tex`; TN.5, the Hironaka strengthening (H+1) for the
standalone library).  Sources: Włodarczyk 2005 (`hiron.tex`), Theorem 1.0.2 (embedded desingularization); Bierstone--Milman
2008 (`bierstone-milman08-functoriality`), Theorem 1.2; Kollár 2007, Theorem 3.36.

**Statement.**  Let `X` be a compact complex manifold and `V ⊆ X` a closed irreducible analytic subvariety.  There is a finite
sequence of blowups with smooth centres `f : X' → X` and a divisor `E = (E₁, …, E_r)` on `X'` with simple normal crossings
such that

* the exceptional locus of `f` lies in `E₁ ∪ ⋯ ∪ E_r`, which lies over `V_sing`; so `f` is an isomorphism over `X \ V_sing`;
* the strict transform `V'` of `V` is a closed connected submanifold of dimension `dim V`;
* `V'` has only normal crossings with `E`.

(The divisor `E` is the support of the exceptional divisor of the tower, which lies over `V_sing`.  The two inclusions are in
fact equalities, `Exc f = E₁ ∪ ⋯ ∪ E_r = f⁻¹(V_sing)`: `HironakaEmbeddedExceptional.exists_embeddedResolution_exceptional`.)

**Route.**  The first-centre argument of `EmbeddedFromResolution` (`hir:embedded-from-resolution`) for the canonical resolution
of `(X, X, [], 𝓘_V, 1)` (`CanonicalCentres.canonicalInvariant`, coherence of `𝓘_V` by Cartan's theorem
`CartanIrreducible.cartanCoherence`): stop before the first centre `C` meeting the preimage of `X \ V_sing`; the strict transform
is the connected component of `C` through a point over `X \ V_sing`.  New here: `C` is an admissible centre of the transform, so
it has only normal crossings with the transformed divisor, and so has each of its connected components
(`hasNormalCrossings_connectedComponentIn`); the transformed divisor has simple normal crossings and its union is the support of
the exceptional divisor of the tower (`HironakaPrincipalization.support_exceptionalDivisor_eq_biUnion`), which contains the
exceptional locus and lies over `V_sing` because every centre so far does (`support_exceptionalDivisor_subset_of_centresAvoid`).

## Main results

* `eventually_mem_connectedComponentIn_iff`, `hasNormalCrossings_connectedComponentIn`: a connected component of a closed
  submanifold agrees with it near each of its points, so it inherits normal crossings with a divisor;
* `support_exceptionalDivisor_subset_of_centresAvoid`: if no centre of `T` meets the preimage of `U`, the support of the
  exceptional divisor of `T` lies over `X \ U`;
* **`exists_tower_embeddedResolution`** (tower form, `dim V < n`) and **`exists_embeddedResolution`** (the public statement).

Import discipline (standalone Hironaka library): this module imports the resolution machinery (`HironakaPrincipalization`,
`HironakaFromSeqInvariant`, hence `CanonicalCentres`) and Cartan's coherence theorem (`CartanIrreducible`); it does not import,
even transitively, `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold

universe u

namespace Hironaka.HironakaEmbeddedResolution

open Hironaka.NonKahlerLocus Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings
  Hironaka.RestrictEmptyTower Hironaka.RegularLocusComponent
  Hironaka.EmbeddedFromResolution
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Connected components of a closed submanifold -/

section Local

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A connected component of a closed submanifold agrees with it near each of its points**: every point of a closed
submanifold is regular, so its connected components are the components of its regular locus, which are open in it. -/
theorem eventually_mem_connectedComponentIn_iff {C : Set M} (hC : IsClosedSubmanifold n C) {c x : M}
    (hx : x ∈ connectedComponentIn C c) :
    ∀ᶠ y in 𝓝 x, y ∈ connectedComponentIn C c ↔ y ∈ C := by
  have hcC : c ∈ C := connectedComponentIn_nonempty_iff.mp ⟨x, hx⟩
  obtain ⟨k, hk⟩ := hC.2 c hcC
  have hRC : regularPoints (n := n) C = C :=
    Subset.antisymm (regularPoints_subset C) fun y hy => hC.2 y hy
  have hKC : component (n := n) C c = connectedComponentIn C c := by
    show connectedComponentIn (regularPoints (n := n) C) c = _
    rw [hRC]
  have hxK : x ∈ component (n := n) C c := by rw [hKC]; exact hx
  obtain ⟨W, hW, hxW, hWC⟩ := exists_open_inter_subset_component hk hxK
  filter_upwards [hW.mem_nhds hxW] with y hyW
  refine ⟨fun h => connectedComponentIn_subset C c h, fun h => ?_⟩
  rw [← hKC]
  exact hWC ⟨h, hyW⟩

/-- **A connected component of a closed submanifold with normal crossings with `E` has normal crossings with `E`.** -/
theorem hasNormalCrossings_connectedComponentIn {C : Set M} (hC : IsClosedSubmanifold n C) {E : List (Set M)}
    (h : HasNormalCrossings n C E) (c : M) : HasNormalCrossings n (connectedComponentIn C c) E :=
  CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually fun _ hx =>
    ⟨C, connectedComponentIn_subset C c hx, eventually_mem_connectedComponentIn_iff hC hx, h⟩

end Local

/-! ### The exceptional divisor of a tower whose centres avoid an open set -/

section Tower

variable {X : CMfd.{u} n}

/-- **If no centre of `T` meets the preimage of `U`, the support of the exceptional divisor of `T` lies over `X \ U`**: after
a blowup `π` along `C` the support is `π⁻¹(supp E_T) ∪ π⁻¹ C`, and `C` misses the preimage of `U`. -/
theorem support_exceptionalDivisor_subset_of_centresAvoid (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresAvoid U T →
      (BlowupTowerTransforms.exceptionalDivisor T).support ⊆ T.proj ⁻¹' (U : Set X)ᶜ
  | _, .refl, _ => by
      intro x hx
      exact absurd (hx (fun _ => (1 : ℂ)) (holomorphicAt_const 1)) one_ne_zero
  | _, .step T C π hπ, h => by
      obtain ⟨hT, hdisj⟩ : CentresAvoid U T ∧ Disjoint C (T.proj ⁻¹' (U : Set X)) := h
      have ih := support_exceptionalDivisor_subset_of_centresAvoid U T hT
      show (GermIdealTotalTransform.EffectiveDivisor.add
          (BlowupExceptionalDivisor.totalTransform hπ (BlowupTowerTransforms.exceptionalDivisor T))
          (BlowupExceptionalDivisor.exceptionalDivisor hπ)).support ⊆ _
      rw [HironakaPrincipalization.support_add, BlowupExceptionalDivisor.support_totalTransform,
        BlowupExceptionalDivisor.support_exceptionalDivisor]
      rintro z (hz | hz)
      · exact ih hz
      · exact fun hzU => Set.disjoint_left.mp hdisj hz hzU

/-- **Embedded resolution, tower form** (`dim V < n`, `𝓘_V` coherent): a multiple test blow-up `T` of `(X, X, [], 𝓘_V, 1)`
whose strict transform of `V` is regular of dimension `dim V` at each of its points, whose transformed divisor `E` has simple
normal crossings with union the support of the exceptional divisor `E_T`, which contains the exceptional locus of `T` and lies
over `V_sing`, and such that the strict transform has only normal crossings with `E`. -/
theorem exists_tower_embeddedResolution [CompactSpace X] (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.dim < n)
    (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T ∧
      (∀ x ∈ strictTransform n T.proj V.carrier,
        RegularAtDim (n := n) (strictTransform n T.proj V.carrier) x V.dim) ∧
      IsSNCDivisor n (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).E ∧
      (BlowupTowerTransforms.exceptionalDivisor T).support =
        ⋃ H ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).E, H ∧
      exceptionalLocus n T.proj ⊆ (BlowupTowerTransforms.exceptionalDivisor T).support ∧
      (BlowupTowerTransforms.exceptionalDivisor T).support ⊆ T.proj ⁻¹' singularLocus V ∧
      HasNormalCrossings n (strictTransform n T.proj V.carrier)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).E := by
  set 𝔪 : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ with h𝔪
  have hdom : IsInvDomain n 𝔪 := isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV hcoh
  set R := CanonicalCentres.canonicalInvariant.{u} n with hR
  have hF := HironakaFromSeqInvariant.embeddingFields_of_seq R
  obtain ⟨Z, T, hcan, hres⟩ := ResolutionInvariantSeq.exists_isGeoResolution_isCanonical R hdom
  have hTt := hF.isGeoTestTower_of_isCanonical hdom T hcan
  obtain ⟨Y', T', -, -, h1, h2, c, hc, hcU⟩ := exists_first_centre _ _ (regularOpen V) T hcan
    (not_centresAvoid_of_cosupp_eq_empty V hdom T hTt hres.2)
  have hT't := hF.isGeoTestTower_of_isCanonical hdom T' h1
  have hadm := hF.isAdmissibleCentre_maxLocus hdom T' h1 hT't
  obtain ⟨-, hST, hreg⟩ := strictTransform_eq_connectedComponentIn_maxLocus hF V hdom T' h1 h2 hc hcU
  refine ⟨Y', T', hT't, hreg, ?_, HironakaPrincipalization.support_exceptionalDivisor_eq_biUnion 𝔪 rfl T',
    HironakaPrincipalization.exceptionalLocus_subset_support T', ?_, ?_⟩
  · exact (InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom T' hT't).isWellFormed.isSNCDivisor
  · intro z hz
    have hz' := support_exceptionalDivisor_subset_of_centresAvoid (regularOpen V) T' h2 hz
    by_contra hzs
    exact hz' ((mem_regularOpen_iff (V := V)).mpr hzs)
  · rw [hST]
    exact hasNormalCrossings_connectedComponentIn hadm.1 hadm.2.2 c

end Tower

/-! ### The public statement -/

/-- **Embedded resolution with a normal-crossings exceptional divisor** (Hironaka; `hir:embedded-resolution-snc`): for a
closed irreducible analytic subvariety `V` of a compact complex manifold `X` there are a finite sequence of blowups with smooth
centres `f : X' → X` and a divisor `E` on `X'` with simple normal crossings such that the exceptional locus of `f` lies in
`⋃ E`, `⋃ E` lies over `V_sing`, `f` is an isomorphism over `X \ V_sing`, the strict transform of `V` is a closed connected
submanifold of dimension `dim V`, and it has only normal crossings with `E`. -/
theorem exists_embeddedResolution {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X] (V : ClosedIrreducibleAnalyticSubvariety n X) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (_ : IsBlowupSequence n X X' f) (E : List (Set X')),
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) ⊆ f ⁻¹' singularLocus V ∧
      IsIsomorphismOver n f (singularLocus V)ᶜ ∧
      IsClosedConnectedSubmanifold n (strictTransform n f V.carrier) V.dim ∧
      HasNormalCrossings n (strictTransform n f V.carrier) E := by
  rcases V.dim_le.lt_or_eq with h | h
  · have : CompactSpace (CMfd.of (n := n) X) := ‹CompactSpace X›
    obtain ⟨Y, T, -, hreg, hsnc, hsupp, hexc, hsing, hnc⟩ :=
      exists_tower_embeddedResolution (X := CMfd.of (n := n) X) V h
        (CartanIrreducible.cartanCoherence V.carrier V.irreducible_carrier.analytic)
    have hexcS : T.proj '' exceptionalLocus n T.proj ⊆ singularLocus V := by
      rintro x ⟨z, hz, rfl⟩
      exact hsing (hexc hz)
    refine ⟨Y, inferInstance, inferInstance, inferInstance, T.proj, T.isBlowupSequence, _, hsnc, ?_, ?_,
      BlowupSequenceIsomorphismOff.isIsomorphismOver_compl_of_image_exceptionalLocus_subset T.isBlowupSequence hexcS,
      ⟨isClosed_closure,
        StrictTransformSubvarietySequence.isConnected_strictTransform_of_isBlowupSequence T.isBlowupSequence V hexcS,
        hreg⟩, hnc⟩
    · rw [← hsupp]
      exact hexc
    · rw [← hsupp]
      exact hsing
  · have hV := isClosedConnectedSubmanifold_of_dim_eq V h
    have hst : strictTransform n (id : X → X) V.carrier = V.carrier := by
      simp [strictTransform, exceptionalLocus_id, V.isClosed_carrier.closure_eq]
    refine ⟨X, inferInstance, inferInstance, inferInstance, id, IsBlowupSequence.refl, [], isSNCDivisor_nil, ?_, ?_,
      BlowupSequenceIsomorphismOff.isIsomorphismOver_compl_of_image_exceptionalLocus_subset IsBlowupSequence.refl
        (by simp [exceptionalLocus_id]), ?_, ?_⟩
    · simp [exceptionalLocus_id]
    · simp
    · rw [hst, h]
      exact hV
    · rw [hst]
      exact hasNormalCrossings_nil_of_isClosedSubmanifold
        (FactorizationDomain.isClosedSubmanifold_of_isClosedConnectedSubmanifold hV)

end

end Hironaka.HironakaEmbeddedResolution
