import Hironaka.Resolution.HironakaG3RPureBoundary
import Hironaka.Resolution.HironakaG3RFinalGlobal
import Hironaka.Resolution.HironakaEmbeddedDimensionParts

/-! # G3 under target (A): the final statement for every closed analytic set of pure dimension

Lane G3 (run 0080, round 5).  Blueprint: `hironaka-g3-r-pure-final.tex`.

* `isOpen_of_pure_of_le`, `diff_regularLocus_eq_empty_of_le`: a closed analytic set of pure dimension `d ≥ n` is open (a union
  of connected components of `X`, or empty) and regular of dimension `d` at each of its points, so `W_sing = ∅`.
* `identity_resolution_of_le` (**the trivial case `dim W = n`**): the identity of `X` is then an embedded resolution:
  `Exc id = ∅ = id⁻¹ W_sing`, an isomorphism everywhere, strict transform `W` a closed submanifold of dimension `d`, and the
  empty boundary is a locally finite simple normal crossings family with which `W` has normal crossings.
* **`g3_final_global_pure`**: on every complex manifold `X` (not necessarily compact),
  (a) as in `HironakaG3RFinalGlobal.g3_final_global` (glued canonical resolutions of marked ideals);
  (b) for EVERY closed analytic `W` of pure dimension `d` (possibly reducible; `d ≤ n`, the case `d = n` included): a proper
  holomorphic surjection `P : X' → X` with `Exc P = P⁻¹ W_sing` a locally finite indexed simple normal crossings divisor with
  which the strict transform of `W` (a closed submanifold of dimension `d`) has only normal crossings, `P` an isomorphism over
  `X ∖ W_sing`; for `d < n` it is the glued embedded resolution of `(W, d)` (unique up to unique biholomorphism over `X`, a
  single stopped canonical prefix over every relatively compact open set), and for `d ≥ n` it is a biholomorphism;
  (c) every closed analytic set `W` (not necessarily pure dimensional) is the finite union `⋃_{k ≤ n} W⁽ᵏ⁾` of its dimension
  parts `W⁽ᵏ⁾ = closure (regularLocus W k)`, each a closed analytic set of pure dimension `k` contained in `W`, to which (b)
  applies.  (This is NOT one embedded resolution of a non-equidimensional `W`; see `HironakaEmbeddedDimensionParts`.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RPureFinal

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals NormalCrossings
  HironakaG3RGluedUniqueness HironakaG3RTowerClass HironakaG3RPureEmbedded
open ResolutionInvariantSpec (IsInvDomain)
open HironakaActualIndexedBoundaryContinuation (HasNormalCrossingsWithBoundary)
open HironakaActualLocallyFiniteBoundary (IsLocallyFiniteSNCDivisor)
open HironakaEmbeddedDimensionParts (dimensionPart)

variable {n : ℕ}

/-! ### The trivial case `dim W ≥ n` -/

section Top

variable {X : CMfd.{u} n} {W : Set X}

/-- **A closed analytic set of pure dimension `d ≥ n` is open and regular of dimension `d` at each of its points**: its
regular points of dimension `d` (necessarily `d = n`) are interior points, it lies in their closure, and the interior of an
analytic set is closed. -/
theorem isOpen_of_pure_of_le (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : n ≤ d)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) : IsOpen W ∧ ∀ x ∈ W, RegularAtDim (n := n) W x d := by
  have hreg : regularLocus (n := n) W d ⊆ interior W := fun y hy => by
    have hdn : d = n := le_antisymm hy.1 hd
    have hy' : RegularAtDim (n := n) W y n := hdn ▸ hy
    exact mem_interior_iff_mem_nhds.mpr (EmbeddedFromResolution.mem_nhds_of_regularAtDim_self hy')
  have hWi : W ⊆ interior W := hpure.trans ((closure_mono hreg).trans hWa.isClosed_interior.closure_subset)
  have hWo : IsOpen W := interior_eq_iff_isOpen.mp (Subset.antisymm interior_subset hWi)
  refine ⟨hWo, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ : (regularLocus (n := n) W d).Nonempty := by
    by_contra h
    have h' := hpure hx
    rw [not_nonempty_iff_eq_empty.mp h, closure_empty] at h'
    exact h'
  have hdn : d = n := le_antisymm hy.1 hd
  rw [hdn]
  exact EmbeddedFromResolution.regularAtDim_of_mem_nhds (hWo.mem_nhds hx)

theorem diff_regularLocus_eq_empty_of_le (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : n ≤ d)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) : W \ regularLocus (n := n) W d = ∅ :=
  eq_empty_of_forall_notMem fun x hx => hx.2 ((isOpen_of_pure_of_le hWa hd hpure).2 x hx.1)

/-- **The trivial case `dim W ≥ n`: the identity is an embedded resolution.** -/
theorem identity_resolution_of_le (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : n ≤ d)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    exceptionalLocus n (id : X → X) = id ⁻¹' (W \ regularLocus (n := n) W d) ∧
      IsIsomorphismOver n (id : X → X) (W \ regularLocus (n := n) W d)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n (id : X → X) W) ∧
      (∀ z ∈ strictTransform n (id : X → X) W,
        RegularAtDim (n := n) (strictTransform n (id : X → X) W) z d) ∧
      ∃ (ι : Type u) (D : ι → Set X), IsLocallyFiniteSNCDivisor n D ∧ (∀ i, (D i).Nonempty) ∧
        (⋃ i, D i) = exceptionalLocus n (id : X → X) ∧
        HasNormalCrossingsWithBoundary (strictTransform n (id : X → X) W) D := by
  obtain ⟨-, hreg⟩ := isOpen_of_pure_of_le hWa hd hpure
  have hst : strictTransform n (id : X → X) W = W := by
    simp [strictTransform, exceptionalLocus_id, hWa.isClosed.closure_eq]
  have hsing := diff_regularLocus_eq_empty_of_le hWa hd hpure
  rw [hst, hsing, exceptionalLocus_id, preimage_empty, compl_empty]
  refine ⟨rfl, ⟨bijOn_id _, by rw [exceptionalLocus_id]; exact disjoint_empty _⟩, ⟨hWa.isClosed, fun x hx => ⟨d, hreg x hx⟩⟩, hreg,
    PEmpty.{u + 1}, fun i => i.elim, ⟨locallyFinite_of_finite _, fun i => i.elim, fun x =>
      ⟨fun i => i.elim, isCoordinateFamilyAt_of_isEmpty _ _ x, fun i => i.elim, fun i => i.elim⟩⟩,
    fun i => i.elim, iUnion_of_empty _, fun x hx => ?_⟩
  obtain ⟨-, -, Φ, hsrc, h0, hflat⟩ := hreg x hx
  refine ⟨Finset.univ.filter fun j : Fin n => d ≤ j.1, fun i => i.elim, ⟨Φ, hsrc, h0, ?_⟩, fun i => i.elim⟩
  rintro (_ | i) _ y hy hyΦ
  · simpa [coordSubspace_eq_complexCoordinatePlane] using hflat hy hyΦ
  · exact i.elim

end Top

/-! ### The final statement -/

/-- **The final G3 theorem under target (A), for every closed analytic set of pure dimension**, with global boundaries;
(a) is `HironakaG3RFinalGlobal.g3_final_global` (a). -/
theorem g3_final_global_pure (X : CMfd.{u} n) :
    (∀ M : MarkedIdeal n X, IsInvDomain n M →
      ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedCanonicalResolution M X' P ∧
        (∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedCanonicalResolution M X'' P' →
          ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
        (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K → ∃ c : GluedChart M X' P, c.U = U) ∧
        (∃ (ι : Type u) (D : ι → Set X'), IsLocallyFiniteSNCDivisor n D ∧ (∀ i, (D i).Nonempty) ∧
          (⋃ i, D i) = HironakaG3RGluedBoundary.gluedBoundary M X' P) ∧
        (M.N = univ → M.d = 1 →
          (GermIdeal.pullback (m := n) P M.ideal).IsInvertible ∧
            (GermIdeal.pullback (m := n) P M.ideal).zeroLocus = P ⁻¹' M.ideal.zeroLocus ∧
            IsIsomorphismOver n P M.ideal.zeroLocusᶜ)) ∧
    (∀ W : Set X, IsComplexAnalyticSubset (n := n) W → ∀ d : ℕ, W ⊆ closure (regularLocus (n := n) W d) →
      ∃ (X' : CMfd.{u} n) (P : X' → X),
        ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
        exceptionalLocus n P = P ⁻¹' (W \ regularLocus (n := n) W d) ∧
        IsIsomorphismOver n P (W \ regularLocus (n := n) W d)ᶜ ∧
        IsClosedSubmanifold n (strictTransform n P W) ∧
        (∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) ∧
        (∃ (ι : Type u) (D : ι → Set X'), IsLocallyFiniteSNCDivisor n D ∧ (∀ i, (D i).Nonempty) ∧
          (⋃ i, D i) = exceptionalLocus n P ∧ HasNormalCrossingsWithBoundary (strictTransform n P W) D) ∧
        (d < n → IsGluedPureResolution W d X' P ∧
          (∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedPureResolution W d X'' P' →
            ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
          (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
            ∃ c : TowerChart (embeddedClass W d) X' P, c.U = U)) ∧
        (n ≤ d → IsOpen W ∧ W \ regularLocus (n := n) W d = ∅ ∧
          ∃ Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X, ∀ z, Φ z = P z)) ∧
    (∀ W : Set X, IsComplexAnalyticSubset (n := n) W →
      W = ⋃ k : Fin (n + 1), dimensionPart (n := n) W k ∧
        ∀ k : Fin (n + 1), IsComplexAnalyticSubset (n := n) (dimensionPart (n := n) W k) ∧
          dimensionPart (n := n) W k ⊆ W ∧
          dimensionPart (n := n) W k ⊆ closure (regularLocus (n := n) (dimensionPart (n := n) W k) k)) := by
  refine ⟨(HironakaG3RFinalGlobal.g3_final_global X).1, fun W hWa d hpure => ?_, fun W hWa =>
    ⟨HironakaEmbeddedDimensionParts.eq_iUnion_dimensionPart hWa, fun k =>
      ⟨HironakaEmbeddedDimensionParts.isComplexAnalyticSubset_dimensionPart hWa k,
        HironakaEmbeddedDimensionParts.dimensionPart_subset hWa.isClosed k,
        HironakaEmbeddedDimensionParts.subset_closure_regularLocus_dimensionPart hWa.isClosed k⟩⟩⟩
  by_cases hd : d < n
  · obtain ⟨X', P, h, huniq⟩ := existsUnique_gluedPureResolution hWa hd hpure
    exact ⟨X', P, h.1, h.2.1, h.2.2.1, exceptionalLocus_eq hWa hd hpure h, isIsomorphismOver hWa hd hpure h,
      strictTransform_isClosedSubmanifold hWa hd hpure h, regularAtDim_strictTransform hWa hd hpure h,
      HironakaG3RPureBoundary.exists_globalBoundary hWa hd hpure h,
      fun _ => ⟨h, huniq, fun U K hK hUK => exists_chart_of_subset_isCompact hWa hd hpure h U hK hUK⟩,
      fun h' => absurd hd (not_lt.mpr h')⟩
  · have hd' : n ≤ d := not_lt.mp hd
    obtain ⟨he, hiso, hsub, hreg, hbd⟩ := identity_resolution_of_le hWa hd' hpure
    exact ⟨X, id, contMDiff_id, isProperMap_id, surjective_id, he, hiso, hsub, hreg, hbd,
      fun h' => absurd h' hd,
      fun _ => ⟨(isOpen_of_pure_of_le hWa hd' hpure).1, diff_regularLocus_eq_empty_of_le hWa hd' hpure,
        Diffeomorph.refl _ _ _, fun _ => rfl⟩⟩

end

end Hironaka.HironakaG3RPureFinal
