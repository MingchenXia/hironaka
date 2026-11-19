import Hironaka.Resolution.HironakaG3RBoundaryFinal

/-! # G3 under target (A): embedded resolution relative to a boundary in every pure dimension

Lane G3 (run 0080, round 6).  Blueprint: `hironaka-g3-r-boundary-top.tex`.

* `exists_family_of_isSNCDivisor`: a divisor with simple normal crossings in the list convention gives a locally finite
  indexed simple normal crossings family of nonempty closed sets with the same union (its nonempty members, via the held
  `HironakaActualLocallyFiniteBoundary.isLocallyFiniteSNCDivisor_boundaryReadout_iff`).
* `hasNormalCrossingsWithBoundary_of_isOpen`: an open set has only normal crossings with every locally finite indexed simple
  normal crossings family.
* `boundary_resolution_of_le` (**the trivial case `dim W ≥ n` relative to a boundary**): `W` is open and the identity is an
  embedded resolution of `W` relative to `E₀`.
* **`boundary_resolution`**: the boundary-relative embedded resolution for every closed analytic set of pure dimension `d`
  (`d < n`: the glued resolution of `HironakaG3RBoundaryEmbedded`; `d ≥ n`: the identity).
* **`g3_final_global_boundary_all`**: `HironakaG3RBoundaryFinal.g3_final_global_boundary` with (d) for every pure
  dimension.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RBoundaryTop

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals NormalCrossings
  HironakaG3RGluedUniqueness HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3RBoundaryEmbedded
  HironakaSharpActualCurveBirthBoundaryOverlaps
open ResolutionInvariantSpec (IsInvDomain)
open HironakaActualIndexedBoundaryContinuation (HasNormalCrossingsWithBoundary)
open HironakaActualLocallyFiniteBoundary (IsLocallyFiniteSNCDivisor)
open HironakaEmbeddedDimensionParts (dimensionPart)

variable {n : ℕ}

/-- **The nonempty members of a divisor with simple normal crossings form a locally finite indexed simple normal crossings
family with the same union.** -/
theorem exists_family_of_isSNCDivisor {X : CMfd.{u} n} {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) :
    ∃ (ι : Type u) (D : ι → Set X), IsLocallyFiniteSNCDivisor n D ∧ (∀ i, (D i).Nonempty) ∧
      (⋃ i, D i) = ⋃ H ∈ E₀, H := by
  obtain ⟨hlf, hcl, hco⟩ :=
    (HironakaActualLocallyFiniteBoundary.isLocallyFiniteSNCDivisor_boundaryReadout_iff E₀).mpr hE₀
  let ι : Type u := {k : ULift.{u} ℕ // (boundaryReadout E₀ k.down).Nonempty}
  let e : ι → ℕ := fun i => i.1.down
  have he : Injective e := fun i j h => Subtype.ext (ULift.ext _ _ h)
  refine ⟨ι, fun i => boundaryReadout E₀ (e i), ⟨hlf.comp_injective he, fun i => hcl (e i), fun x => ?_⟩,
    fun i => i.2, ?_⟩
  · obtain ⟨S, hA, hcard, hinj⟩ := hco x
    exact ⟨fun i => S (e i), NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hA e (fun _ => rfl) (fun _ => rfl),
      fun i hi => hcard (e i) hi, fun i hi j hj hij => he (hinj hi hj hij)⟩
  · ext z
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨i, hz⟩
      have hlt : e i < E₀.length := by
        by_contra hk
        have h0 : boundaryReadout E₀ (e i) = ∅ := List.getD_eq_default E₀ ∅ (Nat.le_of_not_gt hk)
        rw [h0] at hz
        exact hz
      have hget : boundaryReadout E₀ (e i) = E₀[e i] := List.getD_eq_getElem E₀ ∅ hlt
      rw [hget] at hz
      exact ⟨E₀[e i], List.getElem_mem hlt, hz⟩
    · rintro ⟨H, hH, hz⟩
      obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hH
      have hget : boundaryReadout E₀ k.val = E₀.get k := List.getD_eq_getElem E₀ ∅ k.isLt
      have hzk : z ∈ boundaryReadout E₀ k.val := by
        rw [hget]
        exact hz
      exact ⟨⟨ULift.up k.val, ⟨z, hzk⟩⟩, hzk⟩

/-- **An open set has only normal crossings with a locally finite indexed simple normal crossings family.** -/
theorem hasNormalCrossingsWithBoundary_of_isOpen {X : CMfd.{u} n} {ι : Type*} {C : Set X} (hC : IsOpen C)
    {D : ι → Set X} (hD : IsLocallyFiniteSNCDivisor n D) : HasNormalCrossingsWithBoundary C D := by
  intro x hx
  obtain ⟨S, hA, hcard, -⟩ := hD.2.2 x
  refine ⟨∅, S, ?_, hcard⟩
  have h1 : IsCoordinateFamilyAt n (fun o : Option ι => o.elim univ D) (fun o => o.elim ∅ S) x := by
    obtain ⟨Φ, hsub, h0, hflat⟩ := hA
    refine ⟨Φ, hsub, h0, ?_⟩
    rintro (_ | i) hi y hy hyΦ
    · simp [coordSubspace]
    · exact hflat i hi hy hyΦ
  refine CodimOneAdmissibleAlong.isCoordinateFamilyAt_congr ?_ h1
  filter_upwards [hC.mem_nhds hx] with y hy
  rintro (_ | i)
  · simp [hy]
  · exact Iff.rfl

/-- **The trivial case `dim W ≥ n` relative to a boundary: the identity is an embedded resolution.** -/
theorem boundary_resolution_of_le {X : CMfd.{u} n} {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ}
    (hd : n ≤ d) (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) :
    (id : X → X) ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n (id : X → X) ∧
      exceptionalLocus n (id : X → X) ⊆ (id : X → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      IsIsomorphismOver n (id : X → X) (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n (id : X → X) W) ∧
      (∀ z ∈ strictTransform n (id : X → X) W, RegularAtDim (n := n) (strictTransform n (id : X → X) W) z d) ∧
      ∃ (ι : Type u) (D : ι → Set X), IsLocallyFiniteSNCDivisor n D ∧ (∀ i, (D i).Nonempty) ∧
        (⋃ i, D i) = (id : X → X) ⁻¹' (⋃ H ∈ E₀, H) ∪ exceptionalLocus n (id : X → X) ∧
        (⋃ i, D i) = (id : X → X) ⁻¹' ((⋃ H ∈ E₀, H) ∪ W \ regularLocus (n := n) W d) ∧
        HasNormalCrossingsWithBoundary (strictTransform n (id : X → X) W) D := by
  obtain ⟨hexc, -, hsub, hreg, -⟩ := HironakaG3RPureFinal.identity_resolution_of_le hWa hd hpure
  have hsing := HironakaG3RPureFinal.diff_regularLocus_eq_empty_of_le hWa hd hpure
  have hst : strictTransform n (id : X → X) W = W := by
    simp [strictTransform, exceptionalLocus_id, hWa.isClosed.closure_eq]
  obtain ⟨ι, D, hD, hne, hU⟩ := exists_family_of_isSNCDivisor hE₀
  refine ⟨hexc.symm.subset, ?_, ⟨bijOn_id _, by rw [exceptionalLocus_id]; exact disjoint_empty _⟩, hsub, hreg, ι, D, hD,
    hne, ?_, ?_, ?_⟩
  · rw [exceptionalLocus_id]
    exact empty_subset _
  · rw [hU, exceptionalLocus_id, union_empty, preimage_id]
  · rw [hU, hsing, union_empty, preimage_id]
  · rw [hst]
    exact hasNormalCrossingsWithBoundary_of_isOpen (HironakaG3RPureFinal.isOpen_of_pure_of_le hWa hd hpure).1 hD

/-- **Embedded resolution relative to a simple normal crossings boundary, every pure dimension.** -/
theorem boundary_resolution {X : CMfd.{u} n} {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ}
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : CMfd.{u} n) (P : X' → X),
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
      P ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n P ∧
      exceptionalLocus n P ⊆ P ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      IsIsomorphismOver n P (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n P W) ∧
      (∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) ∧
      (∃ (ι : Type u) (D : ι → Set X'), IsLocallyFiniteSNCDivisor n D ∧ (∀ i, (D i).Nonempty) ∧
        (⋃ i, D i) = P ⁻¹' (⋃ H ∈ E₀, H) ∪ exceptionalLocus n P ∧
        (⋃ i, D i) = P ⁻¹' ((⋃ H ∈ E₀, H) ∪ W \ regularLocus (n := n) W d) ∧
        HasNormalCrossingsWithBoundary (strictTransform n P W) D) ∧
      (d < n → IsGluedBoundaryResolution W d E₀ X' P ∧
        (∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedBoundaryResolution W d E₀ X'' P' →
          ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
        (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
          ∃ c : TowerChart (bdryClass W d E₀) X' P, c.U = U)) ∧
      (n ≤ d → IsOpen W ∧ W \ regularLocus (n := n) W d = ∅ ∧
        ∃ Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X, ∀ z, Φ z = P z) := by
  by_cases hd : d < n
  · obtain ⟨X', P, h, huniq⟩ := existsUnique_gluedBoundaryResolution hWa hd hpure hE₀ hE₀W
    obtain ⟨ι, D, hD, hne, hU, hnc⟩ := HironakaG3RBoundaryGlobal.exists_globalBoundary hWa hd hpure hE₀ hE₀W h
    exact ⟨X', P, h.1, h.2.1, h.2.2.1, preimage_sing_subset_exceptionalLocus hWa hd hpure hE₀ hE₀W h,
      exceptionalLocus_subset hWa hd hpure hE₀ hE₀W h, isIsomorphismOver hWa hd hpure hE₀ hE₀W h,
      strictTransform_isClosedSubmanifold hWa hd hpure hE₀ hE₀W h,
      regularAtDim_strictTransform hWa hd hpure hE₀ hE₀W h,
      ⟨ι, D, hD, hne, hU, hU.trans (HironakaG3RBoundaryFinal.preimage_union_eq hWa hd hpure hE₀ hE₀W h), hnc⟩,
      fun _ => ⟨h, huniq, fun U K hK hUK => exists_chart_of_subset_isCompact hWa hd hpure hE₀ hE₀W h U hK hUK⟩,
      fun h' => absurd hd (not_lt.mpr h')⟩
  · have hd' : n ≤ d := not_lt.mp hd
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := boundary_resolution_of_le hWa hd' hpure hE₀
    exact ⟨X, id, contMDiff_id, isProperMap_id, surjective_id, h1, h2, h3, h4, h5, h6, fun h' => absurd h' hd,
      fun _ => ⟨(HironakaG3RPureFinal.isOpen_of_pure_of_le hWa hd' hpure).1,
        HironakaG3RPureFinal.diff_regularLocus_eq_empty_of_le hWa hd' hpure, Diffeomorph.refl _ _ _, fun _ => rfl⟩⟩

/-- **The final G3 theorem under target (A), with embedded resolution relative to a simple normal crossings boundary in
every pure dimension**; (a)–(c) are `HironakaG3RPureFinal.g3_final_global_pure`, (d) is `boundary_resolution`. -/
theorem g3_final_global_boundary_all (X : CMfd.{u} n) :
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
          dimensionPart (n := n) W k ⊆ closure (regularLocus (n := n) (dimensionPart (n := n) W k) k)) ∧
    (∀ W : Set X, IsComplexAnalyticSubset (n := n) W → ∀ d : ℕ, W ⊆ closure (regularLocus (n := n) W d) →
      ∀ E₀ : List (Set X), IsSNCDivisor n E₀ → W ⊆ closure (W \ ⋃ H ∈ E₀, H) →
      ∃ (X' : CMfd.{u} n) (P : X' → X),
        ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
        P ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n P ∧
        exceptionalLocus n P ⊆ P ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) ∧
        IsIsomorphismOver n P (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
        IsClosedSubmanifold n (strictTransform n P W) ∧
        (∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) ∧
        (∃ (ι : Type u) (D : ι → Set X'), IsLocallyFiniteSNCDivisor n D ∧ (∀ i, (D i).Nonempty) ∧
          (⋃ i, D i) = P ⁻¹' (⋃ H ∈ E₀, H) ∪ exceptionalLocus n P ∧
          (⋃ i, D i) = P ⁻¹' ((⋃ H ∈ E₀, H) ∪ W \ regularLocus (n := n) W d) ∧
          HasNormalCrossingsWithBoundary (strictTransform n P W) D) ∧
        (d < n → IsGluedBoundaryResolution W d E₀ X' P ∧
          (∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedBoundaryResolution W d E₀ X'' P' →
            ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
          (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
            ∃ c : TowerChart (bdryClass W d E₀) X' P, c.U = U)) ∧
        (n ≤ d → IsOpen W ∧ W \ regularLocus (n := n) W d = ∅ ∧
          ∃ Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X, ∀ z, Φ z = P z)) ∧
    (∀ (W : Set X) (d : ℕ) (X' : CMfd.{u} n) (P : X' → X),
      IsGluedBoundaryResolution W d [] X' P ↔ IsGluedPureResolution W d X' P) :=
  ⟨(HironakaG3RPureFinal.g3_final_global_pure X).1, (HironakaG3RPureFinal.g3_final_global_pure X).2.1,
    (HironakaG3RPureFinal.g3_final_global_pure X).2.2, fun _W hWa _d hpure _E₀ hE₀ hE₀W =>
    boundary_resolution hWa hpure hE₀ hE₀W, isGluedBoundaryResolution_nil⟩

end

end Hironaka.HironakaG3RBoundaryTop
