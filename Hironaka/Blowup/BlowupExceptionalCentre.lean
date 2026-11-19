import Hironaka.Blowup.BlowupCodimOne
import Hironaka.Blowup.ExceptionalFibres

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The exceptional centre of a blowup

Let `π : Z → M` be the blowup of a compact complex manifold along `C`.  The *exceptional centre*
`C₂ = π(Exc π)` is the union of the components of `C` of codimension `≥ 2`:

* `preimage_exceptionalCentre`: `π⁻¹ C₂ = Exc π` (`ExceptionalFibres`);
* `exists_preimage_of_mem_centre`: `π` is onto `C` (the lift of a monomial chart through the flat
  point itself);
* `exists_flat_exceptionalCentre`: every point of `C₂` has a flattening of `C` onto a coordinate
  plane of codimension `≥ 2` on whose domain `C` and `C₂` agree (`BlowupCodimOne`);
* `exists_blanchardData_exceptionalCentre`: Blanchard data for `C₂` whose flattenings also
  flatten `C`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupExceptionalCentre

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupCodimOne
  BlanchardWeight ChartPartition

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M}

variable (n) in
/-- The exceptional centre `π(Exc π)`. -/
def exceptionalCentre (π : Z → M) : Set M := π '' exceptionalLocus n π

theorem preimage_exceptionalCentre (hπ : IsBlowupAlong n C π) :
    π ⁻¹' exceptionalCentre n π = exceptionalLocus n π :=
  ExceptionalFibres.preimage_image_exceptionalLocus hπ

theorem exceptionalCentre_subset (hπ : IsBlowupAlong n C π) : exceptionalCentre n π ⊆ C :=
  ExceptionalFibres.image_exceptionalLocus_subset hπ

theorem isClosed_exceptionalCentre [CompactSpace M] (hπ : IsBlowupAlong n C π) :
    IsClosed (exceptionalCentre n π) :=
  ExceptionalFibres.isClosed_image_exceptionalLocus hπ

/-- **A blowup is onto its centre** (in a flattening domain). -/
theorem exists_preimage_of_mem_centre (hπ : IsBlowupAlong n C π) {y₀ : M}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    {y : M} (hy : y ∈ flatDomain Φ) (hyC : y ∈ C) : ∃ z, π z = y := by
  have hk : k < n := by
    by_contra hk
    push Not at hk
    have hsub : flatDomain Φ ⊆ C := fun y' hy' =>
      (hflat hy'.1 hy'.2).mpr fun i hi => absurd i.2 (by omega)
    have := interior_maximal hsub (isOpen_flatDomain Φ)
    rw [hπ.2.1] at this
    exact this hy
  set j : Fin n := ⟨k, hk⟩
  set w := Φ.toFun (chartAt (ComplexModel n) y₀ y)
  have hwC : w ∈ complexCoordinatePlane n k := (hflat hy.1 hy.2).mp hyC
  have hσ : monomial k j w = w := by
    ext i
    simp only [monomial_apply]
    split_ifs with h
    · rw [hwC i h.1]; simp
    · rfl
  have hw : w ∈ monomialDomain Φ k j := by
    show monomial k j w ∈ Φ.target
    rw [hσ]; exact Φ.mapsTo_toFun hy.2
  obtain ⟨ℓ, ⟨-, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦsrc hflat (j := j) le_rfl
  refine ⟨ℓ (LiftedOpen.mk _ w hw), ?_⟩
  have := congrFun hℓπ (LiftedOpen.mk _ w hw)
  simp only [Function.comp_apply] at this
  rw [this]
  show (chartAt (ComplexModel n) y₀).symm (Φ.invFun (monomial k j w)) = y
  rw [hσ]
  exact flatInverse_flat Φ hy

/-- **Flattenings along the exceptional centre.** -/
theorem exists_flat_exceptionalCentre (hπ : IsBlowupAlong n C π) {p : M}
    (hp : p ∈ exceptionalCentre n π) :
    ∃ k : ℕ, k + 2 ≤ n ∧ ∃ Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p),
      Φ.source ⊆ (chartAt (ComplexModel n) p).target ∧
      Φ.toFun (chartAt (ComplexModel n) p p) = 0 ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel n) p).source →
        chartAt (ComplexModel n) p y ∈ Φ.source →
          (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) p y) ∈ complexCoordinatePlane n k)) ∧
      ∀ y ∈ flatDomain Φ, y ∈ C → y ∈ exceptionalCentre n π := by
  have hpC := exceptionalCentre_subset hπ hp
  obtain ⟨k, -, -, Φ, hsrc, h0, hflat⟩ := hπ.1.2 p hpC
  obtain ⟨z₀, hz₀, hz₀p⟩ := hp
  have hk : k + 2 ≤ n := by
    by_contra hk
    push Not at hk
    exact notMem_exceptionalLocus_of_codim_le_one hπ hsrc hflat (by omega)
      (by rw [hz₀p]; exact mem_flatDomain_self Φ) hz₀
  refine ⟨k, hk, Φ, hsrc, h0, hflat, fun y hy hyC => ?_⟩
  obtain ⟨z, rfl⟩ := exists_preimage_of_mem_centre hπ hsrc hflat hy hyC
  exact ⟨z, mem_exceptionalLocus_of_codim_ge_two hπ hsrc hflat hk hy hyC, rfl⟩

/-- **Blanchard data for the exceptional centre**, with flattenings that also flatten `C`. -/
theorem exists_blanchardData_exceptionalCentre [CompactSpace M] (hπ : IsBlowupAlong n C π) :
    ∃ D : BlanchardData n (exceptionalCentre n π),
      (∀ q, D.kdim q + 2 ≤ n) ∧
      ∀ (q : exceptionalCentre n π) {y : M}, y ∈ (chartAt (ComplexModel n) q.1).source →
        chartAt (ComplexModel n) q.1 y ∈ (D.flat q).source →
          (y ∈ C ↔ (D.flat q).toFun (chartAt (ComplexModel n) q.1 y) ∈
            complexCoordinatePlane n (D.kdim q)) := by
  classical
  set C₂ := exceptionalCentre n π
  have hC₂ : IsClosed C₂ := isClosed_exceptionalCentre hπ
  choose kdim hk Φ hsrc _ hflat hsub using fun p : C₂ => exists_flat_exceptionalCentre hπ p.2
  have hflat₂ : ∀ (p : C₂) {y : M}, y ∈ (chartAt (ComplexModel n) p.1).source →
      chartAt (ComplexModel n) p.1 y ∈ (Φ p).source →
        (y ∈ C₂ ↔ (Φ p).toFun (chartAt (ComplexModel n) p.1 y) ∈
          complexCoordinatePlane n (kdim p)) := fun p y hy hy' => by
    rw [← hflat p hy hy']
    exact ⟨fun h => exceptionalCentre_subset hπ h, fun h => hsub p y ⟨hy, hy'⟩ h⟩
  set S : Option C₂ → TopologicalSpace.Opens M := fun o => match o with
    | none => ⟨C₂ᶜ, hC₂.isOpen_compl⟩
    | some p => ⟨flatDomain (Φ p), isOpen_flatDomain _⟩ with hS
  have hcover : ∀ y, ∃ o, y ∈ S o := fun y => by
    by_cases hy : y ∈ C₂
    · exact ⟨some ⟨y, hy⟩, mem_flatDomain_self (Φ ⟨y, hy⟩)⟩
    · exact ⟨none, hy⟩
  obtain ⟨m, χ, idx, hs, hnn, hsupp, -, hsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n) S hcover
  exact ⟨⟨kdim, Φ, hsrc, fun p => hflat₂ p, m, χ, idx, hs, hnn, hsum,
    fun a h => by have := hsupp a; rw [h] at this; exact this,
    fun a p h => by have := hsupp a; rw [h] at this; exact this⟩, hk, fun q => hflat q⟩

end

end Hironaka.BlowupExceptionalCentre
