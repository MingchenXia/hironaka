/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MonomialCase
import Hironaka.Blowup.MonomialBlowup
import Hironaka.MarkedIdeal.TransformOffCentre
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Manifold.LocalHolomorphicInverse
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.RegularAtDimTransport
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Resolution of monomial marked ideals (`N = M`)

Sources: Włodarczyk 2005, Step 2b of the proof of the resolution theorem (blow up the intersection of a minimal set
of members whose exponents add up to the mark; the invariant drops); Bierstone--Milman 2008, §5 (the monomial case).
-/

open Set Filter Finset
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MonomialResolution

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder Hironaka.BlowupFlatCoordinates Hironaka.GiraudAlong Hironaka.DivisorExponent Hironaka.MemberPullback Hironaka.MonomialPart Hironaka.NormalCrossings Hironaka.MonomialInvariant Hironaka.BoundaryCount Hironaka.MonomialCase Hironaka.BlowupStrictSubmanifold Hironaka.BlowupSNCTransform Hironaka.InvertibleIdealQuotient Hironaka.RestrictedIdealQuotient Hironaka.RestrictedIdealExtension Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers

noncomputable section

variable {n : ℕ}

/-! ### Principal monomial ideals at a point -/

section Principal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Exponent data on `Fin E.length`, extended by `0` to `ℕ`. -/
def extExp (E : List (Set M)) (a : Fin E.length → ℕ) (i : ℕ) : ℕ :=
  if h : i < E.length then a ⟨i, h⟩ else 0

end Principal

/-! ### Off the centre -/

section OffCentre

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X}

/-- **A flat chart at `π z` read through `π`, off the centre**: the blowup is a local biholomorphism at `z`
(`BlowupIsomorphismOff`), so `Φ ∘ e_{π z} ∘ π` are coordinates at `z`, centred if `Φ` is; their domain lies off
`π⁻¹ C` and over the domain of `Φ`. -/
theorem exists_chart_comp (hπ : IsBlowupAlong n C π) {z : Y} (hz : π z ∉ C)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z)))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) = 0) :
    ∃ Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧ Θ.toFun (chartAt (ComplexModel n) z z) = 0 ∧
      ∀ {y : Y}, y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ Θ.source →
        π y ∉ C ∧ π y ∈ flatDomain Φ ∧
          Θ.toFun (chartAt (ComplexModel n) z y) = Φ.toFun (chartAt (ComplexModel n) (π z) (π y)) := by
  set I := 𝓘(ℂ, ComplexModel n) with hI
  have hrange : range I = univ := by simp [hI]
  set e := chartAt (ComplexModel n) z with he
  set O : Set Y := π ⁻¹' Cᶜ with hOdef
  have hO : IsOpen O := hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous
  set F : ComplexModel n → ComplexModel n := fun u => chartAt (ComplexModel n) (π z) (π (e.symm u)) with hF
  set N : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' (O ∩ π ⁻¹' (chartAt (ComplexModel n) (π z)).source) with hN
  have hNo : IsOpen N :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target
      (hO.inter (hπ.contMDiff.continuous.isOpen_preimage _ (chartAt (ComplexModel n) (π z)).open_source))
  have hzN : e z ∈ N := ⟨e.map_source (mem_chart_source _ z), by
    rw [Set.mem_preimage, e.left_inv (mem_chart_source _ z)]
    exact ⟨hz, mem_chart_source _ (π z)⟩⟩
  have hFN : DifferentiableOn ℂ F N := by
    have h := (contMDiffOn_iff.mp (hπ.contMDiff.contMDiffOn (s := univ))).2 z (π z)
    refine (h.differentiableOn (by simp)).mono ?_
    intro u hu
    exact ⟨⟨mem_univ _, hu.1⟩, mem_univ _, hu.2.2, mem_univ _⟩
  have hmd : MDifferentiableAt I I π z := (hπ.contMDiff z).mdifferentiableAt (by simp)
  have hderiv : mfderiv I I π z = fderiv ℂ F (e z) := by
    rw [hmd.mfderiv, hrange, fderivWithin_univ]
    rfl
  have hzE : z ∉ exceptionalLocus n π := fun h =>
    hz (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
  have hinj : Function.Injective (fderiv ℂ F (e z)) := by
    have := hzE
    simp only [exceptionalLocus, mem_ofPred_eq, not_not] at this
    rw [hderiv] at this
    exact this.1
  obtain ⟨Ψ, hΨN, hΨF, -⟩ := exists_localHolomorphicEquivAt hNo hzN hFN hinj
  have hFz : F (e z) = chartAt (ComplexModel n) (π z) (π z) := by
    simp only [hF, e.left_inv (mem_chart_source _ z)]
  refine ⟨RegularAtDimTransport.LocalHolomorphicEquivAt.comp Ψ Φ (hΨF ▸ hFz), ?_, ?_, ?_⟩
  · intro u hu
    exact (hΨN hu.1).1
  · change Φ.toFun (Ψ.toFun (e z)) = 0
    rw [hΨF, hFz]
    exact hΦ0
  · intro y hy hyΘ
    change e y ∈ Ψ.source ∩ Ψ.toFun ⁻¹' Φ.source at hyΘ
    have hyN := (hΨN hyΘ.1).2
    rw [Set.mem_preimage, e.left_inv hy] at hyN
    have hFy : F (e y) = chartAt (ComplexModel n) (π z) (π y) := by simp only [hF, e.left_inv hy]
    have hyΦ : chartAt (ComplexModel n) (π z) (π y) ∈ Φ.source := by
      have := hyΘ.2
      rwa [Set.mem_preimage, hΨF, hFy] at this
    refine ⟨hyN.1, ⟨hyN.2, hyΦ⟩, ?_⟩
    change Φ.toFun (Ψ.toFun (e y)) = _
    rw [hΨF, hFy]

/-- The members of the transformed divisor through a point off `π⁻¹ C` are the strict transforms of the members through
its image, and near it they are the preimages. -/
theorem mem_get_geoTransform_iff_of_notMem (hπ : IsBlowupAlong n C π) (𝔪 : MarkedIdeal n X)
    (hE : IsSNCDivisor n 𝔪.E) {y : Y} (hy : π y ∉ C) (i : Fin (𝔪.geoTransform C π).E.length) :
    y ∈ (𝔪.geoTransform C π).E.get i ↔ ∃ h : i.1 < 𝔪.E.length, π y ∈ 𝔪.E.get ⟨i.1, h⟩ := by
  have hget : (𝔪.geoTransform C π).E.get i =
      if h : i.1 < 𝔪.E.length then geoStrictTransform π C (𝔪.E.get ⟨i.1, h⟩) else π ⁻¹' C :=
    get_map_append_singleton 𝔪.E (geoStrictTransform π C) (π ⁻¹' C) i
  rw [hget]
  by_cases h : i.1 < 𝔪.E.length
  · rw [dif_pos h, mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous (hE.1 _ (List.get_mem _ _)) hy]
    exact ⟨fun h' => ⟨h, h'⟩, fun ⟨_, h'⟩ => h'⟩
  · rw [dif_neg h]
    exact ⟨fun h' => absurd h' hy, fun ⟨h', _⟩ => absurd h' h⟩

/-- The indices of `E` inside those of the transformed divisor. -/
def castE (𝔪 : MarkedIdeal n X) (C : Set X) (π : Y → X) : Fin 𝔪.E.length ↪ Fin (𝔪.geoTransform C π).E.length where
  toFun i := ⟨i.1, by rw [length_E_geoTransform]; omega⟩
  inj' i j h := Fin.ext (by simpa using congrArg Fin.val h)

end OffCentre

end

end Hironaka.MonomialResolution
