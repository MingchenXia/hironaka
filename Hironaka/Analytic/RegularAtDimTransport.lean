/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Manifold.LocalHolomorphicInverse
import Hironaka.Blowup.BlowupSequences
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# Regular points pull back along local biholomorphisms

* `LocalHolomorphicEquivAt.comp`: composition of local holomorphic equivalences, the second
  centred at the image of the centre of the first.
* `regularAtDim_of_preimage`: if `g : Z → Y` is holomorphic with bijective differential at `z`,
  and near `z` the set `A'` is the preimage of `A` under `g`, then a regular point `g z` of `A`
  of dimension `d` pulls back to a regular point `z` of `A'` of dimension `d`.  The flattening
  at `g z` is precomposed with the local holomorphic inverse of `g` read in preferred charts.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.RegularAtDimTransport

open Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ}

/-- Composition `Φ ∘ Ψ` of local holomorphic equivalences, on the part of the source of `Ψ`
mapped into the source of `Φ`. -/
def LocalHolomorphicEquivAt.comp {p q : ComplexModel n}
    (Ψ : LocalHolomorphicEquivAt (n := n) p) (Φ : LocalHolomorphicEquivAt (n := n) q)
    (hpq : Ψ.toFun p = q) : LocalHolomorphicEquivAt (n := n) p where
  source := Ψ.source ∩ Ψ.toFun ⁻¹' Φ.source
  target := Φ.target ∩ Φ.invFun ⁻¹' Ψ.target
  isOpen_source :=
    Ψ.toFun_holomorphic.continuousOn.isOpen_inter_preimage Ψ.isOpen_source Φ.isOpen_source
  isOpen_target :=
    Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_target Ψ.isOpen_target
  center_mem_source := ⟨Ψ.center_mem_source, by
    rw [mem_preimage, hpq]; exact Φ.center_mem_source⟩
  toFun := fun u => Φ.toFun (Ψ.toFun u)
  invFun := fun w => Ψ.invFun (Φ.invFun w)
  toFun_holomorphic :=
    Φ.toFun_holomorphic.comp (Ψ.toFun_holomorphic.mono inter_subset_left) fun _ hu => hu.2
  invFun_holomorphic :=
    Ψ.invFun_holomorphic.comp (Φ.invFun_holomorphic.mono inter_subset_left) fun _ hw => hw.2
  mapsTo_toFun := fun u hu => ⟨Φ.mapsTo_toFun hu.2, by
    simpa only [mem_preimage, Φ.left_inv _ hu.2] using Ψ.mapsTo_toFun hu.1⟩
  mapsTo_invFun := fun w hw => ⟨Ψ.mapsTo_invFun hw.2, by
    simpa only [mem_preimage, Ψ.right_inv _ hw.2] using Φ.mapsTo_invFun hw.1⟩
  left_inv := fun u hu => by
    simp only [Φ.left_inv _ hu.2]
    exact Ψ.left_inv _ hu.1
  right_inv := fun w hw => by
    simp only [Ψ.right_inv _ hw.2]
    exact Φ.right_inv _ hw.1

variable {Y Z : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **Regular points pull back along a local biholomorphism.** -/
theorem regularAtDim_of_preimage {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {z : Z}
    (hz : z ∉ BlowupSequences.exceptionalLocus n g) {A' : Set Z} {A : Set Y} {O : Set Z}
    (hO : IsOpen O) (hzO : z ∈ O) (hAO : ∀ u ∈ O, u ∈ A' ↔ g u ∈ A) {d : ℕ}
    (hA : RegularAtDim (n := n) A (g z) d) : RegularAtDim (n := n) A' z d := by
  obtain ⟨hdn, hgzA, Φ, hΦt, hΦ0, hΦA⟩ := hA
  set I := 𝓘(ℂ, ComplexModel n) with hI
  have hrange : range I = univ := by simp [hI]
  set e := chartAt (ComplexModel n) z with he
  set e' := chartAt (ComplexModel n) (g z) with he'
  set F : ComplexModel n → ComplexModel n := fun u => e' (g (e.symm u)) with hF
  set N : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' (O ∩ g ⁻¹' e'.source) with hN
  have hNo : IsOpen N :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target
      (hO.inter (hg.continuous.isOpen_preimage _ e'.open_source))
  have hzN : e z ∈ N := ⟨e.map_source (mem_chart_source _ z), by
    rw [mem_preimage, e.left_inv (mem_chart_source _ z)]
    exact ⟨hzO, mem_chart_source _ (g z)⟩⟩
  have hFN : DifferentiableOn ℂ F N := by
    have h := (contMDiffOn_iff.mp (hg.contMDiffOn (s := univ))).2 z (g z)
    refine (h.differentiableOn (by simp)).mono ?_
    intro u hu
    exact ⟨⟨mem_univ _, hu.1⟩, mem_univ _, hu.2.2, mem_univ _⟩
  have hmd : MDifferentiableAt I I g z := (hg z).mdifferentiableAt (by simp)
  have hderiv : mfderiv I I g z = fderiv ℂ F (e z) := by
    rw [hmd.mfderiv, hrange, fderivWithin_univ]
    rfl
  have hinj : Function.Injective (fderiv ℂ F (e z)) := by
    have := hz
    simp only [exceptionalLocus, mem_ofPred_eq, not_not] at this
    rw [hderiv] at this
    exact this.1
  obtain ⟨Ψ, hΨN, hΨF, -⟩ := exists_localHolomorphicEquivAt hNo hzN hFN hinj
  have hFz : F (e z) = e' (g z) := by
    simp only [hF, e.left_inv (mem_chart_source _ z)]
  refine ⟨hdn, (hAO z hzO).mpr hgzA, LocalHolomorphicEquivAt.comp Ψ Φ (hΨF ▸ hFz), ?_, ?_, ?_⟩
  · intro u hu
    exact (hΨN hu.1).1
  · change Φ.toFun (Ψ.toFun (e z)) = 0
    rw [hΨF, hFz]
    exact hΦ0
  · intro y hy hyΘ
    change e y ∈ Ψ.source ∩ Ψ.toFun ⁻¹' Φ.source at hyΘ
    change y ∈ A' ↔ Φ.toFun (Ψ.toFun (e y)) ∈ complexCoordinatePlane n d
    have hyN := (hΨN hyΘ.1).2
    rw [mem_preimage, e.left_inv hy] at hyN
    have hFy : F (e y) = e' (g y) := by simp only [hF, e.left_inv hy]
    have hyΦ : e' (g y) ∈ Φ.source := by
      have := hyΘ.2
      rwa [mem_preimage, hΨF, hFy] at this
    rw [hAO y hyN.1, hΨF, hFy]
    exact hΦA hyN.2 hyΦ

end

end Hironaka.RegularAtDimTransport
