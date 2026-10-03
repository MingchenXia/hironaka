/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Manifold.LocalHolomorphicInverse
import Hironaka.Analytic.SingularLocus
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Resolution.StrictTransformComposition
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Embedded resolution: the exceptional divisor is exactly the preimage of the singular locus (Hironaka)

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Theorem 1.0.2 (embedded desingularization: the exceptional
divisor of the resolution is `f⁻¹(V_sing)`); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Theorem
1.2.

**Statement.**  In the embedded resolution `f : X' → X` of a closed irreducible analytic subvariety `V` of `hir:embedded-resolution-snc`
(compact `X`) and of `hir:embedded-resolution-local` (any `X`, over a neighbourhood `U` of a compact set),
`Exc f = E₁ ∪ ⋯ ∪ E_r = f⁻¹(V_sing)`: the exceptional divisor with simple normal crossings is the whole preimage of the singular
locus, and it is the exceptional locus of `f`.

**Route.** A general fact about any holomorphic map `f` between manifolds of the same dimension
(`preimage_singularLocus_subset_exceptionalLocus`): if the strict transform `V'` of `V` is regular of dimension `dim
V` at each of its points, then `f⁻¹(V_sing) ⊆ Exc f`. Indeed a point `y ∉ Exc f` over `V` lies in `V'`, which near
`y` is the preimage of `V`; regularity of a given dimension *pushes forward* along the local biholomorphism `f` near
`y` (`regularAtDim_of_regularAtDim_preimage`, the converse of `RegularAtDimTransport.regularAtDim_of_preimage`), so
`f y` is a regular point of `V` of dimension `dim V`, i.e. `f y ∉ V_sing`.

## Main results

* `LocalHolomorphicEquivAt.symmAt`: the inverse of a local holomorphic equivalence, centred at the image of the centre;
* **`regularAtDim_of_regularAtDim_preimage`**: regular points push forward along a holomorphic map at a point of bijective
  differential;
* **`preimage_singularLocus_subset_exceptionalLocus`**: for any holomorphic `f` whose strict transform of `V` is
  smooth of dimension `dim V`, `f⁻¹(V_sing) ⊆ Exc f`, with equality when `f(Exc f) ⊆ V_sing`;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaEmbeddedExceptional

open Hironaka.BlowupSequences
open Hironaka.NormalCrossings

noncomputable section

variable {n : ℕ}

/-! ### Regular points push forward along a local biholomorphism -/

section Transport

/-- **The inverse of a local holomorphic equivalence**, centred at the image `q` of the centre `p`. -/
def LocalHolomorphicEquivAt.symmAt {p q : ComplexModel n} (Ψ : LocalHolomorphicEquivAt (n := n) p)
    (hpq : Ψ.toFun p = q) : LocalHolomorphicEquivAt (n := n) q where
  source := Ψ.target
  target := Ψ.source
  isOpen_source := Ψ.isOpen_target
  isOpen_target := Ψ.isOpen_source
  center_mem_source := hpq ▸ Ψ.mapsTo_toFun Ψ.center_mem_source
  toFun := Ψ.invFun
  invFun := Ψ.toFun
  toFun_holomorphic := Ψ.invFun_holomorphic
  invFun_holomorphic := Ψ.toFun_holomorphic
  mapsTo_toFun := Ψ.mapsTo_invFun
  mapsTo_invFun := Ψ.mapsTo_toFun
  left_inv := Ψ.right_inv
  right_inv := Ψ.left_inv

variable {Y Z : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **Regular points push forward along a local biholomorphism** (the converse of
`RegularAtDimTransport.regularAtDim_of_preimage`): if `g : Z → Y` is holomorphic with bijective differential at `z`, and near
`z` the set `A'` is the preimage of `A` under `g`, then a regular point `z` of `A'` of dimension `d` gives a regular point `g z`
of `A` of dimension `d`.  The flattening of `A'` at `z` is composed with the local holomorphic inverse of `g` read in preferred
charts. -/
theorem regularAtDim_of_regularAtDim_preimage {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {z : Z}
    (hz : z ∉ exceptionalLocus n g) {A' : Set Z} {A : Set Y} {O : Set Z}
    (hO : IsOpen O) (hzO : z ∈ O) (hAO : ∀ u ∈ O, u ∈ A' ↔ g u ∈ A) {d : ℕ}
    (hA' : RegularAtDim (n := n) A' z d) : RegularAtDim (n := n) A (g z) d := by
  obtain ⟨hdn, hzA', Φ, hΦt, hΦ0, hΦA⟩ := hA'
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
  have hq : Ψ.toFun (e z) = e' (g z) := by rw [hΨF, hFz]
  have hcomp : (LocalHolomorphicEquivAt.symmAt Ψ hq).toFun (e' (g z)) = e z := by
    show Ψ.invFun (e' (g z)) = e z
    rw [← hq]
    exact Ψ.left_inv _ Ψ.center_mem_source
  -- the target of `Ψ` lies in the chart at `g z`
  have hΨt : ∀ w ∈ Ψ.target, w = F (Ψ.invFun w) ∧ Ψ.invFun w ∈ N := fun w hw => by
    refine ⟨?_, hΨN (Ψ.mapsTo_invFun hw)⟩
    have h := Ψ.right_inv w hw
    rw [hΨF] at h
    exact h.symm
  refine ⟨hdn, (hAO z hzO).mp hzA', RegularAtDimTransport.LocalHolomorphicEquivAt.comp (LocalHolomorphicEquivAt.symmAt Ψ hq) Φ hcomp,
    ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwF, hwN⟩ := hΨt w hw.1
    rw [hwF]
    exact e'.map_source hwN.2.2
  · change Φ.toFun (Ψ.invFun (e' (g z))) = 0
    rw [← hq, Ψ.left_inv _ Ψ.center_mem_source]
    exact hΦ0
  · intro y hy hyΘ
    change e' y ∈ Ψ.target ∩ Ψ.invFun ⁻¹' Φ.source at hyΘ
    change y ∈ A ↔ Φ.toFun (Ψ.invFun (e' y)) ∈ complexCoordinatePlane n d
    obtain ⟨hwF, hwN⟩ := hΨt (e' y) hyΘ.1
    set u := Ψ.invFun (e' y) with hu
    obtain ⟨hue, hpO, hpe'⟩ := hwN
    have hpe : e.symm u ∈ e.source := e.map_target hue
    have hgp : g (e.symm u) = y := e'.injOn hpe'.out hy hwF.symm
    have heu : e (e.symm u) = u := e.right_inv hue
    have hmem : e (e.symm u) ∈ Φ.source := by rw [heu]; exact hyΘ.2
    have key := hΦA hpe hmem
    rw [← hgp, ← hAO _ hpO]
    refine key.trans ?_
    show Φ.toFun (e (e.symm u)) ∈ _ ↔ _
    rw [heu]

end Transport

/-! ### A smooth strict transform forces `f⁻¹(V_sing) ⊆ Exc f` -/

section Exceptional

variable {X X' : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace X'] [ChartedSpace (ComplexModel n) X'] [IsComplexManifold n X']

/-- **A smooth strict transform forces `f⁻¹(V_sing) ⊆ Exc f`**: for any holomorphic `f : X' → X` between manifolds of the same
dimension, if the strict transform of `V` is regular of dimension `dim V` at each of its points, then every point over the
singular locus of `V` is exceptional.  A non-exceptional point `y` over `V` lies on the strict transform, which near `y` is the
preimage of `V`, so `f y` is a regular point of `V` of dimension `dim V` (`regularAtDim_of_regularAtDim_preimage`). -/
theorem preimage_singularLocus_subset_exceptionalLocus {f : X' → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hreg : ∀ x ∈ strictTransform n f V.carrier,
      RegularAtDim (n := n) (strictTransform n f V.carrier) x V.dim) :
    f ⁻¹' singularLocus V ⊆ exceptionalLocus n f := by
  intro y hy
  by_contra hyE
  have hO : IsOpen (exceptionalLocus n f)ᶜ := StrictTransformComposition.isOpen_compl_exceptionalLocus hf
  have hAO : ∀ u ∈ (exceptionalLocus n f)ᶜ, u ∈ strictTransform n f V.carrier ↔ f u ∈ V.carrier := fun u hu =>
    ⟨fun h => closure_minimal sdiff_subset (V.isClosed_carrier.preimage hf.continuous) h,
      fun h => subset_closure ⟨h, hu⟩⟩
  have hyS : y ∈ strictTransform n f V.carrier := (hAO y hyE).mpr hy.1
  exact hy.2 (regularAtDim_of_regularAtDim_preimage hf hyE hO hyE hAO (hreg y hyS))

end Exceptional

end

end Hironaka.HironakaEmbeddedExceptional
