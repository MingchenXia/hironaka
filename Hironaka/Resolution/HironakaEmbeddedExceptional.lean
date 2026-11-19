import Hironaka.Resolution.HironakaEmbeddedResolutionLocal

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Embedded resolution: the exceptional divisor is exactly the preimage of the singular locus (Hironaka)

Blueprint `hir:embedded-resolution-exceptional` (`blueprint/src/hironaka.tex`; TN.5, the sharpening of the Hironaka
strengthening (H+1) for the standalone library).  Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Theorem 1.0.2
(embedded desingularization: the exceptional divisor of the resolution is `f⁻¹(V_sing)`); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), Theorem 1.2.

**Statement.**  In the embedded resolution `f : X' → X` of a closed irreducible analytic subvariety `V` of `hir:embedded-resolution-snc`
(compact `X`) and of `hir:embedded-resolution-local` (any `X`, over a neighbourhood `U` of a compact set),
`Exc f = E₁ ∪ ⋯ ∪ E_r = f⁻¹(V_sing)`: the exceptional divisor with simple normal crossings is the whole preimage of the singular
locus, and it is the exceptional locus of `f`.

**Route.**  A general fact about any holomorphic map `f` between manifolds of the same dimension
(`preimage_singularLocus_subset_exceptionalLocus`): if the strict transform `V'` of `V` is regular of dimension `dim V` at each of
its points, then `f⁻¹(V_sing) ⊆ Exc f`.  Indeed a point `y ∉ Exc f` over `V` lies in `V'`, which near `y` is the preimage of `V`;
regularity of a given dimension *pushes forward* along the local biholomorphism `f` near `y` (`regularAtDim_of_regularAtDim_preimage`,
the converse of `RegularAtDimTransport.regularAtDim_of_preimage`), so `f y` is a regular point of `V` of dimension `dim V`, i.e.
`f y ∉ V_sing`.  Together with `Exc f ⊆ ⋃ E ⊆ f⁻¹(V_sing)` from H+1 (resp. its local form) the three sets are equal.

## Main results

* `LocalHolomorphicEquivAt.symmAt`: the inverse of a local holomorphic equivalence, centred at the image of the centre;
* **`regularAtDim_of_regularAtDim_preimage`**: regular points push forward along a holomorphic map at a point of bijective
  differential;
* **`preimage_singularLocus_subset_exceptionalLocus`**, **`exceptionalLocus_eq_preimage_singularLocus`**: for any holomorphic `f`
  whose strict transform of `V` is smooth of dimension `dim V`, `f⁻¹(V_sing) ⊆ Exc f`, with equality when `f(Exc f) ⊆ V_sing`;
* **`exists_embeddedResolution_exceptional`** (compact `X`) and **`exists_embeddedResolution_local_exceptional`** (any `X`):
  H+1 and its local form with `Exc f = ⋃ E = f⁻¹(V_sing)`.

Import discipline (standalone Hironaka library): this module imports `HironakaEmbeddedResolutionLocal` only; it does not
import, even transitively, `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaEmbeddedExceptional

open Hironaka.NonKahlerLocus Hironaka.BlowupSequences
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

/-- **The exceptional locus is the preimage of the singular locus** for any holomorphic `f` whose exceptional image lies in
`V_sing` and whose strict transform of `V` is regular of dimension `dim V` at each of its points. -/
theorem exceptionalLocus_eq_preimage_singularLocus {f : X' → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hExc : f '' exceptionalLocus n f ⊆ singularLocus V)
    (hreg : ∀ x ∈ strictTransform n f V.carrier,
      RegularAtDim (n := n) (strictTransform n f V.carrier) x V.dim) :
    exceptionalLocus n f = f ⁻¹' singularLocus V :=
  Subset.antisymm (fun y hy => hExc ⟨y, hy, rfl⟩) (preimage_singularLocus_subset_exceptionalLocus hf V hreg)

end Exceptional

/-! ### Embedded resolution with `Exc f = ⋃ E = f⁻¹(V_sing)` -/

/-- **Embedded resolution, sharpened** (Hironaka; `hir:embedded-resolution-exceptional`): for a closed irreducible analytic
subvariety `V` of a compact complex manifold `X` there are a finite sequence of blowups with smooth centres `f : X' → X` and a
divisor `E` on `X'` with simple normal crossings such that `Exc f = ⋃ E = f⁻¹(V_sing)`, `f` is an isomorphism over `X \ V_sing`,
the strict transform of `V` is a closed connected submanifold of dimension `dim V`, and it has only normal crossings with `E`. -/
theorem exists_embeddedResolution_exceptional {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X] (V : ClosedIrreducibleAnalyticSubvariety n X) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (_ : IsBlowupSequence n X X' f) (E : List (Set X')),
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' singularLocus V ∧
      IsIsomorphismOver n f (singularLocus V)ᶜ ∧
      IsClosedConnectedSubmanifold n (strictTransform n f V.carrier) V.dim ∧
      HasNormalCrossings n (strictTransform n f V.carrier) E := by
  obtain ⟨X', i1, i2, i3, f, hf, E, hsnc, hexc, hsing, hiso, hS, hnc⟩ :=
    HironakaEmbeddedResolution.exists_embeddedResolution V
  have hsub := preimage_singularLocus_subset_exceptionalLocus hf.contMDiff V hS.2.2
  exact ⟨X', i1, i2, i3, f, hf, E, hsnc, Subset.antisymm hexc (hsing.trans hsub),
    Subset.antisymm hsing (hsub.trans hexc), hiso, hS, hnc⟩

/-- **Local embedded resolution, sharpened** (Hironaka; `hir:embedded-resolution-exceptional`): for a closed irreducible analytic
subvariety `V` of any complex manifold `X` and a compact `K ⊆ X` there are an open neighbourhood `U` of `K`, a finite sequence of
blowups with smooth centres `f : U' → U` and a divisor `E` on `U'` with simple normal crossings such that
`Exc f = ⋃ E = f⁻¹(V_sing ∩ U)`, `f` is an isomorphism over `U \ V_sing`, and the strict transform of `V ∩ U` is a closed
submanifold of `U'`, of dimension `dim V` at each of its points, with only normal crossings with `E`. -/
theorem exists_embeddedResolution_local_exceptional {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (V : ClosedIrreducibleAnalyticSubvariety n X) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (_ : IsBlowupSequence n U U' f) (E : List (Set U')),
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' ((Subtype.val : U → X) ⁻¹' singularLocus V) ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' singularLocus V)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) x V.dim) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) E := by
  obtain ⟨U, hKU, U', i1, i2, i3, f, hf, E, hsnc, hexc, hsing, hiso, hS, hreg, hnc⟩ :=
    HironakaEmbeddedResolutionLocal.exists_embeddedResolution_local V hK
  -- the points over `V_sing ∩ U` are exceptional: push regularity forward to `V`
  have hsub : f ⁻¹' ((Subtype.val : U → X) ⁻¹' singularLocus V) ⊆ exceptionalLocus n f := by
    intro y hy
    by_contra hyE
    have hO : IsOpen (exceptionalLocus n f)ᶜ := StrictTransformComposition.isOpen_compl_exceptionalLocus hf.contMDiff
    have hAO : ∀ w ∈ (exceptionalLocus n f)ᶜ, w ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier) ↔
        f w ∈ (Subtype.val : U → X) ⁻¹' V.carrier := fun w hw =>
      ⟨fun h => closure_minimal sdiff_subset
        ((V.isClosed_carrier.preimage continuous_subtype_val).preimage hf.contMDiff.continuous) h,
        fun h => subset_closure ⟨h, hw⟩⟩
    have hyS := (hAO y hyE).mpr hy.1
    have h1 := regularAtDim_of_regularAtDim_preimage hf.contMDiff hyE hO hyE hAO (hreg y hyS)
    exact hy.2 (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp h1)
  exact ⟨U, hKU, U', i1, i2, i3, f, hf, E, hsnc, Subset.antisymm hexc (hsing.trans hsub),
    Subset.antisymm hsing (hsub.trans hexc), hiso, hS, hreg, hnc⟩

end

end Hironaka.HironakaEmbeddedExceptional
