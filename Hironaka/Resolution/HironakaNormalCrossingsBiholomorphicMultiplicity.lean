/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaNormalCrossingsBoundarySeparation
import Hironaka.Analytic.RegularAtDimTransport

/-! # Genuine whole NC coordinate and intrinsic multiplicity transport

The actual chart read of a genuine local biholomorphism internally produces a
whole coordinate reader using the true holomorphic inverse-function theorem.
It transports the entire original NC union and actual simultaneous original /
finite-boundary pair. The original branch count is identified with the same
actual selected-coordinate cardinality, independently of all branch labels.

Actual biholomorphic surjectivity then identifies all count values, whole
superlevels, uniform bounds and the count-one stopping condition. The original
carrier internally produces its unique attained positive whole maximum and the
exact preimage correspondence of its entire genuine smooth highest centre.
No count, branch matching, maximum, centre alignment or naturality certificate
is a final producer hypothesis.

These are the prerequisites for arbitrary actual blowup-choice comparisons of
the finite geometric separation tower. That next finite comparison construction
is not asserted here. Extra marked-cosupport admissibility and independence of
the old ordered colexicographic label tie-break remain separate obligations;
full canonical marked-ideal G9 remains open. The protected strict statement
modules are not imported.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsBiholomorphicMultiplicity
open Hironaka.BlowupSequences HironakaNormalCrossingsLocalBranches
  HironakaNormalCrossingsMultiplicityStrata HironakaNormalCrossingsBoundaryTransform
  BlowupFlatCoordinates NormalCrossings NormalCrossingsInvariance

open Hironaka

noncomputable section
variable {n : ℕ} {Y Z : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- The actual full original coordinate vector is internally read under a genuine
local biholomorphism, on a true domain mapping into the original whole flat domain. -/
theorem exists_pullback_flat_coordinates {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {z : Z}
    (hz : z ∉ exceptionalLocus n g)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (g z) (g z))) :
    ∃ Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z) = Φ.toFun (chartAt (ComplexModel n) (g z) (g z)) ∧
      ∀ y ∈ flatDomain Θ, g y ∈ flatDomain Φ ∧
        Θ.toFun (chartAt (ComplexModel n) z y) = Φ.toFun (chartAt (ComplexModel n) (g z) (g y)) := by
  set I := 𝓘(ℂ, ComplexModel n) with hI
  have hrange : range I = univ := by simp [hI]
  let e := chartAt (ComplexModel n) z
  let e' := chartAt (ComplexModel n) (g z)
  set F : ComplexModel n → ComplexModel n := fun u => e' (g (e.symm u)) with hF
  set N : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' (univ ∩ g ⁻¹' e'.source) with hN
  have hNo : IsOpen N :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target
      (isOpen_univ.inter (hg.continuous.isOpen_preimage _ e'.open_source))
  have hzN : e z ∈ N := ⟨e.map_source (mem_chart_source _ z), by
    rw [mem_preimage, e.left_inv (mem_chart_source _ z)]
    exact ⟨mem_univ _, mem_chart_source _ (g z)⟩⟩
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
  refine ⟨RegularAtDimTransport.LocalHolomorphicEquivAt.comp Ψ Φ (hΨF ▸ hFz),?_,?_,?_⟩
  · intro u hu
    exact (hΨN hu.1).1
  · change Φ.toFun (Ψ.toFun (e z)) = Φ.toFun (e' (g z))
    rw [hΨF,hFz]
  · intro y hy
    change y ∈ e.source ∧ e y ∈ Ψ.source ∩ Ψ.toFun ⁻¹' Φ.source at hy
    have hyN := (hΨN hy.2.1).2
    rw [mem_preimage,e.left_inv hy.1] at hyN
    have hFy : F (e y) = e' (g y) := by simp only [hF,e.left_inv hy.1]
    have hyΦ : e' (g y) ∈ Φ.source := by
      have hh := hy.2.2
      rwa [mem_preimage,hΨF,hFy] at hh
    refine ⟨⟨hyN.2,hyΦ⟩,?_⟩
    change Φ.toFun (Ψ.toFun (e y)) = Φ.toFun (e' (g y))
    rw [hΨF,hFy]

/-- Whole original NC union coordinates are produced under every genuine local biholomorphism. -/
theorem isNormalCrossingsCarrier_preimage {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hexc : ∀ z, z ∉ exceptionalLocus n g) {H : Set Y}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    IsNormalCrossingsCarrier (n := n) (g ⁻¹' H) := by
  refine ⟨hH.1.preimage hg.continuous,fun z => ?_⟩
  obtain ⟨Φ,hsrc,h0,S,hflat⟩ := hH.2 (g z)
  obtain ⟨Θ,hΘsrc,hΘ0,hΘ⟩ := exists_pullback_flat_coordinates hg (hexc z) Φ
  refine ⟨Θ,hΘsrc,hΘ0.trans h0,S,?_⟩
  intro y hy
  obtain ⟨hdom,hcoord⟩ := hΘ y hy
  change g y ∈ H ↔ ∃ i ∈ S, Θ.toFun (chartAt (ComplexModel n) z y) i = 0
  rw [hcoord]
  exact hflat (g y) hdom

/-- The same actual full reader internally produces the literal preimage boundary pair. -/
theorem boundaryAdapted_preimage {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hexc : ∀ z, z ∉ exceptionalLocus n g) {H : Set Y} {E : List (Set Y)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) :
    IsBoundaryAdaptedCarrier (n := n) (g ⁻¹' H) (E.map (g ⁻¹' ·)) := by
  refine ⟨h.1.preimage hg.continuous,?_,fun z => ?_⟩
  · intro A hA
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
    exact (h.2.1 B hB).preimage hg.continuous
  · obtain ⟨Φ,S,B,hsrc,h0,hH,hB,hinj,hE⟩ := h.2.2 (g z)
    obtain ⟨Θ,hΘsrc,hΘ0,hΘ⟩ := exists_pullback_flat_coordinates hg (hexc z) Φ
    let c : Fin (E.map (g ⁻¹' ·)).length → Fin E.length := Fin.cast (List.length_map _)
    refine ⟨Θ,S,fun i => B (c i),hΘsrc,hΘ0.trans h0,?_,?_,?_,?_⟩
    · intro y hy
      obtain ⟨hdom,hcoord⟩ := hΘ y hy
      change g y ∈ H ↔ ∃ i ∈ S, Θ.toFun (chartAt (ComplexModel n) z y) i = 0
      rw [hcoord]
      exact hH (g y) hdom
    · intro i hi
      rw [get_map_preimage] at hi
      exact hB (c i) hi
    · intro i hi j hj hij
      simp only [mem_ofPred_eq,get_map_preimage] at hi hj
      exact Fin.cast_injective _ (hinj hi hj hij)
    · intro i hi y hy
      rw [get_map_preimage] at hi ⊢
      obtain ⟨hdom,hcoord⟩ := hΘ y hy
      rw [hcoord]
      exact hE (c i) hi (g y) hdom

/-- The genuine intrinsic count of the entire original preimage is the actual count at its image. -/
theorem branchMultiplicity_preimage {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hexc : ∀ z, z ∉ exceptionalLocus n g) {H : Set Y}
    (hH : IsNormalCrossingsCarrier (n := n) H)
    (hp : IsNormalCrossingsCarrier (n := n) (g ⁻¹' H)) (z : Z) :
    branchMultiplicity hp z = branchMultiplicity hH (g z) := by
  obtain ⟨Φ,hsrc,h0,S,hflat⟩ := hH.2 (g z)
  obtain ⟨Θ,hΘsrc,hΘ0,hΘ⟩ := exists_pullback_flat_coordinates hg (hexc z) Φ
  have hflat' : ∀ y ∈ flatDomain Θ, y ∈ g ⁻¹' H ↔ ∃ i ∈ S, flatCoord Θ i y = 0 := by
    intro y hy
    obtain ⟨hdom,hcoord⟩ := hΘ y hy
    change g y ∈ H ↔ ∃ i ∈ S, Θ.toFun (chartAt (ComplexModel n) z y) i = 0
    rw [hcoord]
    exact hflat (g y) hdom
  exact (branchMultiplicity_eq_card hp Θ (hΘ0.trans h0) S hflat').trans
    (branchMultiplicity_eq_card hH Φ h0 S hflat).symm

private theorem diffeomorph_no_exception
    (φ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y) (z : Z) :
    z ∉ exceptionalLocus n φ :=
  MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
    φ.contMDiff φ.symm.contMDiff φ.apply_symm_apply φ.symm_apply_apply z

/-- Actual whole carrier biholomorphic transport produces its true intrinsic count equality. -/
theorem branchMultiplicity_diffeomorph
    (φ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y) {H : Set Y}
    (hH : IsNormalCrossingsCarrier (n := n) H)
    (hp : IsNormalCrossingsCarrier (n := n) (φ ⁻¹' H)) (z : Z) :
    branchMultiplicity hp z = branchMultiplicity hH (φ z) :=
  branchMultiplicity_preimage φ.contMDiff (diffeomorph_no_exception φ) hH hp z

/-- The entire actual count value sets agree, using genuine biholomorphic surjectivity. -/
theorem range_branchMultiplicity_diffeomorph
    (φ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y) {H : Set Y}
    (hH : IsNormalCrossingsCarrier (n := n) H)
    (hp : IsNormalCrossingsCarrier (n := n) (φ ⁻¹' H)) :
    range (branchMultiplicity hp) = range (branchMultiplicity hH) := by
  ext r
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨φ z,(branchMultiplicity_diffeomorph φ hH hp z).symm⟩
  · rintro ⟨y,rfl⟩
    exact ⟨φ.symm y,by rw [branchMultiplicity_diffeomorph,φ.apply_symm_apply]⟩

/-- Every genuine whole original superlevel, including its entire highest centre, is an exact preimage. -/
theorem superlevel_branchMultiplicity_diffeomorph
    (φ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y) {H : Set Y}
    (hH : IsNormalCrossingsCarrier (n := n) H)
    (hp : IsNormalCrossingsCarrier (n := n) (φ ⁻¹' H)) (r : ℕ) :
    {z | r ≤ branchMultiplicity hp z} = φ ⁻¹' {y | r ≤ branchMultiplicity hH y} := by
  ext z
  simp only [mem_ofPred_eq,mem_preimage,branchMultiplicity_diffeomorph φ hH hp z]

/-- Whole actual count bounds and the count-one terminal condition agree in both directions. -/
theorem branchMultiplicity_bound_diffeomorph_iff
    (φ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y) {H : Set Y}
    (hH : IsNormalCrossingsCarrier (n := n) H)
    (hp : IsNormalCrossingsCarrier (n := n) (φ ⁻¹' H)) (b : ℕ) :
    (∀ z : Z, branchMultiplicity hp z ≤ b) ↔ (∀ y : Y, branchMultiplicity hH y ≤ b) := by
  constructor
  · intro h y
    have hh := h (φ.symm y)
    rwa [branchMultiplicity_diffeomorph,φ.apply_symm_apply] at hh
  · intro h z
    rw [branchMultiplicity_diffeomorph]
    exact h (φ z)

omit [IsComplexManifold n Y] in
/-- Two entire actual attained count maxima are equal without a supplied maximum identity. -/
theorem attained_maximum_eq {H : Set Y} (hH : IsNormalCrossingsCarrier (n := n) H)
    {r s : ℕ} (hr : ∀ y, branchMultiplicity hH y ≤ r)
    (har : {y | branchMultiplicity hH y = r}.Nonempty)
    (hs : ∀ y, branchMultiplicity hH y ≤ s)
    (has : {y | branchMultiplicity hH y = s}.Nonempty) : r = s := by
  obtain ⟨y,hy⟩ := har
  obtain ⟨z,hz⟩ := has
  have hys := hs y
  have hzr := hr z
  change branchMultiplicity hH y = r at hy
  change branchMultiplicity hH z = s at hz
  rw [hy] at hys
  rw [hz] at hzr
  exact Nat.le_antisymm hys hzr

/-- A genuine biholomorphism and nonempty actual NC carrier internally produce
both carriers, their unique common attained whole maximum and exact whole smooth centres. -/
theorem exists_unique_biholomorphic_highest_centre
    (φ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y) {H : Set Y}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hne : H.Nonempty) :
    ∃ hp : IsNormalCrossingsCarrier (n := n) (φ ⁻¹' H), ∃! r : ℕ,
      0 < r ∧ r ≤ n ∧ (∀ y : Y, branchMultiplicity hH y ≤ r) ∧
      {y | branchMultiplicity hH y = r}.Nonempty ∧
      (∀ z : Z, branchMultiplicity hp z ≤ r) ∧ {z | branchMultiplicity hp z = r}.Nonempty ∧
      {z | r ≤ branchMultiplicity hp z} = φ ⁻¹' {y | r ≤ branchMultiplicity hH y} ∧
      IsClosedSubmanifold n {y | r ≤ branchMultiplicity hH y} ∧
      IsClosedSubmanifold n {z | r ≤ branchMultiplicity hp z} := by
  have hp := isNormalCrossingsCarrier_preimage φ.contMDiff (diffeomorph_no_exception φ) hH
  obtain ⟨r,hr,hrn,hmax,hatt,-,-,-⟩ := exists_highest_multiplicity_stratum hH hne
  have hmaxp : ∀ z : Z, branchMultiplicity hp z ≤ r :=
    (branchMultiplicity_bound_diffeomorph_iff φ hH hp r).mpr hmax
  have hattp : {z | branchMultiplicity hp z = r}.Nonempty := by
    obtain ⟨y,hy⟩ := hatt
    refine ⟨φ.symm y,?_⟩
    change branchMultiplicity hp (φ.symm y) = r
    rw [branchMultiplicity_diffeomorph,φ.apply_symm_apply]
    exact hy
  refine ⟨hp,r,⟨hr,hrn,hmax,hatt,hmaxp,hattp,
    superlevel_branchMultiplicity_diffeomorph φ hH hp r,
    isClosedSubmanifold_highest_superlevel hH hmax,
    isClosedSubmanifold_highest_superlevel hp hmaxp⟩,?_⟩
  intro s hs
  exact attained_maximum_eq hH hs.2.2.1 hs.2.2.2.1 hmax hatt

end
end Hironaka.HironakaNormalCrossingsBiholomorphicMultiplicity
