import Hironaka.Analytic.AnalyticJacobianCriterion

set_option autoImplicit false

/-!
# The hypersurface part of the Jacobian stratification

For a locally single-equation analytic set, adjoining all first derivatives
produces a genuine finite holomorphic local presentation.  A nonzero derivative
minor forces local regularity, so the complement of the expected regular
hypersurface locus is contained in this derivative core.

This is deliberately an over-approximation to the true singular locus.  A
single *nonreduced* equation already shows why equality and strict dimension
drop cannot be derived from the current `LocalDecomposition` interface:
`f(z) = z₀²` cuts out a smooth hyperplane but every first derivative vanishes
on it.  Obtaining equality or dimension drop therefore needs an explicit
reduced/coherent-ideal API, not a formal change of names.
-/

open Set

namespace Hironaka.AnalyticCoherentJacobianStratification

open Hironaka.RegularLocusDense AnalyticLocalStatement

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- For a local hypersurface equation in the preferred chart at `x`, the
finite derivative core is the hypersurface together with the simultaneous
vanishing of all coordinate derivatives. -/
def localHypersurfaceDerivativeCore (S : Set M) (x : M)
    (f : ComplexModel n → ℂ) : Set M :=
  S ∩ (complexChartAt (n := n) x).val ⁻¹'
    {z | ∀ j : Fin n,
      fderiv ℂ f z (AnalyticJacobianSingularCore.coordinateDirection j) = 0}

/-- The derivative core of an honest local hypersurface equation has a finite
holomorphic presentation at the chosen point. -/
theorem nonempty_presentation_localHypersurfaceDerivativeCore
    {S : Set M} {x : M} {N : Set (ComplexModel n)} (f : ComplexModel n → ℂ)
    (hN : IsOpen N) (hxN : (complexChartAt (n := n) x).val x ∈ N)
    (hNtarget : N ⊆ (complexChartAt (n := n) x).val.target)
    (hf : DifferentiableOn ℂ f N)
    (hzero : ∀ {y : M},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ N →
        (y ∈ S ↔ f ((complexChartAt (n := n) x).val y) = 0)) :
    Nonempty (ComplexAnalyticPresentationAt (n := n)
      (localHypersurfaceDerivativeCore (n := n) S x f) x) := by
  let e := (complexChartAt (n := n) x).val
  let g : Fin (1 + n) → ComplexModel n → ℂ :=
    Fin.addCases (fun _ : Fin 1 => f)
      (fun j z => fderiv ℂ f z (AnalyticJacobianSingularCore.coordinateDirection j))
  refine ⟨{ generatorCount := 1 + n
            generator := g
            coordinateNeighborhood := N
            isOpen_coordinateNeighborhood := hN
            center_mem_coordinateNeighborhood := hxN
            coordinateNeighborhood_subset_target := hNtarget
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · intro a
    refine Fin.addCases ?_ ?_ a
    · intro _
      simpa [g] using hf
    · intro j
      simpa [g] using differentiableOn_fderiv_apply_of_isOpen hf hN
        (AnalyticJacobianSingularCore.coordinateDirection j)
  · intro y hy hyN
    change (y ∈ S ∧ ∀ j : Fin n,
      fderiv ℂ f (e y) (AnalyticJacobianSingularCore.coordinateDirection j) = 0) ↔
        ∀ a, g a (e y) = 0
    constructor
    · rintro ⟨hyS, hder⟩ a
      refine Fin.addCases ?_ ?_ a
      · intro _
        simpa [g] using (hzero hy hyN).mp hyS
      · intro j
        simpa [g] using hder j
    · intro hg
      refine ⟨(hzero hy hyN).mpr ?_, ?_⟩
      · simpa [g] using hg (Fin.castAdd n (0 : Fin 1))
      · intro j
        simpa [g] using hg (Fin.natAdd 1 j)

/-- A nonzero coordinate derivative of a local hypersurface equation gives a
regular point of the expected dimension, even when the presentation is made in
a chart centred at another point. -/
theorem regularAtDim_of_localHypersurfaceMinor_ne_zero_in_chart
    {S : Set M} {x y : M} {N : Set (ComplexModel n)} (f : ComplexModel n → ℂ)
    (hN : IsOpen N) (hNtarget : N ⊆ (complexChartAt (n := n) x).val.target)
    (hf : DifferentiableOn ℂ f N)
    (hzero : ∀ {u : M},
      u ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val u ∈ N →
        (u ∈ S ↔ f ((complexChartAt (n := n) x).val u) = 0))
    (hy : y ∈ (complexChartAt (n := n) x).val.source)
    (hyN : (complexChartAt (n := n) x).val y ∈ N) (hyS : y ∈ S)
    (j : Fin n)
    (hminor : fderiv ℂ f ((complexChartAt (n := n) x).val y)
      (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0) :
    RegularAtDim (n := n) S y (n - 1) := by
  let e := (complexChartAt (n := n) x).val
  let B : Set (ComplexModel n) := {z | e.symm z ∈ S}
  have hzeroB : ∀ z ∈ N, z ∈ B ↔ f z = 0 := by
    intro z hz
    have hzt : z ∈ e.target := hNtarget hz
    have h := hzero (e.map_target hzt) (by rw [e.right_inv hzt]; exact hz)
    rwa [e.right_inv hzt] at h
  have hyB : e y ∈ B := by
    change e.symm (e y) ∈ S
    rw [e.left_inv hy]
    exact hyS
  let g : Fin 1 → ComplexModel n → ℂ := fun _ => f
  have hli : LinearIndependent ℂ (fun _ : Fin 1 => fderiv ℂ f (e y)) := by
    rw [linearIndependent_unique_iff]
    intro hzeroDeriv
    apply hminor
    rw [hzeroDeriv]
    rfl
  obtain ⟨Φ, hΦN, hΦ0, hΦflat⟩ :=
    AnalyticJacobianCriterion.exists_flattening_of_localCompleteIntersection
      (S := B) (N := N) (q := e y) (g := g) hN hyN hyB
      (fun _ => hf) (by
        intro z hz
        constructor
        · intro hzB _
          exact hzeroB z hz |>.mp hzB
        · intro hz0
          exact hzeroB z hz |>.mpr (by simpa using hz0 (0 : Fin 1))) (by
            simpa [g] using hli)
  refine regularAtDim_of_flattening_of_mem (Nat.sub_le _ _) Φ ?_ hyS hy
    (by simpa [e] using Φ.center_mem_source)
  intro u hu huΦ
  have h := hΦflat (e u) huΦ
  simpa [B, e.left_inv hu] using h

/-- On a local hypersurface chart, any point not regular of dimension `n - 1`
lies in the derivative core.  This is the sound direction towards a singular
locus theorem: the derivative core may be larger for nonreduced equations. -/
theorem not_regularAtDim_mem_localHypersurfaceDerivativeCore
    {S : Set M} {x y : M} {N : Set (ComplexModel n)} (f : ComplexModel n → ℂ)
    (hN : IsOpen N) (hNtarget : N ⊆ (complexChartAt (n := n) x).val.target)
    (hf : DifferentiableOn ℂ f N)
    (hzero : ∀ {u : M},
      u ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val u ∈ N →
        (u ∈ S ↔ f ((complexChartAt (n := n) x).val u) = 0))
    (hy : y ∈ (complexChartAt (n := n) x).val.source)
    (hyN : (complexChartAt (n := n) x).val y ∈ N) (hyS : y ∈ S)
    (hnot : ¬ RegularAtDim (n := n) S y (n - 1)) :
    y ∈ localHypersurfaceDerivativeCore (n := n) S x f := by
  classical
  change y ∈ S ∧ ∀ j : Fin n,
    fderiv ℂ f ((complexChartAt (n := n) x).val y)
      (AnalyticJacobianSingularCore.coordinateDirection j) = 0
  refine ⟨hyS, ?_⟩
  by_contra hder
  simp only [not_forall] at hder
  exact hnot (regularAtDim_of_localHypersurfaceMinor_ne_zero_in_chart f hN hNtarget hf
    hzero hy hyN hyS hder.choose hder.choose_spec)


/-- The distinguished equation of a local-decomposition branch presented by
one equation.  The equality proof is only used to type its unique index. -/
def localHypersurfaceEquation {A : Set M} {p : M}
    (D : LocalDecomposition (n := n) A p) (i : Fin D.count)
    (hone : D.eqnCount i = 1) : ComplexModel n → ℂ :=
  D.eqn i ⟨0, by omega⟩

omit [IsComplexManifold n M] in
/-- On a branch whose local presentation has exactly one equation, membership
is equivalent to vanishing of that distinguished equation. -/
theorem mem_piece_iff_localHypersurfaceEquation
    {A : Set M} {p y : M} (D : LocalDecomposition (n := n) A p)
    (i : Fin D.count) (hone : D.eqnCount i = 1) (hy : y ∈ D.nbhd) :
    y ∈ D.piece i ↔
      localHypersurfaceEquation (n := n) D i hone
        ((complexChartAt (n := n) p).val y) = 0 := by
  let j0 : Fin (D.eqnCount i) := ⟨0, by omega⟩
  change y ∈ D.piece i ↔ D.eqn i j0 ((complexChartAt (n := n) p).val y) = 0
  constructor
  · intro hyi
    exact (D.mem_piece_iff i y hy).mp hyi j0
  · intro hzero
    apply (D.mem_piece_iff i y hy).mpr
    intro j
    have hj : j = j0 := Fin.ext (by omega)
    simpa [hj] using hzero

/-- The derivative core of a one-equation local-decomposition branch has a
finite holomorphic presentation at the centre of that decomposition. -/
theorem nonempty_presentation_localPieceHypersurfaceDerivativeCore
    {A : Set M} {p : M} (D : LocalDecomposition (n := n) A p)
    (i : Fin D.count) (hone : D.eqnCount i = 1) :
    Nonempty (ComplexAnalyticPresentationAt (n := n)
      (localHypersurfaceDerivativeCore (n := n) (D.piece i) p
        (localHypersurfaceEquation (n := n) D i hone)) p) := by
  let e := (complexChartAt (n := n) p).val
  let f := localHypersurfaceEquation (n := n) D i hone
  apply nonempty_presentation_localHypersurfaceDerivativeCore f
  · exact e.isOpen_image_of_subset_source D.isOpen_nbhd D.nbhd_subset_source
  · exact mem_image_of_mem e D.mem_nbhd
  · rintro _ ⟨y, hy, rfl⟩
    exact e.map_source (D.nbhd_subset_source hy)
  · exact D.eqn_holomorphic i ⟨0, by omega⟩
  · intro y hy hyN
    obtain ⟨y', hyW, hy'e⟩ := hyN
    have hyW' : y ∈ D.nbhd := by
      rwa [← e.injOn (D.nbhd_subset_source hyW) hy hy'e]
    exact mem_piece_iff_localHypersurfaceEquation D i hone hyW'

/-- For a one-equation local-decomposition branch, every point of the local
branch that fails to be regular of dimension `n - 1` lies in its analytic
hypersurface derivative core. -/
theorem not_regularAtDim_mem_localPieceHypersurfaceDerivativeCore
    {A : Set M} {p y : M} (D : LocalDecomposition (n := n) A p)
    (i : Fin D.count) (hone : D.eqnCount i = 1)
    (hyW : y ∈ D.nbhd) (hyi : y ∈ D.piece i)
    (hnot : ¬ RegularAtDim (n := n) (D.piece i) y (n - 1)) :
    y ∈ localHypersurfaceDerivativeCore (n := n) (D.piece i) p
      (localHypersurfaceEquation (n := n) D i hone) := by
  let e := (complexChartAt (n := n) p).val
  let f := localHypersurfaceEquation (n := n) D i hone
  apply not_regularAtDim_mem_localHypersurfaceDerivativeCore f
  · exact e.isOpen_image_of_subset_source D.isOpen_nbhd D.nbhd_subset_source
  · rintro _ ⟨z, hz, rfl⟩
    exact e.map_source (D.nbhd_subset_source hz)
  · exact D.eqn_holomorphic i ⟨0, by omega⟩
  · intro u hu huN
    obtain ⟨u', huW, hu'e⟩ := huN
    have huW' : u ∈ D.nbhd := by
      rwa [← e.injOn (D.nbhd_subset_source huW) hu hu'e]
    exact mem_piece_iff_localHypersurfaceEquation D i hone huW'
  · exact D.nbhd_subset_source hyW
  · exact mem_image_of_mem e hyW
  · exact hyi
  · exact hnot

end

end Hironaka.AnalyticCoherentJacobianStratification
