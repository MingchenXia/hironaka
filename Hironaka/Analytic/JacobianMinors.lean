/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.AnalyticJacobianSingularCore
import Hironaka.Analytic.AnalyticLocalStatement
import Hironaka.Manifold.HolomorphicContDiff

import Hironaka.Analytic.PureDimension

set_option autoImplicit false
namespace Hironaka.AnalyticJacobianSingularCore
open Hironaka
noncomputable section
open Set
open Hironaka.AnalyticLocalStatement
variable {n : ℕ}

/-- The finite choices of `r` rows and `r` columns used to form an `r × r`
Jacobian minor.  Repetitions are permitted; this harmlessly includes zero
minors and avoids making injectivity part of the low-level API. -/
abbrev JacobianMinorIndex (m n r : ℕ) : Type :=
  (Fin r → Fin m) × (Fin r → Fin n)

/-- A fixed complex Jacobian minor of a finite equation family. -/
def jacobianMinor {m r : ℕ} (f : Fin m → ComplexModel n → ℂ)
    (rows : Fin r → Fin m) (cols : Fin r → Fin n) (z : ComplexModel n) : ℂ :=
  (Matrix.of fun a b => fderiv ℂ (f (rows a)) z (coordinateDirection (cols b))).det

/-- A finite enumeration of all fixed-size Jacobian minors. -/
def jacobianMinorGenerator {m r : ℕ} (f : Fin m → ComplexModel n → ℂ) :
    Fin (Fintype.card (JacobianMinorIndex m n r)) → ComplexModel n → ℂ := fun a =>
  let q := (Fintype.equivFin (JacobianMinorIndex m n r)).symm a
  jacobianMinor f q.1 q.2

/-- The common zero locus of all `r × r` Jacobian minors. -/
def jacobianRankDefect {m r : ℕ} (f : Fin m → ComplexModel n → ℂ) : Set (ComplexModel n) :=
  {z | ∀ a, jacobianMinorGenerator (n := n) (r := r) f a z = 0}

/-- Fixed Jacobian minors of holomorphic equations are holomorphic.  The
nontrivial input is the existing several-variable theorem that a fixed
directional Fréchet derivative of a holomorphic function is holomorphic. -/
theorem differentiableOn_jacobianMinor {m r : ℕ} {f : Fin m → ComplexModel n → ℂ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (rows : Fin r → Fin m) (cols : Fin r → Fin n) :
    DifferentiableOn ℂ (jacobianMinor f rows cols) U := by
  have hdet : jacobianMinor f rows cols = fun z =>
      ∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ •
        ∏ a : Fin r, fderiv ℂ (f (rows (σ a))) z (coordinateDirection (cols a)) := by
    funext z
    simp only [jacobianMinor, Matrix.det_apply, Matrix.of_apply]
  rw [hdet]
  have hsum : DifferentiableOn ℂ
      (∑ σ : Equiv.Perm (Fin r), fun z => Equiv.Perm.sign σ •
        ∏ a : Fin r, fderiv ℂ (f (rows (σ a))) z (coordinateDirection (cols a))) U := by
    refine DifferentiableOn.sum (𝕜 := ℂ) (E := ComplexModel n) (F := ℂ)
      (u := (Finset.univ : Finset (Equiv.Perm (Fin r))))
      (A := fun σ z => Equiv.Perm.sign σ •
        ∏ a : Fin r, fderiv ℂ (f (rows (σ a))) z (coordinateDirection (cols a))) fun σ _ => ?_
    refine (PureDimension.differentiableOn_finset_prod Finset.univ
      (fun a => fun z => fderiv ℂ (f (rows (σ a))) z (coordinateDirection (cols a))) U ?_).const_smul _
    intro a _
    exact differentiableOn_fderiv_apply_of_isOpen (hf (rows (σ a))) hU
      (coordinateDirection (cols a))
  refine hsum.congr fun z _ => ?_
  exact (Finset.sum_apply z Finset.univ (fun σ : Equiv.Perm (Fin r) => fun z =>
    Equiv.Perm.sign σ • ∏ a : Fin r,
      fderiv ℂ (f (rows (σ a))) z (coordinateDirection (cols a)))).symm

/-- The finite enumeration of fixed Jacobian minors is holomorphic on the same
open set as the original equations. -/
theorem differentiableOn_jacobianMinorGenerator {m r : ℕ} {f : Fin m → ComplexModel n → ℂ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hf : ∀ i, DifferentiableOn ℂ (f i) U) :
    ∀ a, DifferentiableOn ℂ (jacobianMinorGenerator (n := n) (r := r) f a) U := by
  intro a
  simp only [jacobianMinorGenerator]
  exact differentiableOn_jacobianMinor hU hf _ _

/-- On any open domain where the original equations are holomorphic,
`jacobianRankDefect` is literally the common zero locus of a finite
holomorphic family. -/
theorem mem_jacobianRankDefect_iff {m r : ℕ} (f : Fin m → ComplexModel n → ℂ)
    (z : ComplexModel n) :
    z ∈ jacobianRankDefect (n := n) (r := r) f ↔
      ∀ a, jacobianMinorGenerator (n := n) (r := r) f a z = 0 := Iff.rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- For a local decomposition branch, impose both its original equations and
all `r × r` Jacobian minors in the distinguished chart. -/
def localPieceJacobianCore {A : Set M} {p : M}
    (D : LocalDecomposition (n := n) A p) (i : Fin D.count) (r : ℕ) : Set M :=
  D.piece i ∩ (complexChartAt (n := n) p).val ⁻¹'
    (jacobianRankDefect (n := n) (r := r) (D.eqn i))

/-- The Jacobian core built from one local-decomposition branch has a genuine
finite holomorphic presentation at the centre of that decomposition. -/
theorem nonempty_presentation_localPieceJacobianCore {A : Set M} {p : M}
    (D : LocalDecomposition (n := n) A p) (i : Fin D.count) (r : ℕ) :
    Nonempty (ComplexAnalyticPresentationAt (n := n) (localPieceJacobianCore D i r) p) := by
  classical
  let e := (complexChartAt (n := n) p).val
  let q := JacobianMinorIndex (D.eqnCount i) n r
  let g : Fin (D.eqnCount i + Fintype.card q) → ComplexModel n → ℂ :=
    Fin.addCases (D.eqn i) (jacobianMinorGenerator (n := n) (r := r) (D.eqn i))
  have hopen : IsOpen (e '' D.nbhd) :=
    e.isOpen_image_of_subset_source D.isOpen_nbhd D.nbhd_subset_source
  refine ⟨{ generatorCount := D.eqnCount i + Fintype.card q
            generator := g
            coordinateNeighborhood := e '' D.nbhd
            isOpen_coordinateNeighborhood := hopen
            center_mem_coordinateNeighborhood := mem_image_of_mem e D.mem_nbhd
            coordinateNeighborhood_subset_target := ?_
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact e.map_source (D.nbhd_subset_source hy)
  · intro a
    refine Fin.addCases ?_ ?_ a
    · intro j
      simpa [g] using D.eqn_holomorphic i j
    · intro j
      simpa [g, q] using differentiableOn_jacobianMinorGenerator (n := n) (r := r) hopen
        (fun k => D.eqn_holomorphic i k) j
  · intro y hy hyN
    obtain ⟨y', hyW, hy'y⟩ := hyN
    have hyW' : y ∈ D.nbhd := by
      rwa [← e.injOn (D.nbhd_subset_source hyW) hy hy'y]
    have hpiece : y ∈ D.piece i ↔ ∀ j, D.eqn i j (e y) = 0 :=
      D.mem_piece_iff i y hyW'
    change (y ∈ D.piece i ∧ e y ∈ jacobianRankDefect (n := n) (r := r) (D.eqn i)) ↔ _
    rw [mem_jacobianRankDefect_iff]
    constructor
    · rintro ⟨hyi, hyminor⟩ a
      refine Fin.addCases ?_ ?_ a
      · intro j
        simpa [g] using hpiece.mp hyi j
      · intro j
        simpa [g, q] using hyminor j
    · intro h
      constructor
      · apply hpiece.mpr
        intro j
        simpa [g] using h (Fin.castAdd (Fintype.card q) j)
      · intro j
        simpa [g, q] using h (Fin.natAdd (D.eqnCount i) j)

end
end Hironaka.AnalyticJacobianSingularCore
