import Hironaka.Algebra.ModuleFlatteningCenterAtPrime
import Hironaka.Geometry.ModuleFlatteningCenterPrincipal
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# The original maximal-minor blowup preserves the whole original module free locus

Every actual free point internally supplies a nonzero original principal
neighborhood of the same whole ideal. The actual original blowup is an
isomorphism there, hence on every original open contained in the native
module free locus. Its actual center avoids that entire original open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct

namespace Hironaka.Geometry.ModuleFlatteningCenter

open Algebra.ModuleFlatteningCenter Algebra.ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R M : Type u} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.FinitePresentation R M]

/-- Every point of the entire original module free locus belongs to the actual
isomorphism locus of the same original maximal-minor blowup. -/
theorem freeLocus_subset_isomorphismOpen
    {n r : ℕ} (m : Fin n → M) (hm : Submodule.span R (Set.range m) = ⊤)
    (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M))
    (δ : R) (V : Matrix (Fin r) (Fin n) R)
    (hcoord : ∀ i j, algebraMap R (FractionRing R) (V i j) =
      algebraMap R (FractionRing R) δ * b.repr ((1 : FractionRing R) ⊗ₜ[R] m j) i)
    (s₀ : Fin r → Fin n) (hs₀ : columnMinor V s₀ ≠ 0) :
    Module.freeLocus R M ⊆
      (ModificationCenter.isomorphismOpen (affineBlowupStructure (minorIdeal V)) :
        Set (Spec (.of R))) := by
  intro p hp
  let : Module.Free (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] M) :=
    (Module.mem_freeLocus_iff_tensor p (Localization.AtPrime p.asIdeal)).mp hp
  obtain ⟨a, s, hap, hs, hI⟩ :=
    exists_away_nonzero_minor_generator m hm b δ V hcoord s₀ hs₀ p.asIdeal
  have ha : a ≠ 0 := by rintro rfl; exact hap p.asIdeal.zero_mem
  exact basicOpen_le_isomorphismOpen_of_away_principal (minorIdeal V) a (columnMinor V s)
    ha hs hI hap

/-- The literal same original blowup is an isomorphism over the whole original
open whose original module is locally free. -/
theorem isIso_restrict_of_subset_freeLocus
    {n r : ℕ} (m : Fin n → M) (hm : Submodule.span R (Set.range m) = ⊤)
    (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M))
    (δ : R) (V : Matrix (Fin r) (Fin n) R)
    (hcoord : ∀ i j, algebraMap R (FractionRing R) (V i j) =
      algebraMap R (FractionRing R) δ * b.repr ((1 : FractionRing R) ⊗ₜ[R] m j) i)
    (s₀ : Fin r → Fin n) (hs₀ : columnMinor V s₀ ≠ 0)
    (U : (Spec (.of R)).Opens) (hU : (U : Set (Spec (.of R))) ⊆ Module.freeLocus R M) :
    IsIso (affineBlowupStructure (minorIdeal V) ∣_ U) :=
  (ModificationCenter.le_isomorphismOpen_iff _ U).mp
    (hU.trans (freeLocus_subset_isomorphismOpen m hm b δ V hcoord s₀ hs₀))

/-- The actual center of the same original maximal-minor blowup avoids the
entire original open, as an inclusion of actual native closed subsets. -/
theorem center_le_compl_of_subset_freeLocus
    {n r : ℕ} (m : Fin n → M) (hm : Submodule.span R (Set.range m) = ⊤)
    (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M))
    (δ : R) (V : Matrix (Fin r) (Fin n) R)
    (hcoord : ∀ i j, algebraMap R (FractionRing R) (V i j) =
      algebraMap R (FractionRing R) δ * b.repr ((1 : FractionRing R) ⊗ₜ[R] m j) i)
    (s₀ : Fin r → Fin n) (hs₀ : columnMinor V s₀ ≠ 0)
    (U : (Spec (.of R)).Opens) (hU : (U : Set (Spec (.of R))) ⊆ Module.freeLocus R M) :
    ModificationCenter.center (affineBlowupStructure (minorIdeal V)) ≤ U.compl := by
  apply (ModificationCenter.center_le_iff _ U.compl).mpr
  have hcompl : U.compl.compl = U := by
    ext x
    simp [TopologicalSpace.Opens.compl, TopologicalSpace.Closeds.compl]
  rw [hcompl]
  exact isIso_restrict_of_subset_freeLocus m hm b δ V hcoord s₀ hs₀ U hU

end Hironaka.Geometry.ModuleFlatteningCenter
