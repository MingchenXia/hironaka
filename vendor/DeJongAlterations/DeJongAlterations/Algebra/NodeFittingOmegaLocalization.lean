import DeJongAlterations.Algebra.NodeFittingOmegaFinite
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Actual differential localization and entire intrinsic Fitting ideals

All maps are the native maps on the original rings and differential modules.
The statements require no Noetherian hypothesis. This is the algebraic overlap
producer; actual affine ideal-sheaf gluing is a separate geometric step.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingOmega

open NodeFittingModule
open scoped TensorProduct

universe u v w
variable (R : Type u) (S : Type v) (T : Type w)
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The actual native differential tensor equivalence transports native finite presentation. -/
theorem finitePresentation_of_formallyEtale [Algebra.FormallyEtale S T]
    [Module.FinitePresentation S (KaehlerDifferential R S)] :
    Module.FinitePresentation T (KaehlerDifferential R T) :=
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).finitePresentation_iff.mp
    inferInstance

/-- The entire original intrinsic ideal follows the actual formally etale coefficient map. -/
theorem fittingIdeal_formallyEtale [Algebra.FormallyEtale S T]
    [Module.FinitePresentation S (KaehlerDifferential R S)] (i : ℕ) :
    letI : Module.FinitePresentation T (KaehlerDifferential R T) :=
      finitePresentation_of_formallyEtale R S T
    (fittingIdeal (R := S) (M := KaehlerDifferential R S) i).map (algebraMap S T) =
      fittingIdeal (R := T) (M := KaehlerDifferential R T) i := by
  let : Module.FinitePresentation T (KaehlerDifferential R T) :=
    finitePresentation_of_formallyEtale R S T
  exact (fittingIdeal_baseChange (R := S) (M := KaehlerDifferential R S) T i).trans
    (fittingIdeal_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T) i)

/-- Native finite presentation persists under the actual target localization. -/
theorem finitePresentation_localization (M : Submonoid S) [IsLocalization M T]
    [Module.FinitePresentation S (KaehlerDifferential R S)] :
    Module.FinitePresentation T (KaehlerDifferential R T) := by
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization M
  exact finitePresentation_of_formallyEtale R S T

/-- Full original intrinsic differential ideals localize along the actual original coefficient map. -/
theorem fittingIdeal_localization (M : Submonoid S) [IsLocalization M T]
    [Module.FinitePresentation S (KaehlerDifferential R S)] (i : ℕ) :
    letI : Module.FinitePresentation T (KaehlerDifferential R T) :=
      finitePresentation_localization R S T M
    (fittingIdeal (R := S) (M := KaehlerDifferential R S) i).map (algebraMap S T) =
      fittingIdeal (R := T) (M := KaehlerDifferential R T) i := by
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization M
  exact fittingIdeal_formallyEtale R S T i

/-- The original native Jacobi--Zariski map is an equivalence when its actual base is unramified. -/
def baseEquiv [Algebra.FormallyUnramified R S] :
    KaehlerDifferential R T ≃ₗ[T] KaehlerDifferential S T := by
  refine LinearEquiv.ofBijective (KaehlerDifferential.map R S T T) ⟨?_,
    KaehlerDifferential.map_surjective R S T⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-- Every original differential is retained under the same actual native base-change map. -/
@[simp]
theorem baseEquiv_D [Algebra.FormallyUnramified R S] (t : T) :
    baseEquiv R S T (KaehlerDifferential.D R T t) = KaehlerDifferential.D S T t := by
  change KaehlerDifferential.map R S T T (KaehlerDifferential.D R T t) = _
  simp

/-- Native finite presentation follows the actual unramified-base differential equivalence. -/
theorem finitePresentation_changeBase [Algebra.FormallyUnramified R S]
    [Module.FinitePresentation T (KaehlerDifferential R T)] :
    Module.FinitePresentation T (KaehlerDifferential S T) :=
  (baseEquiv R S T).finitePresentation_iff.mp inferInstance

/-- The whole intrinsic ideal is independent of an actual formally unramified base localization. -/
theorem fittingIdeal_changeBase [Algebra.FormallyUnramified R S]
    [Module.FinitePresentation T (KaehlerDifferential R T)] (i : ℕ) :
    letI : Module.FinitePresentation T (KaehlerDifferential S T) :=
      finitePresentation_changeBase R S T
    fittingIdeal (R := T) (M := KaehlerDifferential R T) i =
      fittingIdeal (R := T) (M := KaehlerDifferential S T) i := by
  let : Module.FinitePresentation T (KaehlerDifferential S T) :=
    finitePresentation_changeBase R S T
  exact fittingIdeal_equiv (baseEquiv R S T) i

variable (R' : Type*) [CommRing R'] [Algebra R R'] [Algebra R' T]
  [IsScalarTower R R' T]

/-- Both original coefficient localizations internally produce native finite presentation. -/
theorem finitePresentation_doubleLocalization (M : Submonoid S) (N : Submonoid R)
    [IsLocalization M T] [IsLocalization N R']
    [Module.FinitePresentation S (KaehlerDifferential R S)] :
    Module.FinitePresentation T (KaehlerDifferential R' T) := by
  let : Module.FinitePresentation T (KaehlerDifferential R T) :=
    finitePresentation_localization R S T M
  let : Algebra.FormallyEtale R R' := Algebra.FormallyEtale.of_isLocalization N
  exact finitePresentation_changeBase R R' T

/-- Exact whole-ideal overlap under both actual original coefficient localizations. -/
theorem fittingIdeal_doubleLocalization (M : Submonoid S) (N : Submonoid R)
    [IsLocalization M T] [IsLocalization N R']
    [Module.FinitePresentation S (KaehlerDifferential R S)] (i : ℕ) :
    letI : Module.FinitePresentation T (KaehlerDifferential R' T) :=
      finitePresentation_doubleLocalization R S T R' M N
    (fittingIdeal (R := S) (M := KaehlerDifferential R S) i).map (algebraMap S T) =
      fittingIdeal (R := T) (M := KaehlerDifferential R' T) i := by
  let : Module.FinitePresentation T (KaehlerDifferential R T) :=
    finitePresentation_localization R S T M
  let : Algebra.FormallyEtale R R' := Algebra.FormallyEtale.of_isLocalization N
  exact (fittingIdeal_localization R S T M i).trans (fittingIdeal_changeBase R R' T i)

end DeJongAlterations.Algebra.NodeFittingOmega
