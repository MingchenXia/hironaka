import DeJongAlterations.StableModificationBridge.ClosedIdealAffineLayer
import DeJongAlterations.StableModificationBridge.NilradicalUniformPower
import DeJongAlterations.StableModification.Cohomology.CechPushforward

/-! Actual affine reduction INTERNALLY kills the first cohomology of every original native ideal module. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.NilradicalCechVanishing

open CategoryTheory Limits Opposite AlgebraicGeometry
open StableModification StableModification.Cohomology
open Geometry.ProperSteinProjectiveCech ClosedIdealAffineLayer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X : Scheme.{u}} {R : Type u} [CommRing R]

/-- Every original cochain of a SAME actual zero ideal vanishes, with the original cover and coefficients. -/
theorem isZero_of_ideal_eq_bot (I : X.IdealSheafData) (hI : I = ⊥)
    (C : FiniteAffineCover X) (c : R →+* Γ(X, ⊤)) (p : ℕ) :
    IsZero (cechCohomology I.dja_toModules C.U c p) := by
  classical
  have hsub (T : Finset C.ι) (hT : T.Nonempty) :
      Subsingleton Γ(I.dja_toModules, T.inf C.U) := by
    let U : X.affineOpens := ⟨T.inf C.U, C.isAffineOpen_inf T hT⟩
    let : Subsingleton (I.ideal U) := by
      rw [hI]
      change Subsingleton (⊥ : Ideal Γ(X, U))
      infer_instance
    exact (I.dja_toModulesSectionsEquiv U).injective.subsingleton
  let : Subsingleton (subsetCechCardPiece (cechDiagram I.dja_toModules C.U c) (p + 1)) :=
    ⟨fun a b => by
      apply Subtype.ext
      funext T
      by_cases hT : T.card = p + 1
      · exact @Subsingleton.elim Γ(I.dja_toModules, T.inf C.U)
          (hsub T (Finset.card_pos.mp (by omega))) _ _
      · exact (a.property T hT).trans (b.property T hT).symm⟩
  apply ShortComplex.isZero_homology_of_isZero_X₂
  change IsZero (ModuleCat.of R (subsetCechCardPiece (cechDiagram I.dja_toModules C.U c) (p + 1)))
  exact ModuleCat.isZero_of_subsingleton _

/-- Actual quotient-pullback layer exactness and affine target acyclicity give the original ideal-product step. -/
theorem isZero_first_of_mul (N I : X.IdealSheafData) [IsLocallyNoetherian X]
    [IsAffine N.subscheme] (C : FiniteAffineCover X) (c : R →+* Γ(X, ⊤))
    (hNI : IsZero (cechCohomology (N * I).dja_toModules C.U c 1)) :
    IsZero (cechCohomology I.dja_toModules C.U c 1) := by
  let : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) I.dja_toModules :=
    I.dja_isFinitePresentation_toModules
  let : I.dja_toModules.IsQuasicoherent := inferInstance
  let G := (Scheme.Modules.pullback N.subschemeι).obj I.dja_toModules
  let f := idealInclusion (show N * I ≤ I from fun _W => Ideal.mul_le_right)
  let g := (Scheme.Modules.pullbackPushforwardAdjunction N.subschemeι).unit.app I.dja_toModules
  let α := sectionsDiagramMap c f (fun T : Finset C.ι => T.inf C.U)
    (fun _ _ h => Finset.inf_mono h) (fun _ => le_top)
  let β := sectionsDiagramMap c g (fun T : Finset C.ι => T.inf C.U)
    (fun _ _ h => Finset.inf_mono h) (fun _ => le_top)
  have hlocal (T : Finset C.ι) (hT : T.Nonempty) :
      Function.Exact (α.app T).hom (β.app T).hom ∧
        Function.Injective (α.app T).hom ∧ Function.Surjective (β.app T).hom :=
    affine_exact N I ⟨T.inf C.U, C.isAffineOpen_inf T hT⟩
  have hS := SubsetNonemptyExactness.sequence_shortExact α β hlocal
  have hcov : ⨆ j, N.subschemeι ⁻¹ᵁ C.U j = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, C.iSup_eq_top, Scheme.Hom.preimage_top]
  have haff (T : Finset C.ι) (hT : T.Nonempty) :
      IsAffineOpen (T.inf (fun j => N.subschemeι ⁻¹ᵁ C.U j)) := by
    rw [← preimage_finsetInf N.subschemeι C.U T]
    exact (C.isAffineOpen_inf T hT).preimage N.subschemeι
  have hz : IsZero (cechCohomology ((Scheme.Modules.pushforward N.subschemeι).obj G) C.U c 1) :=
    (isZero_cechCohomology_of_isAffine G (fun j => N.subschemeι ⁻¹ᵁ C.U j)
      hcov haff (N.subschemeι.appTop.hom.comp c) 0).of_iso
      (cechCohomologyPushforwardIso N.subschemeι G c C.U 1)
  exact (hS.homology_exact₂ 1).isZero_of_both_isZero hNI hz

/-- Every actual original ideal has first Čech cohomology zero, INTERNALLY from its SAME affine nilradical reduction. -/
theorem isZero_first_of_affine_reduction (X : Scheme.{u}) [IsLocallyNoetherian X]
    [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffine X.nilradical.subscheme] (I : X.IdealSheafData)
    (C : FiniteAffineCover X) (c : R →+* Γ(X, ⊤)) :
    IsZero (cechCohomology I.dja_toModules C.U c 1) := by
  obtain ⟨e, _hepos, he⟩ := NilradicalUniformPower.exists_positive_pow_eq_bot X
  have hind (n : ℕ) : ∀ J : X.IdealSheafData, X.nilradical ^ n * J = ⊥ →
      IsZero (cechCohomology J.dja_toModules C.U c 1) := by
    induction n with
    | zero =>
        intro J hJ
        exact isZero_of_ideal_eq_bot J (by simpa only [pow_zero, one_mul] using hJ) C c 1
    | succ n ih =>
        intro J hJ
        apply isZero_first_of_mul X.nilradical J C c
        exact ih (X.nilradical * J) (by simpa only [pow_succ, mul_assoc] using hJ)
  exact hind e I (by rw [he]; exact zero_mul I)

end DeJongAlterations.StableModificationBridge.NilradicalCechVanishing
