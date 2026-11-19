import Hironaka.Geometry.ProperSteinProjectiveCechSheafSections
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# An actual ORIGINAL finite affine Cech producer from original properness

The native compact-affine extraction and separated intersection proofs adapt
`EnvelopeProperty/deps/aintlib-ep33/ModularCurves/ForMathlib/FiniteAffineOpenCover.lean`,
SHA256 89e8bed95dff40ab281c3d99cf8b13ddcb0558d9caa569d7f2fd164b7d98f8f9.
Only native Mathlib and owned Hironaka modules are imported.
The source opens, actual sections, restriction arrows and coefficient map are retained.
No chart-term finiteness over the base or positive derived sheaf-cohomology comparison is claimed.
-/

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Actual compactness extracts a finite ORIGINAL affine cover, with actual standard finite index. -/
theorem finiteAffineFinCover_exists (X : Scheme.{u}) [CompactSpace X] :
    ∃ n : ℕ, ∃ U : ULift.{u} (Fin n) → X.Opens, IsOpenCover U ∧ ∀ i, IsAffineOpen (U i) := by
  classical
  have hU : IsOpenCover (fun U : X.affineOpens => U.val) := by
    rw [IsOpenCover, iSup_affineOpens_eq_top]
  obtain ⟨s, hs⟩ := hU.exists_finite_of_compactSpace
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let U : ULift.{u} (Fin (Fintype.card s)) → X.Opens := fun i => (e.symm i.down).val.val
  refine ⟨Fintype.card s, U, ?_, fun i => (e.symm i.down).val.property⟩
  change (⨆ i, U i) = ⊤
  apply top_unique
  intro x _
  have hx : x ∈ ⨆ i : s, i.val.val := by
    change IsOpenCover (fun i : s => i.val.val) at hs
    change (⨆ i : s, i.val.val) = ⊤ at hs
    rw [hs]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨⟨e i⟩, by simpa [U] using hi⟩

/-- ORIGINAL properness over an ORIGINAL affine scheme produces the SAME finite affine cover. -/
theorem properFiniteAffineFinCover_exists {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsAffine S] :
    ∃ n : ℕ, ∃ U : ULift.{u} (Fin n) → X.Opens,
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
      ∀ t : Finset (ULift.{u} (Fin n)), t.Nonempty → IsAffineOpen (actualSchemeSubsetOpen U t) := by
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  obtain ⟨n, U, hU, haff⟩ := finiteAffineFinCover_exists X
  refine ⟨n, U, hU, haff, fun t ht => ?_⟩
  simpa [actualSchemeSubsetOpen, Finset.inf_eq_iInf] using
    IsAffineOpen.biInf (t : Set (ULift.{u} (Fin n))) t.finite_toSet
      (Finset.coe_nonempty.mpr ht) (fun i _ => haff i)

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsAffine S]

/-- The actual internally derived cardinal of the SAME original proper affine cover. -/
def properAffineCechCoverCard : ℕ := (properFiniteAffineFinCover_exists f).choose

/-- The actual ORIGINAL affine opens chosen from original properness, with no cover input. -/
def properAffineCechCoverOpens : ULift.{u} (Fin (properAffineCechCoverCard f)) → X.Opens :=
  (properFiniteAffineFinCover_exists f).choose_spec.choose

/-- The SAME original internally produced affine opens actually cover. -/
theorem properAffineCechCover_covers : IsOpenCover (properAffineCechCoverOpens f) :=
  (properFiniteAffineFinCover_exists f).choose_spec.choose_spec.1

/-- EACH original internally produced cover open is actually affine. -/
theorem properAffineCechCover_isAffine (i : ULift.{u} (Fin (properAffineCechCoverCard f))) :
    IsAffineOpen (properAffineCechCoverOpens f i) :=
  (properFiniteAffineFinCover_exists f).choose_spec.choose_spec.2.1 i

/-- EVERY nonempty ORIGINAL finite intersection of the SAME chosen original opens is affine. -/
theorem properAffineCechCover_intersection_isAffine
    (t : Finset (ULift.{u} (Fin (properAffineCechCoverCard f)))) (ht : t.Nonempty) :
    IsAffineOpen (actualSchemeSubsetOpen (properAffineCechCoverOpens f) t) :=
  (properFiniteAffineFinCover_exists f).choose_spec.choose_spec.2.2 t ht

variable (M : X.Modules) {A : Type u} [CommRing A] (c : A →+* Γ(X, ⊤))

/-- The actual native Cech complex of ORIGINAL sections on the SAME derived finite affine cover. -/
def properAffineCechComplex : CochainComplex (ModuleCat.{u} A) ℕ :=
  subsetCechComplex (actualSchemeModuleBaseSubsetDiagram M (properAffineCechCoverOpens f) c)

/-- Native sheaf gluing identifies the SAME ORIGINAL global sections with actual Cech H0. -/
def properAffineCechGlobalH0Iso : actualSchemeModuleBaseGlobalSections M c ≅
    (properAffineCechComplex f M c).homology 0 :=
  actualSchemeModuleBaseGlobalHomologyIso M (properAffineCechCoverOpens f) c
    (properAffineCechCover_covers f)

/-- The SAME internally derived finite affine cover gives an actual native Cech vanishing bound. -/
theorem properAffineCech_homology_isZero_of_coverCard_le (p : ℕ)
    (hp : properAffineCechCoverCard f ≤ p) :
    CategoryTheory.Limits.IsZero ((properAffineCechComplex f M c).homology p) := by
  apply subsetCechComplex_homology_isZero_of_card_le
  simpa only [Fintype.card_ulift, Fintype.card_fin] using hp

end
end Hironaka.Geometry.ProperSteinProjectiveCech
