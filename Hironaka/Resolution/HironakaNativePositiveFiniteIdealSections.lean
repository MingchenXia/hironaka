import Hironaka.Resolution.HironakaNativeFiniteIdealSections

/-! An ACTUAL zero module section makes the finite ideal family positive,
without density, nonzero-germ or injectivity hypotheses. ENTIRE all-point
original native b-stalk images stay exactly the SAME. Blueprint FIRST:
`hironaka-native-positive-finite-ideal-sections.tex`. -/

noncomputable section
set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace Set AlgebraicGeometry

namespace Hironaka.HironakaNativePositiveFiniteIdealSections

open HironakaSingularModuleSheafStalk HironakaNativeFiniteIdealSections

private theorem ideal_span_fin_cases_zero {R : Type*} [CommRing R] {r : ℕ}
    (v : Fin r → R) :
    Ideal.span (Set.range (Fin.cases (0 : R) v))=Ideal.span (Set.range v) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Ideal.zero_mem _
    · exact Ideal.subset_span ⟨j,rfl⟩
  · apply Ideal.span_le.mpr
    rintro a ⟨i,rfl⟩
    exact Ideal.subset_span ⟨i.succ,rfl⟩

variable {X : LocallyRingedSpace.{0}}
  (B : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf))

/-- ONLY ordinary native finite type and b produce a POSITIVE actual section
family on ONE original open, preserving the ENTIRE b-image at ALL nearby points.
The actual zero ideal/module case is included; no density or Mono b is used. -/
theorem exists_positive_finite_ideal_sections [B.IsFiniteType] (x : X) :
    ∃ (U : Opens X.toTopCat) (_hx : x ∈ U) (r : ℕ) (_hr : 0<r)
      (s : Fin r → B.val.obj (op U)),
      ∀ (y : X) (hy : y ∈ U),
        LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b y) =
          Ideal.span (Set.range fun i => X.presheaf.germ U y hy (b.val.app (op U) (s i))) := by
  obtain ⟨U,hx,r,s,_hep,hspan⟩ := exists_finite_ideal_sections B b x
  let s' : Fin (r+1) → B.val.obj (op U) := Fin.cases 0 s
  refine ⟨U,hx,r+1,Nat.succ_pos r,s',?_⟩
  intro y hy
  have hvec : (fun i : Fin (r+1) => X.presheaf.germ U y hy (b.val.app (op U) (s' i))) =
      Fin.cases 0 (fun i : Fin r => X.presheaf.germ U y hy (b.val.app (op U) (s i))) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [s',Fin.cases_zero,map_zero]
      change (X.presheaf.germ U y hy).hom 0=0
      exact map_zero _
    · rfl
  rw [hvec,ideal_span_fin_cases_zero]
  exact hspan y hy

end Hironaka.HironakaNativePositiveFiniteIdealSections
