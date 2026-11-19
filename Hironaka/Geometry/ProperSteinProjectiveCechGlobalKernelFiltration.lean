/-
Copyright (c) 2026 Chris Birkbeck and the EnvelopeProperty contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hironaka.Geometry.ProperSteinProjectiveCechInfinitesimalH0
import Hironaka.Geometry.ProperSteinProjectiveCechReesFixedTarget
import Hironaka.Geometry.ProperSteinProjectiveCechStableFiltration

/-! # The actual original whole global projection-kernel filtration

Only closed native stable-filtration transport is adapted from
`EnvelopeProperty/EnvelopeProperty/Global/FibreGlobalKernelFiltration.lean`,
SHA256 c65ecf7dda3b858b6030b8b6ad0965b75a4ac88d59014374971ad6ccd9474578.
The original subset H0, global section and projection triangles are derived
for the SAME own original scheme and coefficient action. No kernel, stability,
finite-section or reconstruction output is assumed.
-/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.GlobalKernelFiltration
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private def mapFiltration {A M N : Type u} [CommRing A] [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N] (I : Ideal A)
    (F : I.Filtration M) (e : M →ₗ[A] N) : I.Filtration N where
  N n := (F.N n).map e
  mono n := Submodule.map_mono (F.mono n)
  smul_le n := by
    rw [← Submodule.map_smul'' I (F.N n) e]
    exact Submodule.map_mono (F.smul_le n)

private theorem mapFiltration_stable {A M N : Type u} [CommRing A] [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N] (I : Ideal A)
    (F : I.Filtration M) (e : M →ₗ[A] N) (hF : F.Stable) :
    (mapFiltration I F e).Stable := by
  obtain ⟨c, hc⟩ := hF
  refine ⟨c, fun n hn => ?_⟩
  change I • (F.N n).map e=(F.N (n+1)).map e
  rw [← Submodule.map_smul'' I (F.N n) e, hc n hn]

section OriginalFamily
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  [X.IsSeparated] {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U=⊤)

/-- The actual first original native H0 map, followed by inverse original sheaf gluing. -/
def globalInclusion (d : ℕ) :
    (ReesPowerDiagram.powerComplex I f U d).homology 0 ⟶
      actualSchemeModuleBaseGlobalSections (SheafOfModules.unit X.ringCatSheaf)
        (ProperGeometricGlobalFunctions.coefficientMap f) :=
  HomologicalComplex.homologyMap (InfinitesimalSequence.sequence I f U hU d).f 0 ≫
    (actualSchemeModuleBaseGlobalHomologyIso (SheafOfModules.unit X.ringCatSheaf) U
      (ProperGeometricGlobalFunctions.coefficientMap f) hcover).inv

/-- The ENTIRE original zeroth-power inclusion square retains the SAME actual global function. -/
theorem inclusionHomology_square (d : ℕ) :
    ReesDegreeTransitions.homologyLower I f U (Nat.zero_le d) 0 ≫
        (ReesPowerZeroSections.globalHomologyIso I f U hcover).inv =
      globalInclusion I f U hU hcover d := by
  let C := actualSubsetCechFunctor (K := R) (I := ι)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0
  have hc : ReesDegreeTransitions.degreeLower I f U (Nat.zero_le d) ≫
      (ReesPowerZeroSections.complexIso I f U).inv =
        (InfinitesimalSequence.sequence I f U hU d).f :=
    (C.map_comp (ReesDegreeTransitions.lowerNatural I f U (Nat.zero_le d))
      (ReesPowerZeroSections.diagramIso I f U).inv).symm
  change H.map (ReesDegreeTransitions.degreeLower I f U (Nat.zero_le d)) ≫
      (H.map (ReesPowerZeroSections.complexIso I f U).inv ≫
        (actualSchemeModuleBaseGlobalHomologyIso (SheafOfModules.unit X.ringCatSheaf) U
          (ProperGeometricGlobalFunctions.coefficientMap f) hcover).inv) =
    H.map (InfinitesimalSequence.sequence I f U hU d).f ≫ _
  rw [← Category.assoc, ← H.map_comp, hc]

/-- Genuine native exactness identifies WHOLE original power-H0 images with actual full global projection kernels. -/
theorem globalInclusion_exact (d : ℕ) :
    Function.Exact (globalInclusion I f U hU hcover d) (InfinitesimalH0.projectionGlobal I f d) := by
  let e := actualSchemeModuleBaseGlobalHomologyIso (SheafOfModules.unit X.ringCatSheaf) U
    (ProperGeometricGlobalFunctions.coefficientMap f) hcover
  let ed := InfinitesimalH0.modelGlobalHomologyIso I f U hU hcover d
  let a := HomologicalComplex.homologyMap (InfinitesimalSequence.sequence I f U hU d).f 0
  let b := HomologicalComplex.homologyMap (InfinitesimalSequence.sequence I f U hU d).g 0
  have hex : Function.Exact a b := InfinitesimalSequence.homology_exact_middle I f U hU d 0
  intro s
  constructor
  · intro hs
    have he := congrArg (fun v => v.hom s) (InfinitesimalH0.projectionHomology_square I f U hU hcover d)
    change ed.hom ((InfinitesimalH0.projectionGlobal I f d).hom s)=b.hom (e.hom s) at he
    have hz : b.hom (e.hom s)=0 := he.symm.trans (by rw [hs, map_zero])
    obtain ⟨y, hy⟩ := (hex (e.hom s)).mp hz
    refine ⟨y, ?_⟩
    change e.inv (a.hom y)=s
    exact (congrArg e.inv hy).trans (e.toLinearEquiv.symm_apply_apply s)
  · rintro ⟨y, rfl⟩
    apply ed.toLinearEquiv.injective
    have he := congrArg (fun v => v.hom ((globalInclusion I f U hU hcover d).hom y))
      (InfinitesimalH0.projectionHomology_square I f U hU hcover d)
    change ed.hom ((InfinitesimalH0.projectionGlobal I f d).hom
      ((globalInclusion I f U hU hcover d).hom y))=
      b.hom (e.hom (e.inv (a.hom y))) at he
    exact he.trans ((congrArg b.hom (e.toLinearEquiv.apply_symm_apply (a.hom y))).trans
      (((hex (a.hom y)).mpr ⟨y, rfl⟩).trans (map_zero ed.hom.hom).symm))

/-- The original actual Rees image filtration transported to SAME whole original global sections. -/
def filtration : I.Filtration
    (actualSchemeModuleBaseGlobalSections (SheafOfModules.unit X.ringCatSheaf)
      (ProperGeometricGlobalFunctions.coefficientMap f)) :=
  mapFiltration I (ReesFixedTarget.imageFiltration I f U 0 0)
    (ReesPowerZeroSections.globalHomologyIso I f U hcover).inv.hom

include hU

/-- EVERY transported term is EXACTLY the ENTIRE original projection kernel, with no finite-level global-surjectivity claim. -/
theorem filtration_eq_kernel (d : ℕ) :
    (filtration I f U hcover).N d=LinearMap.ker (InfinitesimalH0.projectionGlobal I f d).hom := by
  ext s
  change s ∈ ((ReesFixedTarget.imageFiltration I f U 0 0).N d).map
    (ReesPowerZeroSections.globalHomologyIso I f U hcover).inv.hom ↔ _
  simp only [ReesFixedTarget.imageFiltration, Nat.zero_add]
  change s ∈ (LinearMap.range (ReesDegreeTransitions.homologyLower I f U (Nat.zero_le d) 0).hom).map
      (ReesPowerZeroSections.globalHomologyIso I f U hcover).inv.hom ↔
    (InfinitesimalH0.projectionGlobal I f d).hom s=0
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    have he := congrArg (fun v => v.hom y) (inclusionHomology_square I f U hU hcover d)
    apply (globalInclusion_exact I f U hU hcover d _).mpr
    exact ⟨y, he.symm⟩
  · intro hs
    obtain ⟨y, hy⟩ := (globalInclusion_exact I f U hU hcover d s).mp hs
    refine ⟨(ReesDegreeTransitions.homologyLower I f U (Nat.zero_le d) 0).hom y, ⟨y, rfl⟩, ?_⟩
    exact (congrArg (fun v => v.hom y) (inclusionHomology_square I f U hU hcover d)).trans hy

/-- Membership retains the SAME literal original scheme projection on EVERY whole original global section. -/
theorem mem_filtration (d : ℕ) (s : Γ(X, ⊤)) :
    s ∈ (filtration I f U hcover).N d ↔ (Infinitesimal.projection I f d).appTop s=0 := by
  rw [filtration_eq_kernel I f U hU hcover]
  rfl

omit hU [X.IsSeparated] in
/-- The genuine original global kernel filtration starts at the WHOLE original global-section module. -/
theorem filtration_zero : (filtration I f U hcover).N 0=⊤ := by
  change ((ReesFixedTarget.imageFiltration I f U 0 0).N 0).map
    (ReesPowerZeroSections.globalHomologyIso I f U hcover).inv.hom=⊤
  rw [ReesFixedTarget.imageFiltration_zero, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (ReesPowerZeroSections.globalHomologyIso I f U hcover).toLinearEquiv.symm.surjective

end OriginalFamily

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} {r : ℕ} (i : X ⟶ projectiveSpace R r) [IsClosedImmersion i]

/-- ORIGINAL closed projective geometry retains precisely EVERY full original global projection kernel. -/
theorem projective_mem_filtration (d : ℕ) (s : Γ(X, ⊤)) :
    s ∈ (filtration I (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i)
      (originalClosedCoordinateOpens_covers i)).N d ↔
      (Infinitesimal.projection I (i ≫ projectiveSpaceStructure R r) d).appTop s=0 := by
  let := ReesDegreeHomology.projectiveSeparated i
  exact mem_filtration I (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i)
    (originalClosedCoordinateOpens_isAffine i) (originalClosedCoordinateOpens_covers i) d s

include I in
/-- ORIGINAL projective Noetherian data DERIVE finite the SAME whole original global-section module. -/
theorem projective_globalSections_finite [IsNoetherianRing R] :
    Module.Finite R (actualSchemeModuleBaseGlobalSections (SheafOfModules.unit X.ringCatSheaf)
      (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure R r))) := by
  let : Module.Finite R ((ReesPowerDiagram.powerComplex I (i ≫ projectiveSpaceStructure R r)
    (originalClosedCoordinateOpens i) 0).homology 0) :=
      ReesPowerCohomologyFinite.projective_powerCech_finite I i 0 0
  exact Module.Finite.equiv (ReesPowerZeroSections.globalHomologyIso I
    (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i)
      (originalClosedCoordinateOpens_covers i)).toLinearEquiv.symm

/-- Actual original projective Rees finiteness DERIVES stability of ENTIRE original global projection kernels. -/
theorem projective_filtration_stable [IsNoetherianRing R] :
    (filtration I (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i)
      (originalClosedCoordinateOpens_covers i)).Stable :=
  mapFiltration_stable I (ReesFixedTarget.imageFiltration I (i ≫ projectiveSpaceStructure R r)
    (originalClosedCoordinateOpens i) 0 0)
    (ReesPowerZeroSections.globalHomologyIso I (i ≫ projectiveSpaceStructure R r)
      (originalClosedCoordinateOpens i) (originalClosedCoordinateOpens_covers i)).inv.hom
    (ReesFixedTarget.projective_imageFiltration_stable I i 0 0)

/-- Complete ORIGINAL projective Noetherian geometry reconstructs SAME global sections from actual whole projection-kernel quotients. -/
def projective_quotientReconstruction [IsNoetherianRing R] [IsAdicComplete I R] :
    actualSchemeModuleBaseGlobalSections (SheafOfModules.unit X.ringCatSheaf)
      (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure R r)) ≃ₗ[R]
      StableFiltration.compatibleQuotients I
        (filtration I (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i)
          (originalClosedCoordinateOpens_covers i)) := by
  let : Module.Finite R (actualSchemeModuleBaseGlobalSections (SheafOfModules.unit X.ringCatSheaf)
    (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure R r))) :=
      projective_globalSections_finite I i
  exact StableFiltration.reconstructionEquiv I
    (filtration I (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i)
      (originalClosedCoordinateOpens_covers i)) (projective_filtration_stable I i)
    (filtration_zero I (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i)
      (originalClosedCoordinateOpens_covers i))

/-- EVERY reconstructed coordinate is the literal original quotient of the SAME original global function. -/
theorem projective_quotientReconstruction_apply [IsNoetherianRing R] [IsAdicComplete I R]
    (s : Γ(X, ⊤)) (n : ℕ) :
    (projective_quotientReconstruction I i s).val n =
      ((filtration I (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i)
        (originalClosedCoordinateOpens_covers i)).N (n+1)).mkQ s := rfl

end Hironaka.Geometry.ProperSteinProjectiveCech.GlobalKernelFiltration
