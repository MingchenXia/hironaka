import Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
import Hironaka.Analytic.Unibranch.HironakaG10RdRelativeStep
import Hironaka.Analytic.Unibranch.HironakaG10GeometricSumCentreSeparation

/-!
# Hironaka's Lemma 4.5.4: tracked supports become relatively open in the strict transform (lane G10RD)

Plan item G10-03-07.b (and the `i = 0` half of the `D_β` step L4).  Source: H. Hironaka, *Flattening theorem in
complex-analytic geometry*, Amer. J. Math. 97 (1975), Lemma 4.5.4 and its proof, printed pp. 542–543: "Pick any
y' ∈ Z_p^* ∩ π^{-1}(D_β) … Hence (I_{G_{ip}} + I_{Z_p}) O_{Y',y'} is invertible … the strict transforms of G_{ip} and
Z_p by π do not have any common point in some neighborhood of y' … The same is trivially true if
y' ∈ π^{-1}(D_β) − Z_p^* … E_{ip} contains all the points of s_i at which the intersection s_i ∩ Z_p is not
locally open in s_i … |E_{ip}| is contained in D_β."

* `isRelOpen_of_local` — relative openness is local;
* `not_geometric_and_onStrictTransform` — at a point over a sum centre with stalk `(I_G + H)^β + H`, `β > 0`, the
  GEOMETRIC strict transform of `G` and the ALGEBRAIC strict transform of the flattener `H` do not meet;
* **`isRelOpen_strictSet_of_sumCentre`** — Lemma 4.5.4: if the boundary `E = closure((S ∩ V) ∖ |Z|) ∩ |Z|` lies in
  the centre and the centre stalk is `(I_G + H)^β + H` at the centre points of `|Z|`, then the transported support
  `|Z'|` (germ-level transport, Lemma 4.4.5) meets the strict transform of `S` in a relatively open set.  With
  `S = B` (Hironaka's index `0`) this is `OpenTracked` of the next datum.

No named input is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10RdLemma454

open Hironaka HironakaSingularModuleSheafStalk HironakaIntrinsicReducedCentreOpenPullback
  HironakaG10CoherentSupportIdeal
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10GeometricStrictMembership
  Hironaka.Analytic.Unibranch.HironakaG10NativeSumCentreSeparation
  Hironaka.Analytic.Unibranch.HironakaG10StrictSourceThickening
  Hironaka.Analytic.Unibranch.HironakaG10GeometricSumCentreSeparation
  Hironaka.Analytic.Unibranch.HironakaG10HirFlattenerGluing
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10RdRelativeStep
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- **Relative openness is local.** -/
theorem isRelOpen_of_local {α : Type*} [TopologicalSpace α] {A T : Set α}
    (h : ∀ y ∈ A ∩ T, ∃ U : Set α, IsOpen U ∧ y ∈ U ∧ A ∩ U ⊆ T) : IsRelOpen A T := by
  choose! U hU hyU hAU using h
  refine ⟨⋃ y ∈ A ∩ T, U y, isOpen_biUnion fun y hy => hU y hy, ?_⟩
  ext x
  constructor
  · rintro ⟨hxA, hxT⟩
    exact ⟨hxA, mem_biUnion ⟨hxA, hxT⟩ (hyU x ⟨hxA, hxT⟩)⟩
  · rintro ⟨hxA, hx⟩
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
    exact ⟨hxA, hAU y hy ⟨hxA, hxy⟩⟩

section Separation

variable {X Y : SourceReducedComplexSpace} {f : Y ⟶ X}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (hDense : Dense {x : X.obj.left |
    LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})

/-- **A geometric strict transform of `G` misses the algebraic strict transform of the flattener** over a
sum centre with stalk `(I_G + H)^β + H`, `β > 0` (Hironaka p. 542). -/
theorem not_geometric_and_onStrictTransform (Z : LocalFlattener f) (G : Set X.obj.left) (β : ℕ)
    (hβ : β ≠ 0) (x' : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left)
    (hStalk : LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
        ((stepProj B b hDense).hom.left.base x')) =
      (intrinsicCentreStalkRange X.obj.left G
        ((stepProj B b hDense).hom.left.base x') ⊔
        Z.H ((stepProj B b hDense).hom.left.base x')) ^ β ⊔
          Z.H ((stepProj B b hDense).hom.left.base x'))
    (hG : x' ∈ closure ((stepProj B b hDense).hom.left.base ⁻¹' (G \ nonunitLocus B b)))
    (hZ : OnStrictTransform (stepProj B b hDense) x' (Z.H ((stepProj B b hDense).hom.left.base x'))
      (LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
        ((stepProj B b hDense).hom.left.base x')) :)) : False := by
  let x := (stepProj B b hDense).hom.left.base x'
  let I := intrinsicCentreStalkRange X.obj.left G x
  let H := Z.H x
  have hD : LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = I ^ β ⊔ H :=
    hStalk.trans (pow_sup_absorb I H β)
  obtain ⟨_, _, _, _, hGI⟩ :=
    exists_equation_and_onStrictTransform_of_mem_closure B b hDense G x' hG I le_rfl
  rw [hD] at hGI hZ
  exact not_both_on_strictTransform B b hDense x' (I ^ β) H hD
    ⟨(onStrictTransform_source_pow_iff (stepProj B b hDense) x' I (I ^ β ⊔ H) hβ).mpr hGI, hZ⟩

end Separation

/-- A point of the closure of the support of a local flattener inside its domain is in the support. -/
theorem mem_support_of_mem_closure {X Y : SourceReducedComplexSpace} {f : Y ⟶ X}
    (Z : LocalFlattener f) {y : X.obj.left} (hyV : y ∈ Z.V) (hy : y ∈ closure Z.support) :
    y ∈ Z.support := by
  refine ⟨hyV, fun htop => ?_⟩
  obtain ⟨z, hz, hzZ⟩ := mem_closure_iff.mp hy _ Z.isOpen_inter_eq_top ⟨hyV, htop⟩
  exact hzZ.2 hz.2

/-- **Hironaka's Lemma 4.5.4** (pp. 542–543), for one tracked flattener `Z` and a closed set `S` (the stratum
`s_i`): if the boundary `closure((S ∩ V) ∖ |Z|) ∩ |Z|` lies in the centre, and at every centre point of `|Z|` the
centre stalk is `(I_G + H)^β + H` with `G = closure((S ∩ V) ∖ |Z|)`, `β > 0`, then the transported support `|Z'|`
(the germ-level transport of `|Z|`) meets the strict transform of `S` in a relatively open set. -/
theorem isRelOpen_strictSet_of_sumCentre (s : Stage) (c : AdmissibleCentre s.f) (Z : LocalFlattener s.f)
    {S : Set s.X.obj.left} (hS : IsClosed S) (β : ℕ) (hβ : β ≠ 0)
    (hE : closure ((S ∩ Z.V) \ Z.support) ∩ Z.support ⊆ nonunitLocus c.B c.b)
    (hagree : ∀ y ∈ nonunitLocus c.B c.b, y ∈ Z.support → centreIdeal c y =
      (intrinsicCentreStalkRange s.X.obj.left (closure ((S ∩ Z.V) \ Z.support)) y ⊔ Z.H y) ^ β ⊔
        Z.H y)
    (Z' : LocalFlattener (nextWith s c).f)
    (hZ' : ∀ x', x' ∈ Z'.support ↔ ((stepσ s c).hom.left.base x' ∈ Z.support ∧
      OnStrictTransform (stepσ s c) x' (germFlattener s.f ((stepσ s c).hom.left.base x'))
        (centreIdeal c ((stepσ s c).hom.left.base x')))) :
    IsRelOpen (strictSet s c S) Z'.support := by
  let _ := c.finiteType
  set G := closure ((S ∩ Z.V) \ Z.support) with hGdef
  have hcont : Continuous (stepσ s c).hom.left.base := (stepσ s c).hom.left.base.hom.continuous
  have hEc : IsClosed ((stepσ s c).hom.left.base ⁻¹' nonunitLocus c.B c.b) :=
    isClosed_stepExcep c.B c.b c.dense
  have hA : strictSet s c S ⊆ (stepσ s c).hom.left.base ⁻¹' S := strictSet_subset_preimage s c hS
  -- transport off the centre
  have hoff : ∀ x', (stepσ s c).hom.left.base x' ∈ Z.support →
      (stepσ s c).hom.left.base x' ∉ nonunitLocus c.B c.b → x' ∈ Z'.support := by
    intro x' h1 h2
    refine (hZ' x').mpr ⟨h1, ?_⟩
    exact (mem_transport_of_not_mem_nonunitLocus c.B c.b c.dense s.f
      (trackedDatumOfLocalFlatteners (fun _ : Fin 1 => Z)) (0 : Fin 1) x' h1 h2).2
  -- points over `S ∩ V` off the centre and off `|Z|` lie over `G`
  have hG : ∀ x', (stepσ s c).hom.left.base x' ∈ S → (stepσ s c).hom.left.base x' ∈ Z.V →
      (stepσ s c).hom.left.base x' ∉ Z.support →
        (stepσ s c).hom.left.base x' ∈ G := fun x' h1 h2 h3 => subset_closure ⟨⟨h1, h2⟩, h3⟩
  refine isRelOpen_of_local fun y' ⟨hy'A, hy'Z⟩ => ?_
  obtain ⟨hyZ, hyStr⟩ := (hZ' y').mp hy'Z
  by_cases hyD : (stepσ s c).hom.left.base y' ∈ nonunitLocus c.B c.b
  · -- over the centre: separation at `y'`
    have hsep : y' ∉ closure ((stepσ s c).hom.left.base ⁻¹' (G \ nonunitLocus c.B c.b)) := by
      intro hmem
      refine not_geometric_and_onStrictTransform c.B c.b c.dense Z G β hβ y'
        (hagree _ hyD hyZ) hmem ?_
      rw [← Z.H_eq_germFlattener hyZ] at hyStr
      exact hyStr
    refine ⟨(closure ((stepσ s c).hom.left.base ⁻¹' (G \ nonunitLocus c.B c.b)))ᶜ ∩
      (stepσ s c).hom.left.base ⁻¹' Z.V, isClosed_closure.isOpen_compl.inter
        (Z.isOpen.preimage hcont), ⟨hsep, hyZ.1⟩, ?_⟩
    rintro x' ⟨hx'A, hx'U, hx'V⟩
    have hx'S := hA hx'A
    by_cases hxD : (stepσ s c).hom.left.base x' ∈ nonunitLocus c.B c.b
    · -- `x'` over the centre: it is on the geometric strict transform of `|Z|`
      have hcl : x' ∈ closure ((stepσ s c).hom.left.base ⁻¹' (Z.support \ nonunitLocus c.B c.b)) := by
        rw [mem_closure_iff]
        intro o ho hx'o
        obtain ⟨w, ⟨hwo, hwU, hwV⟩, hwS⟩ := mem_closure_iff.mp hx'A _
          (ho.inter (isClosed_closure.isOpen_compl.inter (Z.isOpen.preimage hcont)))
          ⟨hx'o, hx'U, hx'V⟩
        refine ⟨w, hwo, ?_, hwS.2⟩
        by_contra hwZ
        exact hwU (subset_closure ⟨hG w hwS.1 hwV hwZ, hwS.2⟩)
      have hσZ : (stepσ s c).hom.left.base x' ∈ Z.support := by
        exact mem_support_of_mem_closure Z hx'V (map_mem_closure hcont hcl fun w hw => hw.1)
      refine (hZ' x').mpr ⟨hσZ, ?_⟩
      obtain ⟨_, _, _, _, hon⟩ := exists_equation_and_onStrictTransform_of_mem_closure c.B c.b c.dense
        Z.support x' hcl (Z.H _) (le_intrinsicCentreStalkRange_support s.X.obj.left Z.V Z.H Z.fg _ hx'V)
      rw [← Z.H_eq_germFlattener hσZ]
      exact hon
    · by_contra hx'Z
      have hσZ : (stepσ s c).hom.left.base x' ∉ Z.support := fun h => hx'Z (hoff x' h hxD)
      exact hx'U (subset_closure ⟨hG x' hx'S hx'V hσZ, hxD⟩)
  · -- off the centre
    have hyG : (stepσ s c).hom.left.base y' ∉ G := fun h => hyD (hE ⟨h, hyZ⟩)
    refine ⟨(stepσ s c).hom.left.base ⁻¹' (Gᶜ ∩ Z.V) ∩
      ((stepσ s c).hom.left.base ⁻¹' nonunitLocus c.B c.b)ᶜ,
      ((isClosed_closure.isOpen_compl.inter Z.isOpen).preimage hcont).inter hEc.isOpen_compl,
      ⟨⟨hyG, hyZ.1⟩, hyD⟩, ?_⟩
    rintro x' ⟨hx'A, ⟨hx'G, hx'V⟩, hx'D⟩
    by_contra hx'Z
    have hσZ : (stepσ s c).hom.left.base x' ∉ Z.support := fun h => hx'Z (hoff x' h hx'D)
    exact hx'G (hG x' (hA hx'A) hx'V hσZ)

end

end Hironaka.Analytic.Unibranch.HironakaG10RdLemma454
