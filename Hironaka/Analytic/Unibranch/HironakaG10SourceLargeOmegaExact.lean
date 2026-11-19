import Hironaka.Analytic.Unibranch.HironakaG10NativeNullstellensatz
import Hironaka.Analytic.Unibranch.HironakaG10BoundarySupportContainment
import Hironaka.Analytic.Unibranch.HironakaG10LargeOmegaAgreement

/-! # Large-exponent agreement for Hironaka's actual source components -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaExact
open Hironaka HironakaG10HirIdealGerms
  HironakaG10FiniteIdealFamilyArithmetic HironakaSingularModuleSheafStalk
  HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
  Hironaka.Analytic.Unibranch.HironakaG10LocalIntrinsicIdeal
  Hironaka.Analytic.Unibranch.HironakaG10SchemeBoundaryThickening
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCSet
  Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCoincidence
  Hironaka.Analytic.Unibranch.HironakaG10BoundarySupportContainment
  Hironaka.Analytic.Unibranch.HironakaG10LargeOmegaAgreement
  Hironaka.Analytic.Unibranch.HironakaG10UniformRadicalPower
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- Source 4.5.2's large-exponent conclusion on a compact subset of the
  actual tracked boundaries: no stalk radical-containment premise is used. -/
theorem exists_source_large_omega_exact {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    {q : ℕ} (Z : Fin q → LocalFlattener f) (Zaux : LocalFlattener f) (i : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn X (Z p).V (strata f B (i + 1)))
    (hSaux : IsLocallyAnalyticOn X Zaux.V (strata f B (i + 1)))
    (N : ℕ) (hN : strata f B N = ∅)
    (hcover : ∀ j x, x ∈ strata f B j → ∃ C, IsStratumComponent f B j C ∧ x ∈ C)
    (hfinite : (selectedHigherComponents f B (fun p => (Z p).support) (i + 1)).Finite)
    (hmax : ∀ jC ∈ badComponents f B (fun p => (Z p).support), jC.1 ≤ i + 1)
    (hC : Cset f B (fun p => (Z p).support) (i + 1) ⊆ Zaux.support)
    (K : Set X.obj.left) (hK : IsCompact K)
    (hKtracked : ∀ x ∈ K, ∃ p, x ∈ stratumBoundary f B (Z p).V (Z p).support i) :
    let C := Cset f B (fun p => (Z p).support) (i + 1)
    ∃ (W : Set X.obj.left) (ω₀ : ℕ), IsOpen W ∧ K ⊆ W ∧ W ⊆ Zaux.V ∧
      ∀ ω ≥ ω₀, ∃ (D : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
        (d : D ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
        D.IsFiniteType ∧ nonunitLocus D d = C ∩ stratumBoundary f B Zaux.V Zaux.support i ∧
        (∀ x ∈ Zaux.V, LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) =
          (intrinsicCentreStalkRange X.obj.left C x) ^ ω ⊔
            (intrinsicCentreStalkRange X.obj.left
              (closure ((strata f B (i + 1) ∩ Zaux.V) \ Zaux.support)) x ⊔ Zaux.H x)) ∧
        (∀ x ∈ W, LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) =
            intrinsicCentreStalkRange X.obj.left
              (closure ((strata f B (i + 1) ∩ Zaux.V) \ Zaux.support)) x ⊔ Zaux.H x) ∧
        ∀ p x, x ∈ K → x ∈ stratumBoundary f B (Z p).V (Z p).support i →
          ∀ᶠ y in 𝓝 x, LinearMap.range
            (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d y) =
              intrinsicCentreStalkRange X.obj.left
                (closure ((strata f B (i + 1) ∩ (Z p).V) \ (Z p).support)) y ⊔ (Z p).H y := by
  let C := Cset f B (fun p => (Z p).support) (i + 1)
  let G := closure ((strata f B (i + 1) ∩ Zaux.V) \ Zaux.support)
  let IE := fun x => intrinsicCentreStalkRange X.obj.left G x ⊔ Zaux.H x
  obtain ⟨hCa,hCc,_,_⟩ := Cset_closed_relOpen_and_nonflat f B (fun p => (Z p).support)
    (i + 1) hfinite hmax
  have hCV : C ⊆ Zaux.V := fun x hx => (hC hx).1
  have hKV : K ⊆ Zaux.V := by
    intro x hx
    obtain ⟨p,hxp⟩ := hKtracked x hx
    exact hCV (tracked_boundary_subset_cset f B Z i hS N hN hcover p hxp)
  have hG : IsLocallyAnalyticOn X Zaux.V G := closure_locallyAnalytic f B Zaux i hSaux
  have hIE : IsLocallyFinitelyGeneratedOn X.obj.left Zaux.V IE :=
    isLocallyFinitelyGeneratedOn_sup Zaux.V _ _
      (local_intrinsicCentreStalkRange_finitelyGenerated X Zaux.V G hG) Zaux.fg
  have hrad : ∀ x ∈ K, intrinsicCentreStalkRange X.obj.left C x ≤ (IE x).radical := by
    intro x hx
    obtain ⟨p,hxp⟩ := hKtracked x hx
    apply Hironaka.Analytic.Unibranch.HironakaG10NativeNullstellensatz.intrinsicCentre_le_radical_of_support_subset
      Zaux.V C Zaux.isOpen IE hIE x (hKV hx)
    exact eventually_auxBoundary_support_subset_cset f B Z Zaux i hS N hN hcover hC p x hxp
  let IC := intrinsicCentreStalkRange X.obj.left C
  have hClocal : IsLocallyAnalyticOn X Zaux.V C := locallyAnalytic_of_analytic hCa Zaux.V
  have hIC : IsLocallyFinitelyGeneratedOn X.obj.left Zaux.V IC :=
    local_intrinsicCentreStalkRange_finitelyGenerated X Zaux.V C hClocal
  obtain ⟨W,N₀,hW,hKW,hWV,hpower⟩ :=
    exists_uniform_power_on_compact Zaux.V K Zaux.isOpen hK hKV IC IE hIC hIE hrad
  refine ⟨W,max N₀ 1,hW,hKW,hWV,fun ω hω => ?_⟩
  have hωN : N₀ ≤ ω := (le_max_left N₀ 1).trans hω
  have hω0 : ω ≠ 0 := Nat.ne_of_gt
    (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N₀ 1).trans hω))
  obtain ⟨D,d,hfin,hQ,hsource,_⟩ :=
    exists_scheme_boundary_thickening f B C Zaux i ω hω0 hSaux hClocal hCc hCV
  have hstalk : ∀ x ∈ W, LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) = IE x := by
    intro x hx
    rw [hsource x (hWV hx)]
    exact sup_eq_right.mpr (hpower x hx ω hωN)
  refine ⟨D,d,hfin,hQ,hsource,hstalk,fun p x hxK hxE => ?_⟩
  have hEq := tracked_boundary_scheme_agrees f B Z Zaux i hS N hN hcover hC p x hxE
  filter_upwards [hW.mem_nhds (hKW hxK),hEq] with y hyW hyEq
  exact (hstalk y hyW).trans hyEq

end
end Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaExact
