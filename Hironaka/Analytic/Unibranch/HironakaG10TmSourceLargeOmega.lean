import Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaCentre
import Hironaka.Analytic.Unibranch.HironakaG10TmUniformColon

/-!
# Large-ω sum centres with the tracked formula at EVERY tracked boundary point (lane G10TM)

Plan item G10-03-06.a, second part (lane G10RD's re-split, `G10RD/G10-03-03-sum-centre-globalization.md` §3):
the library theorems `HironakaG10SourceLargeOmegaExact.exists_source_large_omega_exact` and
`HironakaG10SourceLargeOmegaCentre.exists_source_large_omega_sumCentre` give the tracked-boundary formula of the
centre stalk (requirement G4 of Lemma 4.5.3 (2)) only near a chosen COMPACT set `K` of tracked boundary points.
Here `K` is removed: with the uniform colon power (`HironakaG10TmUniformColon.exists_uniform_colon_power`) on the
compact `C = Cset …` (which contains every tracked boundary point), ONE exponent `ω₀` makes
`I_C^ω ≤ I_{E}` near every tracked boundary point for all `ω ≥ ω₀` (Hironaka 1975, Lemma 4.5.3 (2), printed
p. 542).  The proofs are those of the library theorems with the compact uniform-power step replaced.

* `exists_source_large_omega_exact'`, `exists_source_large_omega_sumCentre'`.

No named input; the hypotheses are those of the library theorems minus `K`, `hK`, `hKtracked`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10TmSourceLargeOmega
open Hironaka HironakaG10HirIdealGerms
  HironakaSingularModuleSheafStalk HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
  Hironaka.Analytic.Unibranch.HironakaG10LocalBoundaryGlobalCut
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCSet
  Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaExact
  Hironaka.Analytic.Unibranch.HironakaG10FiniteIdealSumCentre
  Hironaka.Analytic.Unibranch.HironakaG10SourceIdentifiedSumCentre
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10SumCentreFlat
  Hironaka.Analytic.Unibranch.HironakaG10SourceFamilySeparation
  Hironaka.Analytic.Unibranch.HironakaG10SourceIdealSeparation
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

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


open Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaExact Hironaka.Analytic.Unibranch.HironakaG10TmUniformColon

noncomputable section

/-- Source 4.5.2's large-exponent conclusion at EVERY actual tracked boundary point (no compact set). -/
theorem exists_source_large_omega_exact' {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    {q : ℕ} (Z : Fin q → LocalFlattener f) (Zaux : LocalFlattener f) (i : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn X (Z p).V (strata f B (i + 1)))
    (hSaux : IsLocallyAnalyticOn X Zaux.V (strata f B (i + 1)))
    (N : ℕ) (hN : strata f B N = ∅)
    (hcover : ∀ j x, x ∈ strata f B j → ∃ C, IsStratumComponent f B j C ∧ x ∈ C)
    (hfinite : (selectedHigherComponents f B (fun p => (Z p).support) (i + 1)).Finite)
    (hmax : ∀ jC ∈ badComponents f B (fun p => (Z p).support), jC.1 ≤ i + 1)
    (hC : Cset f B (fun p => (Z p).support) (i + 1) ⊆ Zaux.support) :
    let C := Cset f B (fun p => (Z p).support) (i + 1)
    ∃ ω₀ : ℕ, ∀ ω ≥ ω₀, ∃ (D : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
        (d : D ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
        D.IsFiniteType ∧ nonunitLocus D d = C ∩ stratumBoundary f B Zaux.V Zaux.support i ∧
        (∀ x ∈ Zaux.V, LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) =
          (intrinsicCentreStalkRange X.obj.left C x) ^ ω ⊔
            (intrinsicCentreStalkRange X.obj.left
              (closure ((strata f B (i + 1) ∩ Zaux.V) \ Zaux.support)) x ⊔ Zaux.H x)) ∧
        ∀ p x, x ∈ stratumBoundary f B (Z p).V (Z p).support i →
          ∀ᶠ y in 𝓝 x, LinearMap.range
            (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d y) =
              intrinsicCentreStalkRange X.obj.left
                (closure ((strata f B (i + 1) ∩ (Z p).V) \ (Z p).support)) y ⊔ (Z p).H y := by
  let C := Cset f B (fun p => (Z p).support) (i + 1)
  let G := closure ((strata f B (i + 1) ∩ Zaux.V) \ Zaux.support)
  let IE := fun x => intrinsicCentreStalkRange X.obj.left G x ⊔ Zaux.H x
  obtain ⟨hCa, hCc, _, _⟩ := Cset_closed_relOpen_and_nonflat f B (fun p => (Z p).support)
    (i + 1) hfinite hmax
  have hCV : C ⊆ Zaux.V := fun x hx => (hC hx).1
  have hG : IsLocallyAnalyticOn X Zaux.V G := closure_locallyAnalytic f B Zaux i hSaux
  have hIE : IsLocallyFinitelyGeneratedOn X.obj.left Zaux.V IE :=
    isLocallyFinitelyGeneratedOn_sup Zaux.V _ _
      (local_intrinsicCentreStalkRange_finitelyGenerated X Zaux.V G hG) Zaux.fg
  let IC := intrinsicCentreStalkRange X.obj.left C
  have hClocal : IsLocallyAnalyticOn X Zaux.V C := locallyAnalytic_of_analytic hCa Zaux.V
  have hIC : IsLocallyFinitelyGeneratedOn X.obj.left Zaux.V IC :=
    local_intrinsicCentreStalkRange_finitelyGenerated X Zaux.V C hClocal
  obtain ⟨ω₁, hω₁⟩ := exists_uniform_colon_power Zaux.V Zaux.isOpen IC IE hIC hIE C
    hCc.isCompact hCV
  refine ⟨max ω₁ 1, fun ω hω => ?_⟩
  have hω0 : ω ≠ 0 := Nat.ne_of_gt
    (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right ω₁ 1).trans hω))
  obtain ⟨D, d, hfin, hQ, hsource, _⟩ :=
    exists_scheme_boundary_thickening f B C Zaux i ω hω0 hSaux hClocal hCc hCV
  refine ⟨D, d, hfin, hQ, hsource, fun p x hxE => ?_⟩
  have hxC : x ∈ C := tracked_boundary_subset_cset f B Z i hS N hN hcover p hxE
  have hxV : x ∈ Zaux.V := hCV hxC
  have hrad : IC x ≤ (IE x).radical :=
    Hironaka.Analytic.Unibranch.HironakaG10NativeNullstellensatz.intrinsicCentre_le_radical_of_support_subset
      Zaux.V C Zaux.isOpen IE hIE x hxV
      (eventually_auxBoundary_support_subset_cset f B Z Zaux i hS N hN hcover hC p x hxE)
  have hfgx : (IC x).FG := by
    obtain ⟨O, hxO, r, s, hs⟩ := hIC x hxV
    rw [hs x hxO hxV]
    exact Submodule.fg_span (Set.finite_range _)
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfgx
  have hev : ∀ᶠ z in 𝓝 x, IC z ^ m ≤ IE z :=
    eventually_le_of_le (isLocallyFinitelyGeneratedOn_pow Zaux.V IC hIC m) hIE
      Zaux.isOpen Zaux.isOpen hxV hxV hm
  have hpow := hω₁ x hxC ⟨m, hev⟩ ω ((le_max_left ω₁ 1).trans hω)
  have hEq := tracked_boundary_scheme_agrees f B Z Zaux i hS N hN hcover hC p x hxE
  filter_upwards [hpow, hEq, Zaux.isOpen.mem_nhds hxV] with y hy hyEq hyV
  rw [hsource y hyV]
  exact (sup_eq_right.mpr hy).trans hyEq

/-- **Admissible centre-flat sum centres with the tracked-boundary formula at every tracked boundary
point** (lane G10RD's `exists_source_large_omega_sumCentre'`, G10-03-06.a): the library theorem
`exists_source_large_omega_sumCentre` without the compact set `K`. -/
theorem exists_source_large_omega_sumCentre' {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    {q : ℕ} (Z : Fin q → LocalFlattener f) (Zaux : LocalFlattener f) (i : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn X (Z p).V (strata f B (i + 1)))
    (hSaux : IsLocallyAnalyticOn X Zaux.V (strata f B (i + 1)))
    (N : ℕ) (hN : strata f B N = ∅)
    (hcover : ∀ j x, x ∈ strata f B j → ∃ C, IsStratumComponent f B j C ∧ x ∈ C)
    (hfinite : (selectedHigherComponents f B (fun p => (Z p).support) (i + 1)).Finite)
    (hmax : ∀ jC ∈ badComponents f B (fun p => (Z p).support), jC.1 ≤ i + 1)
    (hC : Cset f B (fun p => (Z p).support) (i + 1) ⊆ Zaux.support)
    (hdense : Dense (nonflatImage f)ᶜ) :
    let C := Cset f B (fun p => (Z p).support) (i + 1)
    let Q := C ∩ stratumBoundary f B Zaux.V Zaux.support i
    ∃ ω₀ : ℕ, ∀ ω ≥ ω₀, ∃ (D : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
        (d : D ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
        D.IsFiniteType ∧ nonunitLocus D d = Q ∧
        (∀ x ∈ Zaux.V, LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) =
          (intrinsicCentreStalkRange X.obj.left C x) ^ ω ⊔
            (intrinsicCentreStalkRange X.obj.left
              (closure ((strata f B (i + 1) ∩ Zaux.V) \ Zaux.support)) x ⊔ Zaux.H x)) ∧
        ∃ α : ℕ, ∀ β : ℕ, α ≤ β → ∃ c : AdmissibleCentre f,
          nonunitLocus c.B c.b = Q ∧ IsSumCentreFor c.B c.b f β ∧
          (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt f x
            (LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf c.B c.b x))) ∧
          (β ≠ 0 → letI : c.B.IsFiniteType := c.finiteType
            ∀ x' : (OriginalFiniteIdealBlowup.sourceObject c.B c.b c.dense).obj.left,
            (stepProj c.B c.b c.dense).hom.left.base x' ∈ Zaux.V →
            ¬ (OnStrictTransform (stepProj c.B c.b c.dense) x'
                (wholeIdealFamily D d ((stepProj c.B c.b c.dense).hom.left.base x'))
                ((wholeIdealFamily D d ((stepProj c.B c.b c.dense).hom.left.base x')) ^ β ⊔
                  Zaux.H ((stepProj c.B c.b c.dense).hom.left.base x')) ∧
              OnStrictTransform (stepProj c.B c.b c.dense) x'
                (Zaux.H ((stepProj c.B c.b c.dense).hom.left.base x'))
                ((wholeIdealFamily D d ((stepProj c.B c.b c.dense).hom.left.base x')) ^ β ⊔
                  Zaux.H ((stepProj c.B c.b c.dense).hom.left.base x')))) ∧
          ∀ p x, x ∈ stratumBoundary f B (Z p).V (Z p).support i →
            ∀ᶠ y in 𝓝 x, LinearMap.range
              (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf c.B c.b y) =
                (intrinsicCentreStalkRange X.obj.left
                  (closure ((strata f B (i + 1) ∩ (Z p).V) \ (Z p).support)) y ⊔ (Z p).H y) ^ β ⊔
                    (Z p).H y := by
  let C := Cset f B (fun p => (Z p).support) (i + 1)
  let Q := C ∩ stratumBoundary f B Zaux.V Zaux.support i
  obtain ⟨hCa, hCc, _, hCnf⟩ := Cset_closed_relOpen_and_nonflat f B (fun p => (Z p).support)
    (i + 1) hfinite hmax
  have hClocal : IsLocallyAnalyticOn X Zaux.V C := locallyAnalytic_of_analytic hCa Zaux.V
  have hCV : C ⊆ Zaux.V := fun x hx => (hC hx).1
  have hCdense : Dense Cᶜ := hdense.mono (Set.compl_subset_compl.mpr hCnf)
  have hQZ : Q ⊆ Zaux.support := fun _ hx => hx.2.2
  obtain ⟨hQcompact, hQnonflat⟩ := compact_global_cut_of_local_data f B C Zaux i
    hSaux hClocal hCc hCV
  have hQdense : Dense Qᶜ := hCdense.mono (Set.compl_subset_compl.mpr inter_subset_left)
  obtain ⟨ω₀, hω⟩ := exists_source_large_omega_exact'
    f B Z Zaux i hS hSaux N hN hcover hfinite hmax hC
  refine ⟨ω₀, fun ω hω₀ => ?_⟩
  obtain ⟨D, d, hDfin, hDQ, hDsource, hDtracked⟩ := hω ω hω₀
  let : D.IsFiniteType := hDfin
  let IS := wholeIdealFamily D d
  have hIS : IsLocallyFinitelyGeneratedOn X.obj.left Zaux.V IS :=
    locallyFinite_wholeIdealFamily D d Zaux.V
  have hQIS : {x : X.obj.left | x ∈ Zaux.support ∧ IS x ≠ ⊤} = Q := by
    ext x
    constructor
    · intro hx
      have hxD : x ∈ nonunitLocus D d := hx.2
      rw [hDQ] at hxD
      exact hxD
    · intro hx
      have hxD : x ∈ nonunitLocus D d := by rw [hDQ]; exact hx
      exact ⟨hQZ hx, hxD⟩
  have hcompact : IsCompact {x : X.obj.left | x ∈ Zaux.support ∧ IS x ≠ ⊤} :=
    hQIS.symm ▸ hQcompact
  have hdense' : Dense {x : X.obj.left | ¬ (x ∈ Zaux.support ∧ IS x ≠ ⊤)} := by
    change Dense ({x : X.obj.left | x ∈ Zaux.support ∧ IS x ≠ ⊤}ᶜ)
    rw [hQIS]
    exact hQdense
  obtain ⟨α, hα⟩ := exists_sourceIdentified_sumCentre f Zaux IS hIS hcompact hdense'
  refine ⟨D, d, hDfin, hDQ, hDsource, α, fun β hαβ => ?_⟩
  obtain ⟨T, t, htfinite, htQ, htdense, htsum, htsource⟩ := hα β hαβ
  let c : AdmissibleCentre f := ⟨T, t, htfinite, htdense, by rw [htQ, hQIS]; exact hQnonflat⟩
  let : T.IsFiniteType := htfinite
  refine ⟨c, htQ.trans hQIS, htsum, flatOver_sumCentre f c.B c.b β htsum, ?_, ?_⟩
  · intro hβ x' hx'
    exact source_families_separated_unpowered f Zaux IS β hβ T t htdense htsource x' hx'
  intro p x hxE
  have hxC := tracked_boundary_subset_cset f B Z i hS N hN hcover p hxE
  have hxAux : x ∈ Zaux.support := hC hxC
  have hH := Zaux.eventually_eq (Z p) hxAux hxE.2
  have hD := hDtracked p x hxE
  filter_upwards [Zaux.isOpen.mem_nhds hxAux.1, hH, hD] with y hyV hyH hyD
  change LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf T t y) = _
  change IS y = _ at hyD
  rw [htsource y hyV, hyD, hyH]

end
end Hironaka.Analytic.Unibranch.HironakaG10TmSourceLargeOmega
