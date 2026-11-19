import Hironaka.Resolution.HironakaRealOpenGeometricStrictSaturation
import Hironaka.Resolution.HironakaActualAnalyticSubspace
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The whole strict-space torsion kernel on a genuine open chart

One internally chosen source-open and exponent work at every raw point and
on every entire ambient structure-sheaf germ. The actual analytic pullback
quotient maps to the actual relative geometric strict-space stalk with
exact exceptional powers-torsion kernel. The original analytic set is
required analytic only inside its genuine open domain.

Blueprint: `hironaka-g10-real-open-strict-torsion-kernel.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG10RealOpenStrictTorsionKernel

noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaRealOpenGeometricStrictSaturation HironakaActualAnalyticBlowupTaylor
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetMonomialSpan
  HironakaActualCoefficientPresentationCentrePower GermIdealPullbackCalculus BlowupRestrictOpen

section WholeGerms

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem whole_mem_function_iff (B : GermIdeal n M) (hB : B.IsCoherent)
    (y : M) (f : M → ℂ) (hf : HolomorphicAt n f y) :
    actualOriginalFunctionGerm y f hf ∈ actualWholeSheafStalkIdeal B y ↔ B.mem y f := by
  obtain ⟨V, hV, hyV, s, G, hsource, hG, hcolumns⟩ :=
    exists_coherent_whole_stalk_original_columns B hB y
  obtain ⟨hGG, hbridge, hwhole⟩ := hcolumns y hyV
  have h := Ideal.apply_mem_of_equiv_iff
    (I := actualWholeSheafStalkIdeal B y) (f := actualStalkChartEquiv y)
    (x := actualOriginalFunctionGerm y f hf)
  change (actualStalkChartEquiv y) (actualOriginalFunctionGerm y f hf) ∈
    Ideal.map (actualStalkChartEquiv y).toRingHom (actualWholeSheafStalkIdeal B y) ↔ _ at h
  rw [map_actualWholeSheafStalkIdeal, actualOriginalFunctionGerm_chart, hwhole] at h
  exact h.symm.trans (hbridge f hf).symm

private theorem exists_function_representative (y : M)
    (g : actualComplexStructureStalk (n := n) y) :
    ∃f : M → ℂ, ∃hf : HolomorphicAt n f y,
      actualOriginalFunctionGerm y f hf = g := by
  obtain ⟨V, hy, s, rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq g
  refine ⟨sectionExtension V s, sectionExtension_holomorphicAt V s y hy, ?_⟩
  exact actualOriginalFunctionGerm_eq_section V y hy s _ _ Filter.EventuallyEq.rfl

private theorem function_germ_mul (y : M) (f g : M → ℂ)
    (hf : HolomorphicAt n f y) (hg : HolomorphicAt n g y) :
    actualOriginalFunctionGerm y (fun p => f p*g p) (hf.mul hg) =
      actualOriginalFunctionGerm y f hf * actualOriginalFunctionGerm y g hg := by
  apply (actualStalkChartEquiv y).injective
  rw [map_mul, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

private theorem function_germ_pow (y : M) (f : M → ℂ)
    (hf : HolomorphicAt n f y) (m : ℕ) :
    actualOriginalFunctionGerm y (fun p => f p^m)
      (BlowupDerivativeIdeal.holomorphicAt_pow hf m) =
        (actualOriginalFunctionGerm y f hf)^m := by
  apply (actualStalkChartEquiv y).injective
  rw [map_pow, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart]
  exact HolGerm.mk_pow _
    (translated_holomorphic _
      (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ y) hf)) m

end WholeGerms

variable (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
  (U : Opens (ComplexModel (d+t))) (W : Set U)

abbrev AmbientStalk (y : realOpenChartDomain d t j b U) :=
  actualComplexStructureStalk (n := d+t) y

/-- The entire original analytic pullback ideal in the actual ambient stalk. -/
def rawAnalyticIdeal (y : realOpenChartDomain d t j b U) :
    Ideal (AmbientStalk d t j b U y) :=
  actualWholeSheafStalkIdeal (realOpenTotalIdeal d t j b U W) y

/-- The whole relative geometric strict ideal at every raw source point. -/
def geometricStrictIdeal (y : realOpenChartDomain d t j b U) :
    Ideal (AmbientStalk d t j b U y) :=
  actualWholeSheafStalkIdeal (realOpenStrictIdeal d t j b U W) y

private theorem pivot_holomorphic (y : realOpenChartDomain d t j b U) :
    HolomorphicAt (d+t) (fun p : realOpenChartDomain d t j b U => p.val (j.natAdd d)) y := by
  have h : HolomorphicAt (d+t) (fun z : ComplexModel (d+t) => z (j.natAdd d)) y.val :=
    Eventually.of_forall fun _ =>
      (EuclideanSpace.proj (j.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt.mdifferentiableAt
  exact h.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)

/-- The actual original pivot function germ, retaining its value at the raw point. -/
def exceptionalGerm (y : realOpenChartDomain d t j b U) : AmbientStalk d t j b U y :=
  actualOriginalFunctionGerm y (fun p => p.val (j.natAdd d)) (pivot_holomorphic d t j b U y)

private theorem projection_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞
      (realOpenProjection d t j b U) := by
  have hp (i : Fin (d+t)) : ContDiff ℂ ∞ (fun z : ComplexModel (d+t) => z i) :=
    (EuclideanSpace.proj i : ComplexModel (d+t) →L[ℂ] ℂ).contDiff
  have hc (i : Fin (d+t)) : ContDiff ℂ ∞
      (actualAnalyticBlowupCoordinate (actualTangentCentreVariables d t) (j.natAdd d) b i) := by
    unfold actualAnalyticBlowupCoordinate
    split_ifs
    · exact hp _
    · exact (hp _).mul (contDiff_const.add (hp _))
    · exact hp _
  have hπ : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞
      (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) :=
    ((EuclideanSpace.equiv (Fin (d+t)) ℂ).symm.contDiff.comp (contDiff_pi.mpr hc)).contMDiff
  exact contMDiff_opens_mk (hπ.comp contMDiff_subtype_val) (fun p => p.property)

private theorem pivot_power_function_germ (y : realOpenChartDomain d t j b U)
    (f : realOpenChartDomain d t j b U → ℂ) (hf : HolomorphicAt (d+t) f y) (m : ℕ) :
    actualOriginalFunctionGerm y (fun p => f p*p.val (j.natAdd d)^m)
      (hf.mul (BlowupDerivativeIdeal.holomorphicAt_pow (pivot_holomorphic d t j b U y) m)) =
        (exceptionalGerm d t j b U y)^m * actualOriginalFunctionGerm y f hf := by
  rw [function_germ_mul y f (fun p => p.val (j.natAdd d)^m) hf
    (BlowupDerivativeIdeal.holomorphicAt_pow (pivot_holomorphic d t j b U y) m),
    function_germ_pow, mul_comm]
  rfl

/-- ONE actual source-open and exponent control the entire ideals at EVERY raw point. -/
theorem exists_local_whole_uniform_saturation
    (h0 : (0 : ComplexModel (d+t)) ∈ U) (hW : IsComplexAnalyticSubset (n := d+t) W) :
    ∃N : ℕ, ∃D : Opens (realOpenChartDomain d t j b U),
      realOpenOrigin d t j b U h0 ∈ D ∧
      ∀y ∈ D, ∀g : AmbientStalk d t j b U y,
        (g ∈ geometricStrictIdeal d t j b U W y ↔
          ∃m : ℕ, (exceptionalGerm d t j b U y)^m*g ∈ rawAnalyticIdeal d t j b U W y) ∧
        (g ∈ geometricStrictIdeal d t j b U W y ↔
          (exceptionalGerm d t j b U y)^N*g ∈ rawAnalyticIdeal d t j b U W y) ∧
        ∀q : ℕ, ((exceptionalGerm d t j b U y)^(N+q)*g ∈ rawAnalyticIdeal d t j b U W y ↔
          (exceptionalGerm d t j b U y)^N*g ∈ rawAnalyticIdeal d t j b U W y) := by
  obtain ⟨N, D, ho, hD⟩ := exists_realOpen_geoStrict_uniform_power d t j b U h0 W hW
  have hI : (realOpenTotalIdeal d t j b U W).IsCoherent :=
    isCoherent_pullback (projection_contMDiff d t j b U)
      (CartanIrreducible.cartanCoherence W hW)
  have hK : (realOpenStrictIdeal d t j b U W).IsCoherent :=
    (mem_realOpen_geoStrict_iff_exists_pivot_power d t j b U h0 W hW).2.1
  refine ⟨N, D, ho, ?_⟩
  intro y hy g
  obtain ⟨f, hf, rfl⟩ := exists_function_representative y g
  have hstrict : actualOriginalFunctionGerm y f hf ∈ geometricStrictIdeal d t j b U W y ↔
      (realOpenStrictIdeal d t j b U W).mem y f := whole_mem_function_iff _ hK y f hf
  have htotal (m : ℕ) :
      (exceptionalGerm d t j b U y)^m * actualOriginalFunctionGerm y f hf ∈
          rawAnalyticIdeal d t j b U W y ↔
        (realOpenTotalIdeal d t j b U W).mem y (fun p => f p*p.val (j.natAdd d)^m) := by
    rw [rawAnalyticIdeal, ←pivot_power_function_germ d t j b U y f hf m]
    exact whole_mem_function_iff _ hI y _ _
  refine ⟨?_, ?_, ?_⟩
  · exact hstrict.trans ((hD y hy f hf).1.trans (exists_congr fun m => (htotal m).symm))
  · exact hstrict.trans ((hD y hy f hf).2.1.trans (htotal N).symm)
  · intro q
    exact (htotal (N+q)).trans ((hD y hy f hf).2.2 q) |>.trans (htotal N).symm

variable (h0 : (0 : ComplexModel (d+t)) ∈ U) (hW : IsComplexAnalyticSubset (n := d+t) W)

/-- The exponent is chosen internally before every point and ambient germ. -/
def localExponent : ℕ :=
  Classical.choose (exists_local_whole_uniform_saturation d t j b U W h0 hW)

/-- One internally chosen genuine source-open works for every subsequent stalk map. -/
def localDomain : Opens (realOpenChartDomain d t j b U) :=
  Classical.choose (Classical.choose_spec (exists_local_whole_uniform_saturation d t j b U W h0 hW))

theorem origin_mem_localDomain :
    realOpenOrigin d t j b U h0 ∈ localDomain d t j b U W h0 hW :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_local_whole_uniform_saturation d t j b U W h0 hW))).1

/-- The entire strict ideal is the entire exceptional saturation at EVERY raw point in D. -/
theorem local_whole_saturation (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (g : AmbientStalk d t j b U y) :
    g ∈ geometricStrictIdeal d t j b U W y ↔
      ∃m : ℕ, (exceptionalGerm d t j b U y)^m*g ∈ rawAnalyticIdeal d t j b U W y :=
  ((Classical.choose_spec (Classical.choose_spec
    (exists_local_whole_uniform_saturation d t j b U W h0 hW))).2 y hy g).1

theorem local_whole_uniform_power (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (g : AmbientStalk d t j b U y) :
    g ∈ geometricStrictIdeal d t j b U W y ↔
      (exceptionalGerm d t j b U y)^(localExponent d t j b U W h0 hW)*g ∈
        rawAnalyticIdeal d t j b U W y :=
  ((Classical.choose_spec (Classical.choose_spec
    (exists_local_whole_uniform_saturation d t j b U W h0 hW))).2 y hy g).2.1

theorem local_whole_later_power (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (g : AmbientStalk d t j b U y) (q : ℕ) :
    (exceptionalGerm d t j b U y)^(localExponent d t j b U W h0 hW+q)*g ∈
        rawAnalyticIdeal d t j b U W y ↔
      (exceptionalGerm d t j b U y)^(localExponent d t j b U W h0 hW)*g ∈
        rawAnalyticIdeal d t j b U W y :=
  ((Classical.choose_spec (Classical.choose_spec
    (exists_local_whole_uniform_saturation d t j b U W h0 hW))).2 y hy g).2.2 q

abbrev RawAnalyticQuotient (y : realOpenChartDomain d t j b U) :=
  AmbientStalk d t j b U y ⧸ rawAnalyticIdeal d t j b U W y

abbrev GeometricStrictQuotient (y : realOpenChartDomain d t j b U) :=
  AmbientStalk d t j b U y ⧸ geometricStrictIdeal d t j b U W y

def exceptionalClass (y : realOpenChartDomain d t j b U) : RawAnalyticQuotient d t j b U W y :=
  Ideal.Quotient.mk (rawAnalyticIdeal d t j b U W y) (exceptionalGerm d t j b U y)

/-- The literal native powers-torsion ideal in the whole analytic quotient. -/
abbrev exceptionalTorsionIdeal (y : realOpenChartDomain d t j b U) :
    Ideal (RawAnalyticQuotient d t j b U W y) :=
  Submodule.torsion' (RawAnalyticQuotient d t j b U W y) (RawAnalyticQuotient d t j b U W y)
    (Submonoid.powers (exceptionalClass d t j b U W y))

theorem rawAnalyticIdeal_le_geometricStrictIdeal (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) :
    rawAnalyticIdeal d t j b U W y ≤ geometricStrictIdeal d t j b U W y := by
  intro g hg
  exact (local_whole_saturation d t j b U W h0 hW y hy g).mpr
    ⟨0, by simpa only [pow_zero, one_mul] using hg⟩

/-- The actual same-ambient-germ quotient map at every raw point of the chosen open. -/
def strictQuotientMap (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) :
    RawAnalyticQuotient d t j b U W y →+* GeometricStrictQuotient d t j b U W y :=
  Ideal.quotientMap (geometricStrictIdeal d t j b U W y)
    (RingHom.id (AmbientStalk d t j b U y))
      (rawAnalyticIdeal_le_geometricStrictIdeal d t j b U W h0 hW y hy)

theorem strictQuotientMap_mk (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (g : AmbientStalk d t j b U y) :
    strictQuotientMap d t j b U W h0 hW y hy
      (Ideal.Quotient.mk (rawAnalyticIdeal d t j b U W y) g) =
        Ideal.Quotient.mk (geometricStrictIdeal d t j b U W y) g := rfl

theorem strictQuotientMap_surjective (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) :
    Function.Surjective (strictQuotientMap d t j b U W h0 hW y hy) :=
  Ideal.quotientMap_surjective Function.surjective_id

/-- Equality of the ENTIRE kernel and native exceptional powers-torsion ideal. -/
theorem strictQuotientMap_ker (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) :
    RingHom.ker (strictQuotientMap d t j b U W h0 hW y hy) =
      exceptionalTorsionIdeal d t j b U W y := by
  ext s
  refine Submodule.Quotient.induction_on (rawAnalyticIdeal d t j b U W y) s ?_
  intro g
  change strictQuotientMap d t j b U W h0 hW y hy
    (Ideal.Quotient.mk (rawAnalyticIdeal d t j b U W y) g) = 0 ↔ _
  rw [strictQuotientMap_mk, Ideal.Quotient.eq_zero_iff_mem,
    local_whole_saturation d t j b U W h0 hW y hy g]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨⟨(exceptionalClass d t j b U W y)^m, ⟨m, rfl⟩⟩, ?_⟩
    change (Ideal.Quotient.mk (rawAnalyticIdeal d t j b U W y)
      (exceptionalGerm d t j b U y))^m *
        Ideal.Quotient.mk (rawAnalyticIdeal d t j b U W y) g = 0
    rw [←map_pow, ←map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  · rintro ⟨⟨s, hs⟩, hsg⟩
    obtain ⟨m, rfl⟩ := hs
    refine ⟨m, ?_⟩
    change (Ideal.Quotient.mk (rawAnalyticIdeal d t j b U W y)
      (exceptionalGerm d t j b U y))^m *
        Ideal.Quotient.mk (rawAnalyticIdeal d t j b U W y) g = 0 at hsg
    rw [←map_pow, ←map_mul, Ideal.Quotient.eq_zero_iff_mem] at hsg
    exact hsg

/-- The actual native strict-space stalk at an included source-open point. -/
abbrev StrictStalk (y : realOpenChartDomain d t j b U)
    (hyS : y ∈ realOpenStrictTransform d t j b U W) :=
  ((actualSubspaceLocallyRingedSpace (n := d+t)
    (realOpenStrictTransform d t j b U W)).presheaf.stalk ⟨y, hyS⟩).carrier

def strictStalkEquiv (y : realOpenChartDomain d t j b U)
    (hyS : y ∈ realOpenStrictTransform d t j b U W) :
    StrictStalk d t j b U W y hyS ≃+* GeometricStrictQuotient d t j b U W y :=
  actualSubspaceStalkWholeEquiv (n := d+t) (realOpenStrictTransform d t j b U W) ⟨y, hyS⟩

/-- The actual analytic quotient maps to the actual relative geometric strict stalk. -/
def strictStalkMap (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW)
    (hyS : y ∈ realOpenStrictTransform d t j b U W) :
    RawAnalyticQuotient d t j b U W y →+* StrictStalk d t j b U W y hyS :=
  (strictStalkEquiv d t j b U W y hyS).symm.toRingHom.comp
    (strictQuotientMap d t j b U W h0 hW y hy)

theorem strictStalkMap_surjective (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW)
    (hyS : y ∈ realOpenStrictTransform d t j b U W) :
    Function.Surjective (strictStalkMap d t j b U W h0 hW y hy hyS) :=
  (strictStalkEquiv d t j b U W y hyS).symm.surjective.comp
    (strictQuotientMap_surjective d t j b U W h0 hW y hy)

theorem strictStalkMap_ker (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW)
    (hyS : y ∈ realOpenStrictTransform d t j b U W) :
    RingHom.ker (strictStalkMap d t j b U W h0 hW y hy hyS) =
      exceptionalTorsionIdeal d t j b U W y := by
  rw [←strictQuotientMap_ker d t j b U W h0 hW y hy]
  ext s
  change (strictStalkEquiv d t j b U W y hyS).symm
    (strictQuotientMap d t j b U W h0 hW y hy s) = 0 ↔ _
  exact (strictStalkEquiv d t j b U W y hyS).symm.map_eq_zero_iff

/-- EVERY actual ambient germ follows the actual LRS inclusion stalk map. -/
theorem strictStalkMap_mk (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW)
    (hyS : y ∈ realOpenStrictTransform d t j b U W) (g : AmbientStalk d t j b U y) :
    strictStalkMap d t j b U W h0 hW y hy hyS
      (Ideal.Quotient.mk (rawAnalyticIdeal d t j b U W y) g) =
        (actualSubspaceInclusion (n := d+t) (realOpenStrictTransform d t j b U W)).stalkMap
          ⟨y, hyS⟩ g := by
  apply (strictStalkEquiv d t j b U W y hyS).injective
  change (strictStalkEquiv d t j b U W y hyS)
    ((strictStalkEquiv d t j b U W y hyS).symm
      (strictQuotientMap d t j b U W h0 hW y hy
        (Ideal.Quotient.mk (rawAnalyticIdeal d t j b U W y) g))) = _
  rw [RingEquiv.apply_symm_apply, strictQuotientMap_mk]
  exact (actualSubspaceInclusion_stalk (n := d+t)
    (realOpenStrictTransform d t j b U W) ⟨y, hyS⟩ g).symm

/-- The actual nearby strict stalk is the WHOLE exceptional torsion quotient. -/
def torsionQuotientStrictStalkEquiv (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW)
    (hyS : y ∈ realOpenStrictTransform d t j b U W) :
    RawAnalyticQuotient d t j b U W y ⧸ exceptionalTorsionIdeal d t j b U W y ≃+*
      StrictStalk d t j b U W y hyS :=
  (Ideal.quotEquivOfEq (strictStalkMap_ker d t j b U W h0 hW y hy hyS).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (strictStalkMap_surjective d t j b U W h0 hW y hy hyS))

theorem torsionQuotientStrictStalkEquiv_mk (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW)
    (hyS : y ∈ realOpenStrictTransform d t j b U W) (s : RawAnalyticQuotient d t j b U W y) :
    torsionQuotientStrictStalkEquiv d t j b U W h0 hW y hy hyS
      (Ideal.Quotient.mk (exceptionalTorsionIdeal d t j b U W y) s) =
        strictStalkMap d t j b U W h0 hW y hy hyS s := rfl

end

end Hironaka.HironakaG10RealOpenStrictTorsionKernel
