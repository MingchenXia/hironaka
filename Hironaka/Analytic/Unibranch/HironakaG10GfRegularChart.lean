import Hironaka.Analytic.Unibranch.HironakaG10GfRelative
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Analytic.AnalyticRegularStratumTopology

/-!
# Flat charts at regular points of analytic sets (lane G10GF, run 0081, plan item G10-03-05.c2')

At a regular point `x` of dimension `k` of a subset `A` of an open `U ⊆ ℂᵈ`
(`Hironaka.RegularAtDim`: a local biholomorphism `Φ` of `ℂᵈ` maps `A` near `x` onto the
coordinate plane `ℂᵏ × 0`), the parametrization `ι = Φ⁻¹ ∘ incl` and the retraction `π = proj ∘ Φ` form a
`HironakaG10GfRelative.FlatChart` of `val '' A` at `x` (**`flatChart_of_regularAtDim`**).  Together with the
density of the regular locus (`AnalyticRegularStratumTopology.subset_closure_regularLocusAny`) this feeds
`HironakaG10GfRelative.exists_forall_relFibreFlatAt` at points of a dense subset of every analytic set
(**`exists_forall_relFibreFlatAt_of_analytic`**).

No named input.  Blueprint: `hironaka-g10gf-relative.tex`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold

namespace Hironaka.Analytic.Unibranch.HironakaG10GfRegularChart

noncomputable section

open Hironaka Hironaka HironakaG10LocRelative
  Hironaka.Analytic.Unibranch.HironakaG10GfRelative

variable {k d : ℕ}

/-- Coordinate inclusion `ℂᵏ → ℂᵈ` (pad with zeros). -/
def inclFun (_hk : k ≤ d) (s : EuclideanSpace ℂ (Fin k)) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun i : Fin d => if h : (i : ℕ) < k then s ⟨i, h⟩ else 0)

/-- Coordinate projection `ℂᵈ → ℂᵏ` (first `k` coordinates). -/
def projFun (hk : k ≤ d) (z : EuclideanSpace ℂ (Fin d)) : EuclideanSpace ℂ (Fin k) :=
  WithLp.toLp 2 (fun j : Fin k => z (Fin.castLE hk j))

/-- The coordinate inclusion as a continuous linear map. -/
def incl (hk : k ≤ d) : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := inclFun hk
      map_add' := by
        intro s t
        ext i
        simp only [inclFun, PiLp.toLp_apply, PiLp.add_apply]
        split_ifs <;> simp
      map_smul' := by
        intro c s
        ext i
        simp only [inclFun, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> simp }

/-- The coordinate projection as a continuous linear map. -/
def proj (hk : k ≤ d) : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin k) :=
  LinearMap.toContinuousLinearMap
    { toFun := projFun hk
      map_add' := by
        intro s t
        ext j
        simp [projFun]
      map_smul' := by
        intro c s
        ext j
        simp [projFun] }

theorem incl_apply (hk : k ≤ d) (s : EuclideanSpace ℂ (Fin k)) : incl hk s = inclFun hk s := rfl

theorem proj_apply (hk : k ≤ d) (z : EuclideanSpace ℂ (Fin d)) : proj hk z = projFun hk z := rfl

theorem proj_incl (hk : k ≤ d) (s : EuclideanSpace ℂ (Fin k)) : proj hk (incl hk s) = s := by
  ext j
  simp [incl_apply, proj_apply, inclFun, projFun]

theorem incl_mem_plane (hk : k ≤ d) (s : EuclideanSpace ℂ (Fin k)) :
    incl hk s ∈ complexCoordinatePlane d k := by
  intro i hi
  simp [incl_apply, inclFun, not_lt.2 hi]

theorem incl_proj_of_mem_plane (hk : k ≤ d) {z : EuclideanSpace ℂ (Fin d)}
    (hz : z ∈ complexCoordinatePlane d k) : incl hk (proj hk z) = z := by
  ext i
  by_cases h : (i : ℕ) < k
  · simp only [incl_apply, proj_apply, inclFun, projFun, PiLp.toLp_apply, dif_pos h]
    rfl
  · simp only [incl_apply, inclFun, PiLp.toLp_apply, dif_neg h]
    exact (hz i (not_lt.1 h)).symm

/-- On an open subset of `ℂᵈ` the preferred chart is the inclusion. -/
theorem complexChartAt_apply (U : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin d))) (x y : U) :
    (complexChartAt (n := d) x).val y = (y : EuclideanSpace ℂ (Fin d)) := by
  change chartAt (EuclideanSpace ℂ (Fin d)) x y = (y : EuclideanSpace ℂ (Fin d))
  rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
  rfl

theorem mem_complexChartAt_source (U : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin d))) (x y : U) :
    y ∈ (complexChartAt (n := d) x).val.source := by
  change y ∈ (chartAt (EuclideanSpace ℂ (Fin d)) x).source
  rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
  simp

theorem mem_of_mem_complexChartAt_target (U : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin d)))
    (x : U) {v : EuclideanSpace ℂ (Fin d)} (hv : v ∈ (complexChartAt (n := d) x).val.target) :
    v ∈ U := by
  change v ∈ (chartAt (EuclideanSpace ℂ (Fin d)) x).target at hv
  rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
    OpenPartialHomeomorph.subtypeRestr_def] at hv
  simp only [mfld_simps] at hv
  exact hv

/-- **A flat chart at a regular point.** -/
def flatChart_of_regularAtDim (U : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin d))) (A : Set U)
    (x : U) (k : ℕ) (h : RegularAtDim (n := d) A x k) :
    FlatChart (Subtype.val '' A) (x : EuclideanSpace ℂ (Fin d)) := by
  have hk : k ≤ d := h.1
  let Φ := Classical.choose h.2.2
  have hΦ := Classical.choose_spec h.2.2
  have hx : (complexChartAt (n := d) x).val x = (x : EuclideanSpace ℂ (Fin d)) :=
    complexChartAt_apply U x x
  have hsrcU : ∀ v ∈ Φ.source, v ∈ U := fun v hv =>
    mem_of_mem_complexChartAt_target U x (hΦ.1 hv)
  have hiff : ∀ v (hv : v ∈ Φ.source), (⟨v, hsrcU v hv⟩ : U) ∈ A ↔
      Φ.toFun v ∈ complexCoordinatePlane d k := by
    intro v hv
    have e := complexChartAt_apply U x ⟨v, hsrcU v hv⟩
    have := hΦ.2.2 (y := ⟨v, hsrcU v hv⟩) (mem_complexChartAt_source U x _)
      (by rw [e]; exact hv)
    rwa [e] at this
  exact
    { k := k
      O := Φ.source
      isOpen_O := Φ.isOpen_source
      mem_O := by rw [← hx]; exact Φ.center_mem_source
      B := incl hk ⁻¹' Φ.target
      isOpen_B := Φ.isOpen_target.preimage (incl hk).continuous
      ι := fun s => Φ.invFun (incl hk s)
      π := fun q => proj hk (Φ.toFun q)
      diff_ι := fun s hs =>
        ((Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hs)).comp s
          (incl hk).differentiableAt).differentiableWithinAt
      diff_π := fun q hq =>
        ((proj hk).differentiableAt.comp q
          (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hq))).differentiableWithinAt
      mapsTo_ι := by
        intro s hs
        have hsrc : Φ.invFun (incl hk s) ∈ Φ.source := Φ.mapsTo_invFun hs
        refine ⟨hsrc, ⟨⟨Φ.invFun (incl hk s), hsrcU _ hsrc⟩, ?_, rfl⟩⟩
        rw [hiff _ hsrc, Φ.right_inv _ hs]
        exact incl_mem_plane hk s
      π_mem := by
        rintro q ⟨hq, ⟨y, hyA, rfl⟩⟩
        have hpl := (hiff _ hq).1 hyA
        show incl hk (proj hk (Φ.toFun y)) ∈ Φ.target
        rw [incl_proj_of_mem_plane hk hpl]
        exact Φ.mapsTo_toFun hq
      π_ι := by
        intro s hs
        show proj hk (Φ.toFun (Φ.invFun (incl hk s))) = s
        rw [Φ.right_inv _ hs, proj_incl]
      ι_π := by
        rintro q ⟨hq, ⟨y, hyA, rfl⟩⟩
        have hpl := (hiff _ hq).1 hyA
        show Φ.invFun (incl hk (proj hk (Φ.toFun y))) = y
        rw [incl_proj_of_mem_plane hk hpl, Φ.left_inv _ hq] }

instance isComplexManifold_opens (U : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin d))) :
    IsComplexManifold d U where

/-- **Generic flatness over an analytic parameter set** (chart level, relative Tor₁ form): every open `V`
meeting `T = val '' A` (`A` analytic in an open `U ⊆ ℂᵈ`) contains a point `q ∈ T` over which `coker F` is flat
over `T` at every point of `{q} × K`. -/
theorem exists_forall_relFibreFlatAt_of_analytic (U : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin d)))
    {A : Set U} (hA : IsComplexAnalyticSubset (n := d) A) {m a b : ℕ}
    (F : Fin a → Fin b → EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin m) → ℂ)
    {W : Set (EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin m))} (hW : IsOpen W)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) W) {V : Set (EuclideanSpace ℂ (Fin d))} (hV : IsOpen V)
    (hVA : (V ∩ Subtype.val '' A).Nonempty) {K : Set (EuclideanSpace ℂ (Fin m))} (hK : IsCompact K)
    (hVK : ∀ q ∈ V ∩ Subtype.val '' A, ∀ z ∈ K, (q, z) ∈ W) :
    ∃ q ∈ V ∩ Subtype.val '' A, ∀ z ∈ K, RelFibreFlatAt (Subtype.val '' A) F (q, z) := by
  obtain ⟨_, hyV, y, hyA, rfl⟩ := hVA
  have hVU : IsOpen ((Subtype.val : U → EuclideanSpace ℂ (Fin d)) ⁻¹' V) :=
    hV.preimage continuous_subtype_val
  obtain ⟨x, hxV, hxreg⟩ := mem_closure_iff.1
    (AnalyticRegularStratumTopology.subset_closure_regularLocusAny hA hyA) _ hVU hyV
  rw [← AnalyticRegularStratumTopology.iUnion_regularLocus_eq_regularLocusAny] at hxreg
  obtain ⟨k, hk⟩ := mem_iUnion.1 hxreg
  have hreg : RegularAtDim (n := d) A x k := hk
  exact HironakaG10GfRelative.exists_forall_relFibreFlatAt F hW hF hV hK hVK hxV
    ⟨x, hreg.2.1, rfl⟩ (flatChart_of_regularAtDim U A x k hreg)

end

end Hironaka.Analytic.Unibranch.HironakaG10GfRegularChart
