import Hironaka.Analytic.ReducedHypersurfaceJacobianCore
import Hironaka.Analytic.HolomorphicGermRing

set_option autoImplicit false

/-!
# A first-order bridge for locally factored hypersurface equations

The zero locus of an arbitrary local equation can be smooth while its
derivative vanishes: `f z = z₀^2` has the smooth zero hyperplane but zero
first derivative along it.  Thus smoothness of the *set*, or `RegularAtDim`,
cannot turn a chosen equation into a reduced generator.

This file records the valid first-order substitute.  A local factorization
`f = u * (z_j - q_j)` with `u q ≠ 0` gives a nonzero coordinate derivative.
`HolGerm.isUnit_iff_eval_ne_zero` supplies the unit side of this statement for
germs at the origin, but the current project has no theorem deriving this
factorization (or its generic version) from radicality of a principal
holomorphic-germ ideal.  In particular, none of the results below removes the
remaining reducedness input in `ReducedHypersurfaceJacobianCore`.
-/

open Set Filter
open scoped Topology

namespace Hironaka.HolomorphicGermReducednessBridge

open Hironaka.RegularLocusDense AnalyticLocalStatement

noncomputable section

variable {n : ℕ}

/-- A coordinate projection is holomorphic as a germ at the origin. -/
theorem eventually_differentiableAt_coordinate (j : Fin n) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z : ComplexModel n => z j) z :=
  Eventually.of_forall fun z => by
    simpa using (EuclideanSpace.proj (𝕜 := ℂ) j).differentiableAt

/-- A locally unit-times-coordinate factorization has a nonzero derivative in
that coordinate direction.  The equality is only required as a genuine germ
equality (`EventuallyEq`) at `q`; it is not an added regularity assumption. -/
theorem fderiv_apply_coordinateDirection_ne_zero_of_eventuallyEq_unit_mul_coordinate
    {f u : ComplexModel n → ℂ} {q : ComplexModel n} {j : Fin n}
    (hu : DifferentiableAt ℂ u q) (huq : u q ≠ 0)
    (hfac : f =ᶠ[𝓝 q] fun z => u z * (z j - q j)) :
    fderiv ℂ f q (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0 := by
  rw [hfac.fderiv_eq]
  have hcoord : HasFDerivAt (fun z : ComplexModel n => z j - q j)
      (EuclideanSpace.proj (𝕜 := ℂ) j) q := by
    simpa using (EuclideanSpace.proj (𝕜 := ℂ) j).hasFDerivAt.sub_const (q j)
  have hprod := hu.hasFDerivAt.mul hcoord
  change fderiv ℂ (u * fun z : ComplexModel n => z j - q j) q
    (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0
  rw [hprod.fderiv]
  simp [AnalyticJacobianSingularCore.coordinateDirection, huq]

/-- The preceding first-order fact can be obtained from an actual equality of
holomorphic germs at the origin.  Here `IsUnit` is the existing germ-ring
notion, and is converted to a nonzero value by
`HolGerm.isUnit_iff_eval_ne_zero`; the factorization equality itself is a
mathematical input, not a field added to an analytic-set presentation. -/
theorem fderiv_apply_coordinateDirection_ne_zero_of_germ_unit_mul_coordinate
    {f u : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ f z)
    (hu : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ u z)
    {j : Fin n}
    (hunit : IsUnit (HolGerm.mk u hu))
    (hfac : HolGerm.mk f hf = HolGerm.mk u hu *
      HolGerm.mk (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j)) :
    fderiv ℂ f 0 (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0 := by
  have hu0 : u 0 ≠ 0 := (HolGerm.isUnit_iff_eval_ne_zero _).mp hunit
  have hdu0 : DifferentiableAt ℂ u 0 := hu.self_of_nhds
  have hfac' : HolGerm.mk f hf = HolGerm.mk (fun z : ComplexModel n => u z * z j)
      (eventually_differentiableAt_mul hu (eventually_differentiableAt_coordinate j)) := by
    exact hfac.trans (HolGerm.mk_mul u (fun z : ComplexModel n => z j) hu
      (eventually_differentiableAt_coordinate j)).symm
  have heq : f =ᶠ[𝓝 (0 : ComplexModel n)] fun z => u z * z j :=
    HolGerm.mk_eq_mk_iff.mp hfac'
  have heq' : f =ᶠ[𝓝 (0 : ComplexModel n)]
      fun z => u z * (z j - (0 : ComplexModel n) j) := by
    filter_upwards [heq] with z hz
    simpa using hz
  exact fderiv_apply_coordinateDirection_ne_zero_of_eventuallyEq_unit_mul_coordinate
    hdu0 hu0 heq'

/-- A coordinate function represents a nonzero holomorphic germ at the
origin.  The proof uses its explicitly nonzero coordinate derivative, so does
not rely on an identity theorem for germs. -/
theorem coordinate_germ_ne_zero (j : Fin n) :
    HolGerm.mk (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j) ≠ 0 := by
  intro hzero
  have hmk : HolGerm.mk (fun z : ComplexModel n => z j)
      (eventually_differentiableAt_coordinate j) =
      HolGerm.mk (fun _ : ComplexModel n => 0) eventually_differentiableAt_zero := by
    rw [hzero]
    exact HolGerm.mk_zero.symm
  have heq : (fun z : ComplexModel n => z j) =ᶠ[𝓝 (0 : ComplexModel n)] fun _ => 0 :=
    HolGerm.mk_eq_mk_iff.mp hmk
  have hderiv : fderiv ℂ (fun z : ComplexModel n => z j) 0
      (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0 := by
    apply fderiv_apply_coordinateDirection_ne_zero_of_eventuallyEq_unit_mul_coordinate
      (f := fun z : ComplexModel n => z j) (u := fun _ : ComplexModel n => (1 : ℂ))
    · exact differentiableAt_const _
    · norm_num
    · filter_upwards with z
      simp
  apply hderiv
  rw [heq.fderiv_eq]
  simp

/-- A radical principal hypersurface ideal cannot be generated by a unit times
a proper positive power of a nonzero coordinate germ.  This is the precise
algebraic step missing from mere reducedness of the ambient germ ring: it
requires radicality of the *principal ideal* generated by `g`. -/
theorem exponent_eq_one_of_isRadical_span_unit_mul_coordinate_pow
    {g u : HolGerm (ComplexModel n)} {j : Fin n} {m : ℕ}
    (hradical : (Ideal.span ({g} : Set (HolGerm (ComplexModel n)))).IsRadical)
    (hunit : IsUnit u)
    (hfac : g = u * HolGerm.mk (fun z : ComplexModel n => z j)
      (eventually_differentiableAt_coordinate j) ^ m)
    (hzero : HolGerm.eval g = 0) :
    m = 1 := by
  have hcoord := coordinate_germ_ne_zero j
  let x : HolGerm (ComplexModel n) := HolGerm.mk (fun z : ComplexModel n => z j)
    (eventually_differentiableAt_coordinate j)
  change x ≠ 0 at hcoord
  change g = u * x ^ m at hfac
  cases m with
  | zero =>
      have hgu : g = u := by simpa using hfac
      have hu0 : HolGerm.eval u = 0 := by simpa [hgu] using hzero
      exact (HolGerm.isUnit_iff_eval_ne_zero u).mp hunit hu0 |>.elim
  | succ m =>
      cases m with
      | zero => rfl
      | succ k =>
          let I : Ideal (HolGerm (ComplexModel n)) := Ideal.span ({g} : Set _)
          have hpowmem : x ^ Nat.succ (Nat.succ k) ∈ I := by
            apply (I.unit_mul_mem_iff_mem hunit).mp
            rw [← hfac]
            exact Ideal.mem_span_singleton_self g
          have hxmem : x ∈ I := hradical ⟨Nat.succ (Nat.succ k), hpowmem⟩
          obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hxmem
          have hxq : x = x * (q * u * x ^ Nat.succ k) := by
            calc
              x = q * g := hq.symm
              _ = q * (u * x ^ Nat.succ (Nat.succ k)) := by rw [hfac]
              _ = x * (q * u * x ^ Nat.succ k) := by
                simp only [pow_succ]
                ring
          have hxeval : HolGerm.eval x = 0 := by
            simp [x]
          have hteval : HolGerm.eval (q * u * x ^ Nat.succ k) = 0 := by
            rw [map_mul, map_mul, map_pow, hxeval]
            simp
          have htunit : IsUnit (1 - q * u * x ^ Nat.succ k) :=
            (HolGerm.isUnit_iff_eval_ne_zero _).mpr (by simp [hteval])
          have hprod : x * (1 - q * u * x ^ Nat.succ k) = 0 := by
            rw [mul_sub, mul_one]
            exact sub_eq_zero.mpr hxq
          exfalso
          apply hcoord
          obtain ⟨v, hv⟩ := htunit
          have hprod' : x * (v : HolGerm (ComplexModel n)) = 0 := by
            rw [hv]
            exact hprod
          calc
            x = x * 1 := (mul_one x).symm
            _ = x * ((v : HolGerm (ComplexModel n)) * (↑(v⁻¹) : HolGerm (ComplexModel n))) := by
              rw [Units.mul_inv]
            _ = (x * (v : HolGerm (ComplexModel n))) * (↑(v⁻¹) : HolGerm (ComplexModel n)) := by
              rw [mul_assoc]
            _ = 0 := by rw [hprod', zero_mul]

/-- The radicality-and-power statement directly supplies the nonzero
coordinate derivative needed by the local hypersurface Jacobian criterion.
It deliberately keeps both the radical principal-ideal hypothesis and the
unit-times-coordinate-power factorization explicit. -/
theorem fderiv_apply_coordinateDirection_ne_zero_of_radical_germ_unit_mul_coordinate_pow
    {f u : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ f z)
    (hu : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ u z)
    {j : Fin n} {m : ℕ}
    (hradical : (Ideal.span ({HolGerm.mk f hf} : Set (HolGerm (ComplexModel n)))).IsRadical)
    (hunit : IsUnit (HolGerm.mk u hu))
    (hfac : HolGerm.mk f hf = HolGerm.mk u hu *
      HolGerm.mk (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j) ^ m)
    (hzero : HolGerm.eval (HolGerm.mk f hf) = 0) :
    fderiv ℂ f 0 (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0 := by
  have hm := exponent_eq_one_of_isRadical_span_unit_mul_coordinate_pow hradical hunit hfac hzero
  subst m
  apply fderiv_apply_coordinateDirection_ne_zero_of_germ_unit_mul_coordinate hf hu hunit
  simpa using hfac

/-- The radical-germ derivative bridge is invariant under translation of the
model coordinates.  Thus a germ factored at an arbitrary chart point can be
recentered at zero before applying the algebraic argument above. -/
theorem fderiv_apply_coordinateDirection_ne_zero_of_translated_radical_germ_unit_mul_coordinate_pow
    {f u : ComplexModel n → ℂ} (p : ComplexModel n)
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z => f (z + p)) z)
    (hu : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z => u (z + p)) z)
    {j : Fin n} {m : ℕ}
    (hradical : (Ideal.span ({HolGerm.mk (fun z => f (z + p)) hf} :
      Set (HolGerm (ComplexModel n)))).IsRadical)
    (hunit : IsUnit (HolGerm.mk (fun z => u (z + p)) hu))
    (hfac : HolGerm.mk (fun z => f (z + p)) hf =
      HolGerm.mk (fun z => u (z + p)) hu *
      HolGerm.mk (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j) ^ m)
    (hzero : HolGerm.eval (HolGerm.mk (fun z => f (z + p)) hf) = 0) :
    fderiv ℂ f p (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0 := by
  have hderiv := fderiv_apply_coordinateDirection_ne_zero_of_radical_germ_unit_mul_coordinate_pow
    hf hu hradical hunit hfac hzero
  simpa [fderiv_comp_add_right] using hderiv

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A genuine local unit-times-coordinate factorization of an honest
hypersurface presentation certifies its centre as a regular point.  This is
the usable connection from the germ-level bridge to the existing local
Jacobian criterion. -/
theorem regularAtDim_of_eventuallyEq_unit_mul_coordinate
    {S : Set M} {x : M} {N : Set (ComplexModel n)}
    {f u : ComplexModel n → ℂ} {j : Fin n}
    (hN : IsOpen N) (hxN : (complexChartAt (n := n) x).val x ∈ N)
    (hNtarget : N ⊆ (complexChartAt (n := n) x).val.target)
    (hf : DifferentiableOn ℂ f N)
    (hzero : ∀ {y : M}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ N →
        (y ∈ S ↔ f ((complexChartAt (n := n) x).val y) = 0))
    (hxS : x ∈ S)
    (hu : DifferentiableAt ℂ u ((complexChartAt (n := n) x).val x))
    (huq : u ((complexChartAt (n := n) x).val x) ≠ 0)
    (hfac : f =ᶠ[𝓝 ((complexChartAt (n := n) x).val x)]
      fun z => u z * (z j - ((complexChartAt (n := n) x).val x) j)) :
    RegularAtDim (n := n) S x (n - 1) := by
  apply AnalyticJacobianCriterion.regularAtDim_of_localHypersurfaceMinor_ne_zero
    f hN hxN hNtarget hf hzero hxS j
  exact fderiv_apply_coordinateDirection_ne_zero_of_eventuallyEq_unit_mul_coordinate
    hu huq hfac

end

end Hironaka.HolomorphicGermReducednessBridge
