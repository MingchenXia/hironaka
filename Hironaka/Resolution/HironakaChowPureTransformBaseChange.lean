import Hironaka.Resolution.HironakaChowPureTransformMinorDensity
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The SAME original pure-transform matrix under arbitrary base change

The original matrix and its full minor ideal are retained. Native tensor
localization gives the ENTIRE kernel of the original target localization
map, with no flatness hypothesis on the base-change map.

Blueprint: `hironaka-g10-pure-transform-base-change.tex`.
-/

set_option autoImplicit false

open Set Module TensorProduct

namespace Hironaka.HironakaChowPureTransformBaseChange

universe uT

noncomputable section

variable {R S M P : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]

/-- Native tensor base change of an actual localization map is the actual
localization at the image denominator. No flatness/regularity input. -/
theorem baseChange_isLocalizedModule (d : R) (h : M →ₗ[R] P)
    [IsLocalizedModule (Submonoid.powers d) h] :
    IsLocalizedModule (Submonoid.powers (algebraMap R S d)) (h.baseChange S) := by
  have hcomm : (h.baseChange S).restrictScalars R =
      (TensorProduct.comm R P S).toLinearMap.comp
        ((AlgebraTensorModule.rTensor R S h).comp
          (TensorProduct.comm R S M).toLinearMap) := by
    ext s m
    rfl
  have : IsLocalizedModule (Submonoid.powers d) ((h.baseChange S).restrictScalars R) := by
    rw [hcomm]
    infer_instance
  simpa only [Algebra.algebraMapSubmonoid_powers] using
    (IsLocalizedModule.of_restrictScalars (Submonoid.powers d) (h.baseChange S))

/-- Actual tensor/localization comparison for the ORIGINAL source localization
map. It uses the native module actions and native localization uniqueness. -/
def localizedBaseChangeEquiv (d : R) :
    LocalizedModule (Submonoid.powers (algebraMap R S d)) (S ⊗[R] M)
      ≃ₗ[S] S ⊗[R] LocalizedModule (Submonoid.powers d) M := by
  let h := (LocalizedModule.mkLinearMap (Submonoid.powers d) M).baseChange S
  let := baseChange_isLocalizedModule (S := S) d
    (LocalizedModule.mkLinearMap (Submonoid.powers d) M)
  exact IsLocalizedModule.iso (Submonoid.powers (algebraMap R S d)) h

@[simp]
theorem localizedBaseChangeEquiv_mk (d : R) (t : S ⊗[R] M) :
    localizedBaseChangeEquiv (S := S) (M := M) d
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S d)) (S ⊗[R] M) t) =
      (LocalizedModule.mkLinearMap (Submonoid.powers d) M).baseChange S t :=
  by
    let := baseChange_isLocalizedModule (S := S) d
      (LocalizedModule.mkLinearMap (Submonoid.powers d) M)
    exact IsLocalizedModule.iso_mk_one _ _ t

/-- The deterministic vector-valued tensor map of the SAME original cleared map. -/
def vectorBaseChange {r : ℕ} (f : M →ₗ[R] (Fin r → R)) :
    S ⊗[R] M →ₗ[S] (Fin r → S) :=
  (TensorProduct.piScalarRight R S S (Fin r)).toLinearMap.comp (f.baseChange S)

@[simp]
theorem vectorBaseChange_tmul {r : ℕ} (f : M →ₗ[R] (Fin r → R)) (s : S) (m : M)
    (i : Fin r) :
    vectorBaseChange (S := S) f (s ⊗ₜ[R] m) i = algebraMap R S (f m i) * s := by
  simp [vectorBaseChange, Algebra.smul_def]

private def coordinateLocalizationMap (d : R) (r : ℕ) :
    (Fin r → R) →ₗ[R] (Fin r → Localization.Away d) :=
  LinearMap.pi fun i => (Algebra.linearMap R (Localization.Away d)).comp (LinearMap.proj i)

private theorem coordinateLocalizationMap_isLocalizedModule (d : R) (r : ℕ) :
    IsLocalizedModule (Submonoid.powers d) (coordinateLocalizationMap d r) := by
  let E := (TensorProduct.piScalarRight R (Localization.Away d) (Localization.Away d)
    (Fin r)).restrictScalars R
  have hE : coordinateLocalizationMap d r =
      E.toLinearMap.comp (TensorProduct.mk R (Localization.Away d) (Fin r → R) 1) := by
    ext v i
    simp [coordinateLocalizationMap, E, Algebra.smul_def]
  rw [hE]
  infer_instance

/-- The whole kernel after arbitrary base change is the kernel of the ORIGINAL
new localization map, proved from the original clearing identity, not by
incorrectly tensoring the old kernel equality. -/
theorem ker_vectorBaseChange_eq_localization {r : ℕ}
    (d : R) (hδ : IsRegular (algebraMap R S d)) (N : ℕ)
    (f : M →ₗ[R] (Fin r → R))
    (e : LocalizedModule (Submonoid.powers d) M ≃ₗ[Localization.Away d]
      (Fin r → Localization.Away d))
    (hclear : ∀ m i, algebraMap R (Localization.Away d) (f m i) =
      d ^ N • e (LocalizedModule.mkLinearMap (Submonoid.powers d) M m) i) :
    LinearMap.ker (vectorBaseChange (S := S) f) =
      LinearMap.ker (LocalizedModule.mkLinearMap
        (Submonoid.powers (algebraMap R S d)) (S ⊗[R] M)) := by
  let l := LocalizedModule.mkLinearMap (Submonoid.powers d) M
  let J := coordinateLocalizationMap d r
  let E := (e.restrictScalars R).baseChange R S
  let L := l.baseChange S
  let B := f.baseChange S
  let V := TensorProduct.piScalarRight R S S (Fin r)
  let := coordinateLocalizationMap_isLocalizedModule d r
  let := baseChange_isLocalizedModule (S := S) d J
  let := baseChange_isLocalizedModule (S := S) d l
  have hclearMap : J.comp f = d ^ N • (e.restrictScalars R).toLinearMap.comp l := by
    ext m i
    exact hclear m i
  have hbase : (J.baseChange S).comp B = d ^ N • E.toLinearMap.comp L := by
    simpa only [E, B, L, LinearMap.baseChange_comp, LinearMap.baseChange_smul,
      LinearEquiv.coe_baseChange] using congrArg (LinearMap.baseChange S) hclearMap
  have hL (t : S ⊗[R] M) : L t = 0 ↔
      LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S d)) (S ⊗[R] M) t = 0 := by
    rw [← (localizedBaseChangeEquiv (S := S) (M := M) d).map_eq_zero_iff]
    rw [localizedBaseChangeEquiv_mk]
  ext t
  simp only [LinearMap.mem_ker]
  constructor
  · intro ht
    have hB : B t = 0 := V.injective (by simpa [vectorBaseChange, B, V] using ht)
    have hpow : d ^ N • E (L t) = 0 := by
      have hh := congrArg (fun h => h t) hbase
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, hB, map_zero] using hh.symm
    have hEL : (E.restrictScalars R) (d ^ N • L t) = (E.restrictScalars R) 0 := by
      rw [map_smul, map_zero]
      exact hpow
    have hzero : d ^ N • L t = 0 := E.injective hEL
    have hzeroS : (algebraMap R S d) ^ N • L t = 0 := by
      simpa only [← map_pow, algebraMap_smul] using hzero
    have hzeroL : L t = 0 := IsLocalizedModule.smul_injective L
      (⟨_, N, rfl⟩ : Submonoid.powers (algebraMap R S d))
      (by simpa only [Submonoid.smul_def, smul_zero] using hzeroS)
    exact (hL t).mp hzeroL
  · intro ht
    have hzeroL := (hL t).mpr ht
    have hJB : J.baseChange S (B t) = J.baseChange S 0 := by
      have hh := congrArg (fun h => h t) hbase
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply, hzeroL, map_zero,
        smul_zero] using hh
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers (algebraMap R S d)) (f := J.baseChange S) hJB
    have hv : (algebraMap R S d) ^ k • vectorBaseChange (S := S) f t = 0 := by
      have hh := congrArg V hk
      simpa only [Submonoid.smul_def, map_smul, map_zero, smul_zero,
        vectorBaseChange, LinearMap.comp_apply, V, B, LinearEquiv.coe_coe] using hh
    ext i
    apply (hδ.pow k).left
    simpa only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero] using congrFun hv i


/-- The original generators become the literal columns of the SAME entrywise
base-changed matrix. No flatness or regularity is needed for this range equality. -/
theorem range_vectorBaseChange_eq_matrix {r q : ℕ}
    (g : Fin q → M) (hg : Submodule.span R (range g) = ⊤)
    (f : M →ₗ[R] (Fin r → R)) (A : Matrix (Fin r) (Fin q) R)
    (hcols : ∀ j, A.col j = f (g j)) :
    (vectorBaseChange (S := S) f).range = (Matrix.toLin' (A.map (algebraMap R S))).range := by
  have hgS : Submodule.span S (range fun j => (1 : S) ⊗ₜ[R] g j) = ⊤ := by
    have hh := congrArg (Submodule.baseChange S) hg
    simpa only [Submodule.baseChange_span, Submodule.baseChange_top, ← range_comp,
      Function.comp_def, TensorProduct.mk_apply] using hh
  have hcolsS : (fun j => vectorBaseChange (S := S) f ((1 : S) ⊗ₜ[R] g j)) =
      (A.map (algebraMap R S)).col := by
    funext j
    ext i
    simp only [vectorBaseChange_tmul, mul_one]
    exact congrArg (algebraMap R S) (congrFun (hcols j).symm i)
  rw [Matrix.range_toLin', ← Submodule.map_top (vectorBaseChange (S := S) f),
    ← hgS, Submodule.map_span, ← range_comp]
  exact congrArg (Submodule.span S) (congrArg range hcolsS)

open HironakaChowDeterminantalImage

/-- Standard full determinantal-ideal base change, specialized to the already
accepted ORIGINAL ideal definition; all original row/column selections retained. -/
theorem minorIdeal_map {T : Type*} [CommRing T] {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) R) (r : ℕ) (φ : R →+* T) :
    minorIdeal (A.map φ) r = Ideal.map φ (minorIdeal A r) := by
  rw [minorIdeal, minorIdeal, Ideal.map_span]
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨ij, rfl⟩
    exact ⟨(A.submatrix ij.1 ij.2).det, ⟨ij, rfl⟩, φ.map_det (A.submatrix ij.1 ij.2)⟩
  · rintro ⟨_, ⟨ij, rfl⟩, rfl⟩
    exact ⟨ij, (φ.map_det (A.submatrix ij.1 ij.2)).symm⟩

/-- The actual ORIGINAL target-localization quotient is the SAME original matrix
image after base change, with a dictionary on EVERY original tensor class. -/
theorem baseChange_quotient_equiv {r q : ℕ}
    (d : R) (hδ : IsRegular (algebraMap R S d)) (N : ℕ)
    (g : Fin q → M) (hg : Submodule.span R (range g) = ⊤)
    (f : M →ₗ[R] (Fin r → R)) (A : Matrix (Fin r) (Fin q) R)
    (e : LocalizedModule (Submonoid.powers d) M ≃ₗ[Localization.Away d]
      (Fin r → Localization.Away d))
    (hclear : ∀ m i, algebraMap R (Localization.Away d) (f m i) =
      d ^ N • e (LocalizedModule.mkLinearMap (Submonoid.powers d) M m) i)
    (hcols : ∀ j, A.col j = f (g j)) :
    ∃ E : ((S ⊗[R] M) ⧸ LinearMap.ker (LocalizedModule.mkLinearMap
      (Submonoid.powers (algebraMap R S d)) (S ⊗[R] M)))
        ≃ₗ[S] (Matrix.toLin' (A.map (algebraMap R S))).range,
      (vectorBaseChange (S := S) f).range = (Matrix.toLin' (A.map (algebraMap R S))).range ∧
      LinearMap.ker (vectorBaseChange (S := S) f) =
        LinearMap.ker (LocalizedModule.mkLinearMap
          (Submonoid.powers (algebraMap R S d)) (S ⊗[R] M)) ∧
      (∀ t, (E (Submodule.Quotient.mk t)).val = vectorBaseChange (S := S) f t) ∧
      minorIdeal (A.map (algebraMap R S)) r = Ideal.map (algebraMap R S) (minorIdeal A r) := by
  let F := vectorBaseChange (S := S) f
  let l := LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S d)) (S ⊗[R] M)
  have hrange := range_vectorBaseChange_eq_matrix (S := S) g hg f A hcols
  have hker := ker_vectorBaseChange_eq_localization d hδ N f e hclear
  let E := (Submodule.quotEquivOfEq (LinearMap.ker l) (LinearMap.ker F) hker.symm).trans
    (F.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))
  exact ⟨E, hrange, hker, fun _ => rfl, minorIdeal_map A r (algebraMap R S)⟩


/-- ONE original internally constructed matrix/ideal is retained before EVERY
arbitrary target ring map with regular image denominator. No target matrix choice,
flatness hypothesis or target free/basis certificate is supplied. -/
theorem exists_universal_baseChange_pure_transform_matrix [Module.Finite R M]
    (d : R) (hd : IsRegular d) (r : ℕ)
    (e : LocalizedModule (Submonoid.powers d) M ≃ₗ[Localization.Away d]
      (Fin r → Localization.Away d)) :
    ∃ (N q : ℕ) (g : Fin q → M) (f : M →ₗ[R] (Fin r → R))
      (A : Matrix (Fin r) (Fin q) R)
      (E : (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) M))
        ≃ₗ[R] (Matrix.toLin' A).range) (K : ℕ),
      Submodule.span R (range g) = ⊤ ∧
      (∀ m i, algebraMap R (Localization.Away d) (f m i) =
        d ^ N • e (LocalizedModule.mkLinearMap (Submonoid.powers d) M m) i) ∧
      (∀ j, A.col j = f (g j)) ∧ f.range = (Matrix.toLin' A).range ∧
      LinearMap.ker f = LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) M) ∧
      (∀ m, (E (Submodule.Quotient.mk m)).val = f m) ∧
      (minorIdeal A r).FG ∧ d ^ K ∈ minorIdeal A r ∧ IsRegular (d ^ K) ∧
      ∀ (T : Type uT) [CommRing T] (φ : R →+* T),
        letI : Algebra R T := φ.toAlgebra
        IsRegular (φ d) →
        ∃ ET : ((T ⊗[R] M) ⧸ LinearMap.ker (LocalizedModule.mkLinearMap
          (Submonoid.powers (φ d)) (T ⊗[R] M))) ≃ₗ[T] (Matrix.toLin' (A.map φ)).range,
          (vectorBaseChange (S := T) f).range = (Matrix.toLin' (A.map φ)).range ∧
          LinearMap.ker (vectorBaseChange (S := T) f) =
            LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers (φ d)) (T ⊗[R] M)) ∧
          (∀ t, (ET (Submodule.Quotient.mk t)).val = vectorBaseChange (S := T) f t) ∧
          minorIdeal (A.map φ) r = Ideal.map φ (minorIdeal A r) ∧
          (φ d) ^ K ∈ Ideal.map φ (minorIdeal A r) ∧ IsRegular ((φ d) ^ K) := by
  obtain ⟨N, q, g, f, A, E, K, hg, hclear, hcols, hrange, hker, hE, hfg, hK, hreg⟩ :=
    HironakaChowPureTransformMinorDensity.exists_pure_transform_matrix_with_regular_minor_power
      d hd r e
  refine ⟨N, q, g, f, A, E, K, hg, hclear, hcols, hrange, hker, hE, hfg, hK, hreg, ?_⟩
  intro T _ φ
  let : Algebra R T := φ.toAlgebra
  intro hδ
  obtain ⟨ET, hTrange, hTker, hET, hI⟩ :=
    baseChange_quotient_equiv (S := T) d hδ N g hg f A e hclear hcols
  refine ⟨ET, hTrange, hTker, hET, hI, ?_, hδ.pow K⟩
  simpa only [map_pow] using Ideal.mem_map_of_mem φ hK

end

end Hironaka.HironakaChowPureTransformBaseChange
