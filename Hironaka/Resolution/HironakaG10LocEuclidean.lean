import Hironaka.Resolution.HironakaG10LocFrischUniversal
import Hironaka.Resolution.HironakaG10FlatPrivilegedEuclidean

/-! # Douady §8 and Frisch Lemme 3 on `ℂⁿ`: Th. 1 discharged

Lane G10F proved Douady's theorem of privileged neighbourhoods on `ℂⁿ` for closed polydiscs
(`HironakaG10FlatPrivilegedEuclidean.privilegedNbhdsProperty_euclidean`, no named input). This module
instantiates the chain with `X = ℂⁿ` (`EuclideanSpace ℂ (Fin n)`) and `𝒦 = closedPolydiscs n`:

* **`relExactAt_of_fibreExactAt_euclidean`** (Douady §8 Prop. 2 (a), free starts, over a parameter
  set `T`): NO named input.
* `eventually_fibreExactAt_euclidean` (Prop. 2 (b)), **`isOpen_fibreFlatAt_euclidean`** (openness of
  the flat locus, Tor₁ form), **`eventually_relFibreFlatAt_euclidean`** (relative version over a
  parameter set `T`), `relFibreFlatAt_of_kernelFamily_euclidean` (Frisch Lemme 3 (i)),
  **`relFibreFlatAt_frischLocus_euclidean`** (Lemme 3 (i) on Frisch's reduced locus): the ONLY
  remaining named input is `hA : RelationsTheoremA (EuclideanSpace ℂ (Fin n)) (closedPolydiscs n)`
  (Cartan's Theorem A on closed polydiscs, relation-sheaf form; TRUE).
BP: hironaka-g10-loc-euclidean.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10LocEuclidean
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10FlatPrivilegedEuclidean HironakaG10LocDirectPersistence
  HironakaG10LocSheafExact HironakaG10LocFibreOpen HironakaG10LocRelative HironakaG10LocProductExact
  HironakaG10LocFrischFlat HironakaG10LocFrischLocus

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] {n : ℕ}

/-- **Douady §8 Prop. 2 (a) on `ℂⁿ`, over a parameter set** (no named input). -/
theorem relExactAt_of_fibreExactAt_euclidean [FiniteDimensional ℂ S] (T : Set S) {a b c : ℕ}
    {G : Fin b → Fin c → S × EuclideanSpace ℂ (Fin n) → ℂ}
    {F : Fin a → Fin b → S × EuclideanSpace ℂ (Fin n) → ℂ} {s₀ : S} {x₀ : EuclideanSpace ℂ (Fin n)}
    (hs₀T : s₀ ∈ T) (hG : ∀ j k, HolAt (G j k) (s₀, x₀)) (hF : ∀ i j, HolAt (F i j) (s₀, x₀))
    (hFG : ∀ i k, ∀ᶠ p in 𝓝 (s₀, x₀), p.1 ∈ T → ∑ j, F i j p * G j k p = 0)
    (hex : FibreExactAt G F s₀ x₀) : RelExactAt T G F (s₀, x₀) :=
  relExactAt_of_fibreExactAt (privilegedNbhdsProperty_euclidean n) T hs₀T hG hF hFG hex

/-- **Douady §8 Prop. 2 (b) on `ℂⁿ`** (named input: Theorem A on closed polydiscs). -/
theorem eventually_fibreExactAt_euclidean [LocallyCompactSpace S]
    (hA : RelationsTheoremA (EuclideanSpace ℂ (Fin n)) (closedPolydiscs n)) (T : Set S) {a b c : ℕ}
    {G : Fin b → Fin c → S × EuclideanSpace ℂ (Fin n) → ℂ}
    {F : Fin a → Fin b → S × EuclideanSpace ℂ (Fin n) → ℂ} {s₀ : S} {x₀ : EuclideanSpace ℂ (Fin n)}
    (hs₀T : s₀ ∈ T) (hG : ∀ j k, HolAt (G j k) (s₀, x₀)) (hF : ∀ i j, HolAt (F i j) (s₀, x₀))
    (hFG : ∀ i k, ∀ᶠ p in 𝓝 (s₀, x₀), p.1 ∈ T → ∑ j, F i j p * G j k p = 0)
    (hex : FibreExactAt G F s₀ x₀) :
    ∀ᶠ p in 𝓝 (s₀, x₀), p.1 ∈ T → FibreExactAt G F p.1 p.2 :=
  eventually_fibreExactAt_rel (privilegedNbhdsProperty_euclidean n) hA T hs₀T hG hF hFG hex

/-- **Openness of the flat locus on `S × ℂⁿ`** (Tor₁ form; named input: Theorem A). -/
theorem isOpen_fibreFlatAt_euclidean [LocallyCompactSpace S]
    (hA : RelationsTheoremA (EuclideanSpace ℂ (Fin n)) (closedPolydiscs n)) {a b : ℕ}
    (A : Fin a → Fin b → S × EuclideanSpace ℂ (Fin n) → ℂ) :
    IsOpen {p : S × EuclideanSpace ℂ (Fin n) | FibreFlatAt A p} :=
  isOpen_fibreFlatAt (privilegedNbhdsProperty_euclidean n) hA A

/-- **Openness of the relative flat locus over a parameter set `T`** (named input: Theorem A). -/
theorem eventually_relFibreFlatAt_euclidean [LocallyCompactSpace S]
    (hA : RelationsTheoremA (EuclideanSpace ℂ (Fin n)) (closedPolydiscs n)) (T : Set S) {a b : ℕ}
    (A : Fin a → Fin b → S × EuclideanSpace ℂ (Fin n) → ℂ) {p₀ : S × EuclideanSpace ℂ (Fin n)}
    (hp₀ : p₀.1 ∈ T) (h : RelFibreFlatAt T A p₀) :
    ∀ᶠ p in 𝓝 p₀, p.1 ∈ T → RelFibreFlatAt T A p :=
  eventually_relFibreFlatAt (privilegedNbhdsProperty_euclidean n) hA T A hp₀ h

/-- **Frisch 1968 Lemme 3 (i) on `ℂⁿ`, kernel-family form** (named input: Theorem A). -/
theorem relFibreFlatAt_of_kernelFamily_euclidean [FiniteDimensional ℂ S]
    (hA : RelationsTheoremA (EuclideanSpace ℂ (Fin n)) (closedPolydiscs n)) (T : Set S)
    {K U : Set (EuclideanSpace ℂ (Fin n))} (hK : K ∈ closedPolydiscs n) [CompactSpace K]
    (hU : IsOpen U) (hKU : K ⊆ U) {V : Set S} (hV : IsOpen V) {s₀ : S} (hs₀V : s₀ ∈ V)
    (hs₀T : s₀ ∈ T) {a b c : ℕ} (f : Fin a → Fin b → S × EuclideanSpace ℂ (Fin n) → ℂ)
    (hf : ∀ i j, DifferentiableOn ℂ (f i j) (V ×ˢ U)) (σ : S → Fin b → Fin c → holSubalgebra K)
    (hσ : ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ σ s)
    (hcomp : ∀ᶠ s in 𝓝 s₀, s ∈ T → ∀ i k,
      ∑ j, fibRestrict K hKU (f i j) (hf i j) s * σ s j k = 0)
    (h₀ : DirectExact (σ s₀) (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀)) :
    ∀ᶠ s in 𝓝 s₀, s ∈ T → ∀ y ∈ interior K, RelFibreFlatAt T f (s, y) :=
  relFibreFlatAt_of_kernelFamily (privilegedNbhdsProperty_euclidean n) hA T hK hU hKU hV hs₀V hs₀T
    f hf σ hσ hcomp h₀

/-- **Frisch 1968 Lemme 3 (i) on Frisch's reduced locus, on `ℂⁿ`** (named input: Theorem A). -/
theorem relFibreFlatAt_frischLocus_euclidean [FiniteDimensional ℂ S]
    (hA : RelationsTheoremA (EuclideanSpace ℂ (Fin n)) (closedPolydiscs n))
    {K U : Set (EuclideanSpace ℂ (Fin n))} (hK : K ∈ closedPolydiscs n) [CompactSpace K]
    (hU : IsOpen U) (hKU : K ⊆ U) {V : Set S} (hV : IsOpen V) {s₀ : S} (hs₀V : s₀ ∈ V) {a b c : ℕ}
    (f : Fin a → Fin b → S × EuclideanSpace ℂ (Fin n) → ℂ)
    (hf : ∀ i j, DifferentiableOn ℂ (f i j) (V ×ˢ U)) (g₀ : Fin b → Fin c → holSubalgebra K)
    (h₀ : DirectExact g₀ (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀))
    (R₀ : (Fin b → holSubalgebra K) →L[ℂ] (Fin c → holSubalgebra K))
    (hR₀ : ∀ e, matrixOperator g₀ (R₀ (matrixOperator g₀ e)) = matrixOperator g₀ e)
    (S₀ : (Fin a → holSubalgebra K) →L[ℂ] (Fin b → holSubalgebra K))
    (hS₀ : ∀ x, matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀)
      (S₀ (matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀) x)) =
        matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀) x) :
    s₀ ∈ frischLocus ((matrixOperator g₀).comp R₀)
        ((matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀)).comp S₀) S₀
        (fun s => matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s)) V ∧
      ∀ᶠ s in 𝓝 s₀, s ∈ frischLocus ((matrixOperator g₀).comp R₀)
        ((matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀)).comp S₀) S₀
        (fun s => matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s)) V →
          ∀ y ∈ interior K, RelFibreFlatAt (frischLocus ((matrixOperator g₀).comp R₀)
            ((matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀)).comp S₀) S₀
            (fun s => matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s)) V)
            f (s, y) :=
  relFibreFlatAt_frischLocus (privilegedNbhdsProperty_euclidean n) hA hK hU hKU hV hs₀V f hf g₀ h₀
    R₀ hR₀ S₀ hS₀

end
end Hironaka.HironakaG10LocEuclidean
