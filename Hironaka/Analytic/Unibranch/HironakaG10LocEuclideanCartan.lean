import Hironaka.Analytic.Unibranch.HironakaG10CartanBoxBridge
import Hironaka.Resolution.HironakaG10LocEuclidean

/-!
# Cartan inputs discharged and compact uniform persistence

Cartan's box theorems supply the remaining relation-Theorem-A input in the
Euclidean Douady--Frisch development.  Compactness then makes relative or
absolute exact-start persistence uniform on an arbitrary compact fibre set.

`FibreFlatAt` and `RelFibreFlatAt` are the existing Tor₁/exact-start predicates.
The local criterion identifying them with flatness of a stalk module is a
separate obligation.  These results do not assert persistent local flatteners
for general proper morphisms or nonreduced parameter spaces.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan

open Hironaka OkaRelationSheaf HironakaG10FlatPrivilegedEuclidean
  HironakaG10LocSheafExact HironakaG10LocFibreOpen HironakaG10LocRelative

/-- Cartan's relation Theorem A for the full family of Euclidean closed polydiscs. -/
theorem relationsTheoremA_closedPolydiscs (n : ℕ) :
    RelationsTheoremA (EuclideanSpace ℂ (Fin n)) (closedPolydiscs n) := by
  intro K hK
  exact (HironakaG10CartanBoxBridge.ta_tb_closedPolydisc n hK).1

section Metric

variable {S X : Type*} [PseudoMetricSpace S] [PseudoMetricSpace X]

/-- An open set containing one compact fibre contains the nearby fibres on
that same compact set.  No nonemptiness assumption on the compact set is needed. -/
theorem eventually_forall_mem_of_isOpen {K : Set X} (hK : IsCompact K)
    {W : Set (S × X)} (hW : IsOpen W) {s₀ : S}
    (hKW : ∀ y ∈ K, (s₀, y) ∈ W) :
    ∀ᶠ s in 𝓝 s₀, ∀ y ∈ K, (s, y) ∈ W := by
  have hC : IsCompact (({s₀} : Set S) ×ˢ K) := isCompact_singleton.prod hK
  have hCW : ({s₀} : Set S) ×ˢ K ⊆ W := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    rcases mem_singleton_iff.mp hs with rfl
    exact hKW y hy
  obtain ⟨δ, hδ, hδW⟩ := hC.exists_cthickening_subset_open hW hCW
  filter_upwards [Metric.ball_mem_nhds s₀ hδ] with s hs y hy
  apply hδW
  refine Metric.mem_cthickening_of_dist_le (s, y) (s₀, y) δ _ ⟨by simp, hy⟩ ?_
  simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using
    (le_of_lt (Metric.mem_ball.mp hs))

end Metric

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
  [LocallyCompactSpace S] {n : ℕ}

/-- The Euclidean absolute exact-start locus is open without a named Cartan input. -/
theorem isOpen_fibreFlatAt {a b : ℕ}
    (A : Fin a → Fin b → S × EuclideanSpace ℂ (Fin n) → ℂ) :
    IsOpen {p : S × EuclideanSpace ℂ (Fin n) | FibreFlatAt A p} :=
  HironakaG10LocEuclidean.isOpen_fibreFlatAt_euclidean
    (relationsTheoremA_closedPolydiscs n) A

/-- Relative exact-start persistence on Euclidean fibres, with Cartan's
relation Theorem A supplied by the box construction. -/
theorem eventually_relFibreFlatAt (T : Set S) {a b : ℕ}
    (A : Fin a → Fin b → S × EuclideanSpace ℂ (Fin n) → ℂ)
    {p₀ : S × EuclideanSpace ℂ (Fin n)} (hp₀ : p₀.1 ∈ T)
    (h : RelFibreFlatAt T A p₀) :
    ∀ᶠ p in 𝓝 p₀, p.1 ∈ T → RelFibreFlatAt T A p :=
  HironakaG10LocEuclidean.eventually_relFibreFlatAt_euclidean
    (relationsTheoremA_closedPolydiscs n) T A hp₀ h

/-- Relative persistence is uniform on any compact subset of a fibre.
The parameter subset `T` need not be open, closed or analytic. -/
theorem eventually_relFibreFlatAt_compact (T : Set S) {a b : ℕ}
    (A : Fin a → Fin b → S × EuclideanSpace ℂ (Fin n) → ℂ)
    {K : Set (EuclideanSpace ℂ (Fin n))} (hK : IsCompact K)
    {s₀ : S} (hs₀ : s₀ ∈ T) (h : ∀ y ∈ K, RelFibreFlatAt T A (s₀, y)) :
    ∀ᶠ s in 𝓝 s₀, s ∈ T → ∀ y ∈ K, RelFibreFlatAt T A (s, y) := by
  let D : Set (S × EuclideanSpace ℂ (Fin n)) :=
    {p | p.1 ∈ T → RelFibreFlatAt T A p}
  have hKD : ∀ y ∈ K, (s₀, y) ∈ interior D := by
    intro y hy
    exact mem_interior_iff_mem_nhds.mpr
      (eventually_relFibreFlatAt T A hs₀ (h y hy))
  have hev := eventually_forall_mem_of_isOpen hK isOpen_interior hKD
  filter_upwards [hev] with s hs hsT y hy
  exact (interior_subset (hs y hy)) hsT

/-- Absolute exact-start persistence is uniform on an arbitrary compact fibre set. -/
theorem eventually_fibreFlatAt_compact {a b : ℕ}
    (A : Fin a → Fin b → S × EuclideanSpace ℂ (Fin n) → ℂ)
    {K : Set (EuclideanSpace ℂ (Fin n))} (hK : IsCompact K)
    {s₀ : S} (h : ∀ y ∈ K, FibreFlatAt A (s₀, y)) :
    ∀ᶠ s in 𝓝 s₀, ∀ y ∈ K, FibreFlatAt A (s, y) :=
  eventually_forall_mem_of_isOpen hK (isOpen_fibreFlatAt A) h

end Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
