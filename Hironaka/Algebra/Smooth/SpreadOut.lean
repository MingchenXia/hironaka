/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalRing.Module

/-!
# Spreading out generators of the Kähler differentials from a point

Let `k → S` be an algebra and `v_0, …, v_{n-1} ∈ S`. Two Nakayama-type statements used to pass
from the stalk at a point to a neighbourhood (the "shrink `U`" step in producing étale coordinates
on a smooth scheme, `Hironaka/Scheme/Smooth/EtaleCoordinates.lean`):

* `exists_smul_mem_span_of_localized`: if the `d v_i` generate `Ω[T⁄k]` for a localization `T` of
  `S` at a submonoid `M`, then every `ω ∈ Ω[S⁄k]` has a multiple `s • ω`, `s ∈ M`, in the span of
  the `d v_i` (the span of the `d v_i` localizes to the span of their images, Mathlib's
  `Submodule.localized'_span`, and `Ω[T⁄k]` is the localized module of `Ω[S⁄k]`,
  `KaehlerDifferential.isLocalizedModule_map`);
* `exists_mem_forall_smul_mem_span`: for `Ω[S⁄k]` finitely generated, one `s ∈ M` works for all
  `ω` (the product of the multipliers of finitely many generators);
* `span_eq_top_of_forall_smul_mem`: if `s • Ω[S⁄k]` lies in the span of the `d v_i`, then the
  `d v_i` generate `Ω[S'⁄k]` for the localization `S' = S[1/s]`;
* `span_eq_top_of_basis_tensor`: Nakayama at a local ring `T`: if the classes `1 ⊗ d v_i` form a
  basis of `κ ⊗_T Ω[T⁄k]`, the `d v_i` generate `Ω[T⁄k]`
  (`IsLocalRing.span_eq_top_of_tmul_eq_basis`).

Routine commutative algebra, not stated as such in the sources (the localization of a finitely
generated module, [Sta, Tag 00DQ], and Nakayama's lemma).
-/

public section

namespace Algebra

open KaehlerDifferential _root_.TensorProduct

universe u

variable {k S T : Type u} [CommRing k] [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
  [Algebra S T] [IsScalarTower k S T]

/-- The image under `Ω[S⁄k] → Ω[T⁄k]` of the differentials of the `v i` are the differentials of
their images. -/
theorem map_image_range_D {ι : Type*} (v : ι → S) :
    KaehlerDifferential.map k k S T '' (Set.range fun i => D k S (v i)) =
      Set.range fun i => D k T (algebraMap S T (v i)) := by
  ext w
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by rw [KaehlerDifferential.map_D]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, by rw [KaehlerDifferential.map_D]⟩

/-- If the `d v_i` generate `Ω[T⁄k]` for the localization `T = S[M⁻¹]`, every `ω ∈ Ω[S⁄k]` has a
multiple `s • ω`, `s ∈ M`, in the span of the `d v_i`. -/
theorem exists_smul_mem_span_of_localized (M : Submonoid S) [IsLocalization M T] {ι : Type*}
    (v : ι → S) (h : Submodule.span T (Set.range fun i => D k T (algebraMap S T (v i))) = ⊤)
    (ω : Ω[S⁄k]) : ∃ s ∈ M, s • ω ∈ Submodule.span S (Set.range fun i => D k S (v i)) := by
  set P := Submodule.span S (Set.range fun i => D k S (v i)) with hPdef
  have hP : P.localized' T M (KaehlerDifferential.map k k S T) = ⊤ := by
    rw [hPdef, Submodule.localized'_span, map_image_range_D, h]
  have hmem : KaehlerDifferential.map k k S T ω ∈
      P.localized' T M (KaehlerDifferential.map k k S T) := hP ▸ Submodule.mem_top
  rw [Submodule.mem_localized'] at hmem
  obtain ⟨m, hm, s, hs⟩ := hmem
  rw [← IsLocalizedModule.mk'_one M (KaehlerDifferential.map k k S T) ω,
    IsLocalizedModule.mk'_eq_mk'_iff] at hs
  obtain ⟨c, hc⟩ := hs
  refine ⟨c.1 * s.1, M.mul_mem c.2 s.2, ?_⟩
  rw [mul_smul]
  change c.1 • s.1 • ω ∈ P
  rw [← Submonoid.smul_def, ← Submonoid.smul_def, hc, one_smul]
  exact P.smul_mem _ hm

/-- One multiplier for all of `Ω[S⁄k]` when it is finitely generated. -/
theorem exists_mem_forall_smul_mem_span (M : Submonoid S) [IsLocalization M T]
    [Module.Finite S Ω[S⁄k]] {ι : Type*} (v : ι → S)
    (h : Submodule.span T (Set.range fun i => D k T (algebraMap S T (v i))) = ⊤) :
    ∃ s ∈ M, ∀ ω : Ω[S⁄k], s • ω ∈ Submodule.span S (Set.range fun i => D k S (v i)) := by
  classical
  set P := Submodule.span S (Set.range fun i => D k S (v i))
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := S) (M := Ω[S⁄k])
  have key : ∀ j : Fin m, ∃ s ∈ M, s • g j ∈ P := fun j =>
    exists_smul_mem_span_of_localized M v h (g j)
  choose sf hsM hsP using key
  refine ⟨∏ j, sf j, M.prod_mem fun j _ => hsM j, fun ω => ?_⟩
  have hω : ω ∈ Submodule.span S (Set.range g) := hg ▸ Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨j, rfl⟩ := hω
    rw [← Finset.mul_prod_erase Finset.univ sf (Finset.mem_univ j), mul_comm, mul_smul]
    exact P.smul_mem _ (hsP j)
  | zero => rw [smul_zero]; exact P.zero_mem
  | add a b _ _ ha hb => rw [smul_add]; exact P.add_mem ha hb
  | smul r a _ ha => rw [smul_comm]; exact P.smul_mem r ha

/-- If `s • Ω[S⁄k]` lies in the span of the `d v_i`, the `d v_i` generate `Ω[S'⁄k]` for the
localization `S' = S[1/s]` (or any localization at a submonoid containing `s`). -/
theorem span_eq_top_of_forall_smul_mem {S' : Type u} [CommRing S'] [Algebra k S'] [Algebra S S']
    [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S'] {ι : Type*} (v : ι → S)
    {s : S} (hs : s ∈ M)
    (h : ∀ ω : Ω[S⁄k], s • ω ∈ Submodule.span S (Set.range fun i => D k S (v i))) :
    Submodule.span S' (Set.range fun i => D k S' (algebraMap S S' (v i))) = ⊤ := by
  set P := Submodule.span S (Set.range fun i => D k S (v i)) with hPdef
  have hP : P.localized' S' M (KaehlerDifferential.map k k S S') = ⊤ := by
    rw [_root_.eq_top_iff]
    rintro w -
    obtain ⟨⟨ω, t⟩, hw⟩ := IsLocalizedModule.mk'_surjective M (KaehlerDifferential.map k k S S') w
    rw [Submodule.mem_localized']
    refine ⟨(⟨s, hs⟩ : M) • ω, ?_, ⟨s, hs⟩ * t, ?_⟩
    · rw [Submonoid.smul_def]
      exact h ω
    · rw [IsLocalizedModule.mk'_cancel_left]
      exact hw
  rwa [hPdef, Submodule.localized'_span, map_image_range_D] at hP

end Algebra

namespace Algebra

open KaehlerDifferential _root_.TensorProduct

universe v

variable {k S T : Type v} [CommRing k] [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
  [Algebra S T] [IsScalarTower k S T]

/-- `Ω[T⁄k]` is a finite `T`-module when `Ω[S⁄k]` is a finite `S`-module and `T` is a localization
of `S` (it is the base change `T ⊗_S Ω[S⁄k]`). -/
theorem finite_kaehlerDifferential_of_isLocalization (M : Submonoid S) [IsLocalization M T]
    [Module.Finite S Ω[S⁄k]] : Module.Finite T Ω[T⁄k] :=
  Module.Finite.equiv (IsLocalizedModule.isBaseChange M T (KaehlerDifferential.map k k S T)).equiv

omit [Algebra k S] [IsScalarTower k S T] in
/-- Nakayama at a local ring `T`: if the classes `1 ⊗ d v_i` form a basis of `κ ⊗_T Ω[T⁄k]`, the
`d v_i` generate `Ω[T⁄k]`. -/
theorem span_eq_top_of_basis_tensor [IsLocalRing T] [Module.Finite T Ω[T⁄k]] {ι : Type*}
    (v : ι → S)
    (b : Module.Basis ι (IsLocalRing.ResidueField T) (IsLocalRing.ResidueField T ⊗[T] Ω[T⁄k]))
    (hb : ∀ i, b i = 1 ⊗ₜ D k T (algebraMap S T (v i))) :
    Submodule.span T (Set.range fun i => D k T (algebraMap S T (v i))) = ⊤ :=
  IsLocalRing.span_eq_top_of_tmul_eq_basis _ b fun i => (hb i).symm

end Algebra
