import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

/-!
# Two-sided perturbations in finite boxes

A direction that vanishes on all active coordinate bounds admits a uniformly
small positive step in both directions. The bounds can be arbitrary real
numbers; no integrality or unimodularity assumption is needed here.

The accompanying extreme-point lemmas turn a nonzero feasible two-sided
direction into a contradiction, also after applying a linear projection.
-/

noncomputable section

namespace TropicalCurves
namespace UnitBoxPerturbation

/-- A finite collection of strictly positive real numbers has a strictly
positive common lower bound. The empty index type is allowed. -/
theorem exists_pos_le_all {J : Type*} [Fintype J] (r : J → ℝ)
    (hr : ∀ j, 0 < r j) : ∃ ε : ℝ, 0 < ε ∧ ∀ j, ε ≤ r j := by
  classical
  cases isEmpty_or_nonempty J with
  | inl hJ => exact ⟨1, by norm_num, fun j => isEmptyElim j⟩
  | inr hJ =>
    refine ⟨Finset.univ.inf' Finset.univ_nonempty r, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff _).2 (fun j _ => hr j)
    · intro j
      exact Finset.inf'_le r (Finset.mem_univ j)

/-- Every direction supported away from the active bounds admits a common
positive step in both directions within a finite coordinate box. -/
theorem exists_two_sided_box_perturbation {J : Type*} [Fintype J]
    {lower upper u d : J → ℝ}
    (hu : ∀ j, lower j ≤ u j ∧ u j ≤ upper j)
    (hd : ∀ j, u j = lower j ∨ u j = upper j → d j = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ j, lower j ≤ u j + ε * d j ∧ u j + ε * d j ≤ upper j) ∧
      (∀ j, lower j ≤ u j - ε * d j ∧ u j - ε * d j ≤ upper j) := by
  classical
  let r : J → ℝ := fun j =>
    if d j = 0 then 1 else min (u j - lower j) (upper j - u j) / (|d j| + 1)
  have hr : ∀ j, 0 < r j := by
    intro j
    dsimp [r]
    split_ifs with hj
    · norm_num
    · have hl : lower j < u j := lt_of_le_of_ne (hu j).1
        (fun h => hj (hd j (Or.inl h.symm)))
      have hh : u j < upper j := lt_of_le_of_ne (hu j).2
        (fun h => hj (hd j (Or.inr h)))
      apply div_pos (lt_min (sub_pos.mpr hl) (sub_pos.mpr hh))
      linarith [abs_nonneg (d j)]
  obtain ⟨ε, hε, hεr⟩ := exists_pos_le_all r hr
  have hbound : ∀ j, |ε * d j| ≤ min (u j - lower j) (upper j - u j) := by
    intro j
    by_cases hj : d j = 0
    · simp only [hj, mul_zero, abs_zero, le_min_iff]
      exact ⟨sub_nonneg.mpr (hu j).1, sub_nonneg.mpr (hu j).2⟩
    · have hden : 0 < |d j| + 1 := by linarith [abs_nonneg (d j)]
      have hrj : ε ≤ min (u j - lower j) (upper j - u j) / (|d j| + 1) := by
        simpa [r, hj] using hεr j
      have hmul := (le_div_iff₀ hden).mp hrj
      rw [abs_mul, abs_of_pos hε]
      nlinarith
  refine ⟨ε, hε, ?_, ?_⟩
  · intro j
    have hlow := (abs_le.mp (hbound j)).1
    have hupp := (abs_le.mp (hbound j)).2
    have hleft := min_le_left (u j - lower j) (upper j - u j)
    have hright := min_le_right (u j - lower j) (upper j - u j)
    constructor <;> linarith
  · intro j
    have hlow := (abs_le.mp (hbound j)).1
    have hupp := (abs_le.mp (hbound j)).2
    have hleft := min_le_left (u j - lower j) (upper j - u j)
    have hright := min_le_right (u j - lower j) (upper j - u j)
    constructor <;> linarith

/-- The unit coordinate cube, including its boundary. -/
def unitCube (J : Type*) : Set (J → ℝ) :=
  {u | ∀ j, 0 ≤ u j ∧ u j ≤ 1}

/-- Unit-cube version of the finite-box perturbation lemma. -/
theorem exists_two_sided_perturbation {J : Type*} [Fintype J]
    {u d : J → ℝ} (hu : u ∈ unitCube J)
    (hd : ∀ j, u j = 0 ∨ u j = 1 → d j = 0) :
    ∃ ε : ℝ, 0 < ε ∧ u + ε • d ∈ unitCube J ∧ u - ε • d ∈ unitCube J := by
  exact exists_two_sided_box_perturbation hu hd

/-- A point is the midpoint of two opposite scalar perturbations. -/
theorem mem_openSegment_add_sub_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (u d : E) (ε : ℝ) :
    u ∈ openSegment ℝ (u + ε • d) (u - ε • d) := by
  refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
  calc
    (1 / 2 : ℝ) • (u + ε • d) + (1 / 2 : ℝ) • (u - ε • d) =
        ((1 / 2 : ℝ) + 1 / 2) • u := by
          simp only [smul_add, smul_sub, add_smul]
          abel
    _ = u := by norm_num

/-- A nonzero feasible two-sided direction rules out extremality. -/
theorem not_extreme_of_two_sided_perturbation
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {u d : E} {ε : ℝ}
    (hε : 0 < ε) (hd : d ≠ 0)
    (hplus : u + ε • d ∈ S) (hminus : u - ε • d ∈ S) :
    u ∉ S.extremePoints ℝ := by
  intro hext
  have h := (hext.2 hplus hminus (mem_openSegment_add_sub_smul u d ε)).1
  have hz : ε • d = 0 := by simpa only [add_eq_left] using h
  exact hd ((smul_eq_zero.mp hz).resolve_left hε.ne')

/-- The same criterion applies after linear projection, provided the projected
direction is nonzero. Membership is needed only in the projected set. -/
theorem not_extreme_of_projected_two_sided_perturbation
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E →ₗ[ℝ] F) {S : Set F} {u d : E} {ε : ℝ}
    (hε : 0 < ε) (hd : f d ≠ 0)
    (hplus : f (u + ε • d) ∈ S) (hminus : f (u - ε • d) ∈ S) :
    f u ∉ S.extremePoints ℝ := by
  apply not_extreme_of_two_sided_perturbation hε hd
  · simpa only [map_add, map_smul] using hplus
  · simpa only [map_sub, map_smul] using hminus

end UnitBoxPerturbation
end TropicalCurves
