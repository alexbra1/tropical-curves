import Mathlib.Analysis.Normed.Group.AddCircle
import TropicalCurves.UnitBoxPerturbation
import TropicalCurves.UnitCube
import Mathlib.Tactic.Ring

/-!
# Integrality of projected unit-edge flow polytopes

Slots may repeat graph edges. Each slot has coefficient `+1` or `-1`, is
bounded by zero and one, and participates in the row belonging to its edge.
Rows differ from vertex-potential differences by prescribed integers.
The projected extreme points have only zero and one coordinates, including
after imposing any collection of source-coordinate faces.
-/

noncomputable section

namespace TropicalCurves
namespace UnitFlowPolytope

open UnitBoxPerturbation

variable {J E V I : Type*} [Fintype J] [DecidableEq J] [DecidableEq E]

/-- Signed slot sum on one graph edge. Repeated edge assignments are allowed. -/
def slotRow (edge : J → E) (sign : J → ℤ) (u : J → ℝ) (e : E) : ℝ :=
  ∑ j, if edge j = e then (sign j : ℝ) * u j else 0

/-- All edge rows as a linear map. -/
def rowMap (edge : J → E) (sign : J → ℤ) : (J → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := slotRow edge sign
  map_add' u v := by
    classical
    funext e
    simp only [slotRow, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : edge j = e <;> simp [h, mul_add]
  map_smul' r u := by
    classical
    funext e
    simp only [slotRow, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : edge j = e <;> simp [h, mul_left_comm]

/-- Projection onto any selected slots; the selection need not be injective. -/
def projection (selected : I → J) : (J → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun u := u ∘ selected
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Optional endpoint conditions defining a source face. -/
def OnSourceFace (face : I → Option Bool) (x : I → ℝ) : Prop :=
  ∀ i b, face i = some b → x i = if b then 1 else 0

/-- The projected flow polytope with slot signs and source-face conditions.
Source and target slots on the same edge may carry opposite signs. -/
def projectedSlots (source target : E → V) (edge : J → E) (sign : J → ℤ)
    (z : E → ℤ) (selected : I → J) (face : I → Option Bool) : Set (I → ℝ) :=
  {x | ∃ u : J → ℝ, u ∈ unitCube J ∧
    (∃ p : V → ℝ, ∀ e, slotRow edge sign u e =
      (z e : ℝ) + p (target e) - p (source e)) ∧
    projection selected u = x ∧ OnSourceFace face x}


/-- The residue class of a real potential modulo integers. -/
private def residueClass (x : ℝ) : AddCircle (1 : ℝ) := (x : AddCircle (1 : ℝ))

/-- Potential residues agree exactly when their difference is integral. -/
private theorem residueClass_eq_iff (x y : ℝ) :
    residueClass x = residueClass y ↔ ∃ n : ℤ, x - y = (n : ℝ) := by
  change (x : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)) ↔ _
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn.symm⟩

private def IsIntegral (x : ℝ) : Prop := ∃ n : ℤ, x = (n : ℝ)

omit [DecidableEq J] in
private theorem integral_sum (f : J → ℝ) (hf : ∀ j, IsIntegral (f j)) :
    IsIntegral (∑ j, f j) := by
  classical
  choose g hg using hf
  refine ⟨∑ j, g j, ?_⟩
  simp_rw [hg]
  simp

private theorem boundary_of_integral {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1)
    (hi : IsIntegral x) : x = 0 ∨ x = 1 := by
  rcases hi with ⟨n, rfl⟩
  have hn0 : 0 ≤ n := by exact_mod_cast hx.1
  have hn1 : n ≤ 1 := by exact_mod_cast hx.2
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl <;> simp

private theorem integral_signed_boundary (s : ℤ) {x : ℝ} (hx : x = 0 ∨ x = 1) :
    IsIntegral ((s : ℝ) * x) := by
  rcases hx with rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨s, by simp⟩

private theorem integral_of_signed {s : ℤ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : IsIntegral ((s : ℝ) * x)) : IsIntegral x := by
  rcases hx with ⟨n, hn⟩
  rcases hs with rfl | rfl
  · exact ⟨n, by simpa using hn⟩
  · refine ⟨-n, ?_⟩
    push_cast
    norm_num at hn
    linarith

private theorem sign_sq {s : ℤ} (hs : s = 1 ∨ s = -1) :
    (s : ℝ) * (s : ℝ) = 1 := by
  rcases hs with rfl | rfl <;> norm_num

private theorem sign_ne_zero {s : ℤ} (hs : s = 1 ∨ s = -1) : (s : ℝ) ≠ 0 := by
  rcases hs with rfl | rfl <;> norm_num

private theorem row_decompose (edge : J → E) (sign : J → ℤ) (u : J → ℝ)
    (e : E) (j₀ : J) :
    slotRow edge sign u e =
      (if edge j₀ = e then (sign j₀ : ℝ) * u j₀ else 0) +
      ∑ j, if j = j₀ then 0 else if edge j = e then (sign j : ℝ) * u j else 0 := by
  classical
  calc
    slotRow edge sign u e = ∑ j,
        ((if j = j₀ then (if edge j₀ = e then (sign j₀ : ℝ) * u j₀ else 0) else 0) +
          (if j = j₀ then 0 else if edge j = e then (sign j : ℝ) * u j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = j₀ <;> simp [hj]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

omit [DecidableEq J] in
private theorem color_eq_of_boundary_rows (source target : E → V) (edge : J → E)
    (sign : J → ℤ) (z : E → ℤ) (u : J → ℝ) (p : V → ℝ)
    (hflow : ∀ e, slotRow edge sign u e = (z e : ℝ) + p (target e) - p (source e))
    (e : E) (hb : ∀ j, edge j = e → u j = 0 ∨ u j = 1) :
    residueClass (p (target e)) = residueClass (p (source e)) := by
  classical
  obtain ⟨n, hn⟩ : IsIntegral (slotRow edge sign u e) := by
    apply integral_sum
    intro j
    by_cases hj : edge j = e
    · simpa [hj] using integral_signed_boundary (sign j) (hb j hj)
    · exact ⟨0, by simp [hj]⟩
  apply (residueClass_eq_iff _ _).2
  refine ⟨n - z e, ?_⟩
  push_cast
  have he := hflow e
  linarith

private theorem color_ne_of_unique_fractional (source target : E → V) (edge : J → E)
    (sign : J → ℤ) (hsign : ∀ j, sign j = 1 ∨ sign j = -1)
    (z : E → ℤ) (u : J → ℝ) (hu : u ∈ unitCube J) (p : V → ℝ)
    (hflow : ∀ e, slotRow edge sign u e = (z e : ℝ) + p (target e) - p (source e))
    (j₀ : J) (hj₀ : ¬ (u j₀ = 0 ∨ u j₀ = 1))
    (hunique : ∀ j, edge j = edge j₀ → j ≠ j₀ → u j = 0 ∨ u j = 1) :
    residueClass (p (target (edge j₀))) ≠ residueClass (p (source (edge j₀))) := by
  classical
  intro hcolor
  obtain ⟨n, hn⟩ := (residueClass_eq_iff _ _).mp hcolor
  obtain ⟨m, hm⟩ : IsIntegral
      (∑ j, if j = j₀ then 0 else
        if edge j = edge j₀ then (sign j : ℝ) * u j else 0) := by
    apply integral_sum
    intro j
    by_cases hj : j = j₀
    · exact ⟨0, by simp [hj]⟩
    · by_cases he : edge j = edge j₀
      · simpa [hj, he] using integral_signed_boundary (sign j) (hunique j he hj)
      · exact ⟨0, by simp [hj, he]⟩
  apply hj₀
  apply boundary_of_integral (hu j₀)
  apply integral_of_signed (hsign j₀)
  refine ⟨z (edge j₀) + n - m, ?_⟩
  have hrow := row_decompose edge sign u (edge j₀) j₀
  simp only [ite_true] at hrow
  have he := hflow (edge j₀)
  push_cast
  linarith

private def signedBasis (sign : J → ℤ) (j₀ : J) : J → ℝ :=
  fun j => if j = j₀ then (sign j₀ : ℝ) else 0

private theorem row_signedBasis (edge : J → E) (sign : J → ℤ)
    (hsign : ∀ j, sign j = 1 ∨ sign j = -1) (j₀ : J) (e : E) :
    slotRow edge sign (signedBasis sign j₀) e = if edge j₀ = e then 1 else 0 := by
  classical
  rw [slotRow, Finset.sum_eq_single j₀]
  · by_cases he : edge j₀ = e <;> simp [signedBasis, he, sign_sq (hsign j₀)]
  · intro j _ hj
    simp [signedBasis, hj]
  · simp

/-- A fractional slot always admits a two-sided feasible direction that
changes that slot. The proof either exchanges two slots on the same edge,
or cuts the vertex set according to potential classes modulo integers. -/
theorem exists_flow_direction (source target : E → V) (edge : J → E)
    (sign : J → ℤ) (hsign : ∀ j, sign j = 1 ∨ sign j = -1)
    (z : E → ℤ) (u : J → ℝ) (hu : u ∈ unitCube J) (p : V → ℝ)
    (hflow : ∀ e, slotRow edge sign u e = (z e : ℝ) + p (target e) - p (source e))
    (j₀ : J) (hj₀ : ¬ (u j₀ = 0 ∨ u j₀ = 1)) :
    ∃ (d : J → ℝ) (q : V → ℝ),
      (∀ j, u j = 0 ∨ u j = 1 → d j = 0) ∧
      (∀ e, slotRow edge sign d e = q (target e) - q (source e)) ∧ d j₀ ≠ 0 := by
  classical
  by_cases hother : ∃ j, edge j = edge j₀ ∧ j ≠ j₀ ∧ ¬ (u j = 0 ∨ u j = 1)
  · obtain ⟨j₁, he, hne, hj₁⟩ := hother
    refine ⟨signedBasis sign j₀ - signedBasis sign j₁, 0, ?_, ?_, ?_⟩
    · intro j hj
      have hn₀ : j ≠ j₀ := by intro h; subst j; exact hj₀ hj
      have hn₁ : j ≠ j₁ := by intro h; subst j; exact hj₁ hj
      simp [signedBasis, hn₀, hn₁]
    · intro e
      change rowMap edge sign (signedBasis sign j₀ - signedBasis sign j₁) e = _
      rw [map_sub]
      change slotRow edge sign (signedBasis sign j₀) e -
        slotRow edge sign (signedBasis sign j₁) e = _
      rw [row_signedBasis edge sign hsign, row_signedBasis edge sign hsign, he]
      simp
    · simpa [signedBasis, Ne.symm hne] using sign_ne_zero (hsign j₀)
  · have hunique : ∀ j, edge j = edge j₀ → j ≠ j₀ → u j = 0 ∨ u j = 1 := by
      intro j he hj
      by_contra hfrac
      exact hother ⟨j, he, hj, hfrac⟩
    have hcolor := color_ne_of_unique_fractional source target edge sign hsign z u hu p
      hflow j₀ hj₀ hunique
    let q : V → ℝ := fun v =>
      if residueClass (p v) = residueClass (p (source (edge j₀))) then 1 else 0
    have hqsource : q (source (edge j₀)) = 1 := by simp [q]
    have hqtarget : q (target (edge j₀)) = 0 := by simp [q, hcolor]
    have hqcross : q (target (edge j₀)) - q (source (edge j₀)) ≠ 0 := by
      rw [hqsource, hqtarget]
      norm_num
    have crossing_fractional : ∀ e, q (target e) - q (source e) ≠ 0 →
        ∃ j, edge j = e ∧ ¬ (u j = 0 ∨ u j = 1) := by
      intro e hcross
      by_contra hnot
      have hb : ∀ j, edge j = e → u j = 0 ∨ u j = 1 := by
        intro j he
        by_contra hfrac
        exact hnot ⟨j, he, hfrac⟩
      have hsame := color_eq_of_boundary_rows source target edge sign z u p hflow e hb
      have hq : q (target e) = q (source e) := by
        simp only [q, hsame]
      exact hcross (sub_eq_zero.mpr hq)
    let pick : E → J := fun e =>
      if h : q (target e) - q (source e) ≠ 0 then
        (crossing_fractional e h).choose else j₀
    have hpick : ∀ e, q (target e) - q (source e) ≠ 0 →
        edge (pick e) = e ∧ ¬ (u (pick e) = 0 ∨ u (pick e) = 1) := by
      intro e hcross
      simp only [pick, dif_pos hcross]
      exact (crossing_fractional e hcross).choose_spec
    let d : J → ℝ := fun j =>
      if pick (edge j) = j then
        (sign j : ℝ) * (q (target (edge j)) - q (source (edge j))) else 0
    refine ⟨d, q, ?_, ?_, ?_⟩
    · intro j hj
      by_cases hcross : q (target (edge j)) - q (source (edge j)) ≠ 0
      · have hf := (hpick (edge j) hcross).2
        have hneq : pick (edge j) ≠ j := by
          intro heq
          rw [heq] at hf
          exact hf hj
        simp [d, hneq]
      · have hz : q (target (edge j)) - q (source (edge j)) = 0 := not_ne_iff.mp hcross
        simp [d, hz]
    · intro e
      by_cases hcross : q (target e) - q (source e) ≠ 0
      · have he := (hpick e hcross).1
        rw [slotRow, Finset.sum_eq_single (pick e)]
        · simp only [d, he, eq_self_iff_true, ite_true]
          rw [← mul_assoc, sign_sq (hsign (pick e)), one_mul]
        · intro j _ hj
          by_cases hej : edge j = e
          · simp [d, hej, Ne.symm hj]
          · simp [hej]
        · simp
      · have hz : q (target e) - q (source e) = 0 := not_ne_iff.mp hcross
        rw [hz]
        apply Finset.sum_eq_zero
        intro j _
        by_cases hej : edge j = e
        · simp [d, hej, hz]
        · simp [hej]
    · have hp := hpick (edge j₀) hqcross
      have hchosen : pick (edge j₀) = j₀ := by
        by_contra hneq
        exact hp.2 (hunique (pick (edge j₀)) hp.1 hneq)
      simp only [d, hchosen, ite_true]
      exact mul_ne_zero (sign_ne_zero (hsign j₀)) hqcross

omit [DecidableEq J] in
private theorem perturbation_preserves_flow (source target : E → V) (edge : J → E)
    (sign : J → ℤ) (z : E → ℤ) (u d : J → ℝ) (p q : V → ℝ)
    (hflow : ∀ e, slotRow edge sign u e = (z e : ℝ) + p (target e) - p (source e))
    (hdflow : ∀ e, slotRow edge sign d e = q (target e) - q (source e))
    (r : ℝ) :
    ∀ e, slotRow edge sign (u + r • d) e =
      (z e : ℝ) + (p + r • q) (target e) - (p + r • q) (source e) := by
  intro e
  change rowMap edge sign (u + r • d) e = _
  rw [map_add, map_smul]
  change slotRow edge sign u e + r * slotRow edge sign d e = _
  rw [hflow, hdflow]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype J] [DecidableEq J] in
private theorem perturbation_preserves_face (selected : I → J) (face : I → Option Bool)
    (u d : J → ℝ) (hface : OnSourceFace face (projection selected u))
    (hd : ∀ j, u j = 0 ∨ u j = 1 → d j = 0) (r : ℝ) :
    OnSourceFace face (projection selected (u + r • d)) := by
  intro i b hfb
  have hi : u (selected i) = if b then 1 else 0 := hface i b hfb
  have hboundary : u (selected i) = 0 ∨ u (selected i) = 1 := by
    cases b with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  have hid := hd (selected i) hboundary
  change u (selected i) + r * d (selected i) = _
  rw [hid, mul_zero, add_zero]
  exact hi

omit [DecidableEq J] in
private theorem perturbed_projection_mem (source target : E → V) (edge : J → E)
    (sign : J → ℤ) (z : E → ℤ) (selected : I → J) (face : I → Option Bool)
    (u d : J → ℝ) (p q : V → ℝ)
    (hflow : ∀ e, slotRow edge sign u e = (z e : ℝ) + p (target e) - p (source e))
    (hdflow : ∀ e, slotRow edge sign d e = q (target e) - q (source e))
    (hface : OnSourceFace face (projection selected u))
    (hd : ∀ j, u j = 0 ∨ u j = 1 → d j = 0) (r : ℝ)
    (hur : u + r • d ∈ unitCube J) :
    projection selected (u + r • d) ∈ projectedSlots source target edge sign z selected face := by
  refine ⟨u + r • d, hur, ⟨p + r • q, ?_⟩, rfl, ?_⟩
  · exact perturbation_preserves_flow source target edge sign z u d p q hflow hdflow r
  · exact perturbation_preserves_face selected face u d hface hd r

/-- Every coordinate of an extreme projected flow is an endpoint of the unit
interval. Neither edge assignment nor source-slot selection must be injective. -/
theorem extreme_source_coordinate_binary (source target : E → V) (edge : J → E)
    (sign : J → ℤ) (hsign : ∀ j, sign j = 1 ∨ sign j = -1)
    (z : E → ℤ) (selected : I → J) (face : I → Option Bool)
    {x : I → ℝ}
    (hx : x ∈ (projectedSlots source target edge sign z selected face).extremePoints ℝ)
    (i : I) : x i = 0 ∨ x i = 1 := by
  classical
  by_contra hi
  obtain ⟨u, hu, ⟨p, hflow⟩, hux, hface⟩ := hx.1
  subst x
  have hfrac : ¬ (u (selected i) = 0 ∨ u (selected i) = 1) := hi
  obtain ⟨d, q, hd, hdflow, hdi⟩ :=
    exists_flow_direction source target edge sign hsign z u hu p hflow (selected i) hfrac
  obtain ⟨ε, hε, hplus, hminus⟩ := exists_two_sided_perturbation hu hd
  have hproj : projection selected d ≠ 0 := by
    intro hz
    apply hdi
    have hi := congrArg (fun y : I → ℝ => y i) hz
    exact hi
  have hp := perturbed_projection_mem source target edge sign z selected face
    u d p q hflow hdflow hface hd ε hplus
  have hm' : u + (-ε) • d ∈ unitCube J := by
    simpa only [neg_smul, sub_eq_add_neg] using hminus
  have hm := perturbed_projection_mem source target edge sign z selected face
    u d p q hflow hdflow hface hd (-ε) hm'
  have hm'' : projection selected (u - ε • d) ∈
      projectedSlots source target edge sign z selected face := by
    simpa only [neg_smul, sub_eq_add_neg] using hm
  exact (not_extreme_of_projected_two_sided_perturbation
    (projection selected) hε hproj hp hm'') hx

/-- The projected flow cells have no new vertices relative to the source cube,
with `extremePoints` interpreted by mathlib's convex-geometry definition. -/
theorem projectedSlots_no_new_vertices (source target : E → V) (edge : J → E)
    (sign : J → ℤ) (hsign : ∀ j, sign j = 1 ∨ sign j = -1)
    (z : E → ℤ) (selected : I → J) (face : I → Option Bool) :
    (projectedSlots source target edge sign z selected face).extremePoints ℝ ⊆
      (UnitCube.Cube I).extremePoints ℝ := by
  intro x hx
  apply UnitCube.binary_mem_extremePoints_cube
  exact extreme_source_coordinate_binary source target edge sign hsign z selected face hx

omit [DecidableEq J] in
/-- Each projected flow cell lies in its specified source face. -/
theorem projectedSlots_subset_sourceFace (source target : E → V) (edge : J → E)
    (sign : J → ℤ) (z : E → ℤ) (selected : I → J) (face : I → Option Bool) :
    projectedSlots source target edge sign z selected face ⊆ UnitCube.sourceFace face := by
  rintro x ⟨u, hu, _, hux, hface⟩
  subst x
  exact ⟨fun i => hu (selected i), hface⟩

omit [DecidableEq J] in
/-- For a fixed integer lift, the projected feasible set is convex. -/
theorem projectedSlots_convex (source target : E → V) (edge : J → E)
    (sign : J → ℤ) (z : E → ℤ) (selected : I → J) (face : I → Option Bool) :
    Convex ℝ (projectedSlots source target edge sign z selected face) := by
  intro x hx y hy α β hα hβ hsum
  obtain ⟨u, hu, ⟨p, hp⟩, hux, hfx⟩ := hx
  obtain ⟨v, hv, ⟨q, hq⟩, hvy, hfy⟩ := hy
  refine ⟨α • u + β • v, UnitCube.cube_convex J hu hv hα hβ hsum,
    ⟨α • p + β • q, ?_⟩, ?_, ?_⟩
  · intro e
    change rowMap edge sign (α • u + β • v) e = _
    rw [map_add, map_smul, map_smul]
    change α * slotRow edge sign u e + β * slotRow edge sign v e = _
    rw [hp, hq]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      α * ((z e : ℝ) + p (target e) - p (source e)) +
          β * ((z e : ℝ) + q (target e) - q (source e)) =
          (α + β) * (z e : ℝ) +
            (α * p (target e) + β * q (target e)) -
            (α * p (source e) + β * q (source e)) := by ring
      _ = _ := by rw [hsum, one_mul]
  · rw [map_add, map_smul, map_smul, hux, hvy]
  · intro i b hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hfx i b hi, hfy i b hi]
    rw [← add_mul, hsum, one_mul]

end UnitFlowPolytope
end TropicalCurves
