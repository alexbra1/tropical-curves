import TropicalCurves.UnitAbelMap

/-!
# Recognizing arbitrary real-length models with unit edges

A `RealLengthGraph` whose lengths are all one is equal to the canonical
unit-length realization of its endpoint graph. Consequently the unit-length
Abel-map theorems apply to arbitrary presentations satisfying the unit-length
hypothesis, rather than only to models constructed by `unitGraph`.

The point and edge-product equivalences retain vertices, edge labels and real
coordinates. The graph equality also permits direct transport of divisor
constructions and all dependent statements.
-/

namespace TropicalCurves
namespace UnitLengthModel

open FiniteStability UnitAbelMap

variable {V E : Type*}

/-- Forget lengths while retaining both oriented endpoint maps. -/
def endpointGraph (G : RealLengthGraph V E) : EndpointGraph V E where
  source := G.source
  target := G.target

/-- Every edge of the given real-length model has length one. -/
def IsUnit (G : RealLengthGraph V E) : Prop := ∀ e, G.length e = 1

@[simp] theorem endpointGraph_source (G : RealLengthGraph V E) (e : E) :
    (endpointGraph G).source e = G.source e := rfl

@[simp] theorem endpointGraph_target (G : RealLengthGraph V E) (e : E) :
    (endpointGraph G).target e = G.target e := rfl

/-- Canonical unit realizations satisfy the unit-length condition. -/
@[simp] theorem unitGraph_isUnit (G : EndpointGraph V E) : IsUnit (unitGraph G) :=
  fun _ => rfl

@[simp] theorem endpointGraph_unitGraph (G : EndpointGraph V E) :
    endpointGraph (unitGraph G) = G := by
  cases G
  rfl

/-- A real-length graph with unit lengths is exactly the canonical realization
of its own endpoint graph. Positivity proof fields agree by proof irrelevance. -/
theorem eq_unitGraph_endpointGraph (G : RealLengthGraph V E) (hG : IsUnit G) :
    G = unitGraph (endpointGraph G) := by
  cases G with
  | mk source target length length_pos =>
    have hlength : length = fun _ => (1 : ℝ) := funext hG
    subst length
    rfl

/-- Equality with the canonical unit model is equivalent to the explicit
unit-length hypothesis. -/
theorem isUnit_iff_eq_unitGraph_endpointGraph (G : RealLengthGraph V E) :
    IsUnit G ↔ G = unitGraph (endpointGraph G) := by
  constructor
  · exact eq_unitGraph_endpointGraph G
  · intro h
    have hu := unitGraph_isUnit (endpointGraph G)
    rwa [← h] at hu

/-- The unit-length models are precisely the canonical realizations of
endpoint graphs. -/
theorem isUnit_iff_exists_unitGraph (G : RealLengthGraph V E) :
    IsUnit G ↔ ∃ H : EndpointGraph V E, G = unitGraph H := by
  constructor
  · intro hG
    exact ⟨endpointGraph G, eq_unitGraph_endpointGraph G hG⟩
  · rintro ⟨H, rfl⟩
    exact unitGraph_isUnit H

/-- Equality of real-length graph structures gives a point-set equivalence. -/
def transportPointEquiv {G H : RealLengthGraph V E} (h : G = H) : G.Point ≃ H.Point := by
  subst H
  exact Equiv.refl _

@[simp] theorem transportPointEquiv_vertex {G H : RealLengthGraph V E}
    (h : G = H) (v : V) : transportPointEquiv h (G.vertex v) = H.vertex v := by
  subst H
  rfl

/-- Identify the points of an arbitrary unit-length model with the points of
its canonical unit realization. -/
def pointEquivToUnit (G : RealLengthGraph V E) (hG : IsUnit G) :
    G.Point ≃ (unitGraph (endpointGraph G)).Point :=
  transportPointEquiv (eq_unitGraph_endpointGraph G hG)

@[simp] theorem pointEquivToUnit_vertex (G : RealLengthGraph V E)
    (hG : IsUnit G) (v : V) :
    pointEquivToUnit G hG (G.vertex v) = (unitGraph (endpointGraph G)).vertex v :=
  transportPointEquiv_vertex _ v

/-- The products of specified edges are equivalent by retaining every real
coordinate. Repeated edges and empty products are permitted. -/
def edgeProductEquivToUnit (G : RealLengthGraph V E) (hG : IsUnit G)
    {I : Type*} (edges : I → E) :
    G.EdgeProduct edges ≃ (unitGraph (endpointGraph G)).EdgeProduct edges where
  toFun x i := ⟨(x i : ℝ), by simpa only [unitGraph_length, hG (edges i)] using (x i).property⟩
  invFun x i := ⟨(x i : ℝ), by simpa only [unitGraph_length, hG (edges i)] using (x i).property⟩
  left_inv x := by
    funext i
    apply Subtype.ext
    rfl
  right_inv x := by
    funext i
    apply Subtype.ext
    rfl

@[simp] theorem edgeProductEquivToUnit_coordinate (G : RealLengthGraph V E) (hG : IsUnit G)
    {I : Type*} (edges : I → E) (x : G.EdgeProduct edges) (i : I) :
    (edgeProductEquivToUnit G hG edges x i : ℝ) = (x i : ℝ) := rfl

@[simp] theorem edgeProductEquivToUnit_symm_coordinate (G : RealLengthGraph V E)
    (hG : IsUnit G) {I : Type*} (edges : I → E)
    (x : (unitGraph (endpointGraph G)).EdgeProduct edges) (i : I) :
    ((edgeProductEquivToUnit G hG edges).symm x i : ℝ) = (x i : ℝ) := rfl

end UnitLengthModel
end TropicalCurves
