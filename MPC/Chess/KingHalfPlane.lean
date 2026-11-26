import MPC.Chess.RayIntersection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Open half-planes bounded by the line through two kings. Directions are
classified by a cross product, without computing real angles. -/

namespace MPC.Chess

inductive HalfPlaneSide where
  | positive | negative
  deriving DecidableEq, Repr

instance : Fintype HalfPlaneSide :=
  ⟨{.positive, .negative}, fun s => by cases s <;> simp⟩

def HalfPlaneSide.sign : HalfPlaneSide → ℚ | .positive => 1 | .negative => -1

def HalfPlaneSide.opposite : HalfPlaneSide → HalfPlaneSide
  | .positive => .negative | .negative => .positive

def halfPlaneCross (K L p : PlanePoint) : ℚ :=
  (L.1 - K.1) * (p.2 - K.2) - (L.2 - K.2) * (p.1 - K.1)

/-- The boundary is excluded from both sides. -/
def InKingHalfPlane (K L : PlanePoint) (side : HalfPlaneSide) (p : PlanePoint) : Prop :=
  0 < side.sign * halfPlaneCross K L p

instance (K L : PlanePoint) (side : HalfPlaneSide) (p : PlanePoint) :
    Decidable (InKingHalfPlane K L side p) := inferInstanceAs (Decidable (0 < _))

/-- Directions into a fixed global side, usable from either boundary king. -/
def halfPlaneDirections (K L : PlanePoint) (side : HalfPlaneSide) : Finset RayDirection :=
  Finset.univ.filter fun d => 0 < side.sign * rayOffset K L d

theorem halfPlaneCross_rayPoint (K L a : PlanePoint) (d : RayDirection) (t : ℚ) :
    halfPlaneCross K L (rayPoint a d t) = halfPlaneCross K L a + t * rayOffset K L d := by
  unfold halfPlaneCross rayPoint rayOffset
  ring

theorem inKingHalfPlane_swap_iff (K L p : PlanePoint) (side : HalfPlaneSide) :
    InKingHalfPlane L K side.opposite p ↔ InKingHalfPlane K L side p := by
  have h : halfPlaneCross L K p = -halfPlaneCross K L p := by unfold halfPlaneCross; ring
  cases side <;> simp [InKingHalfPlane, HalfPlaneSide.opposite, HalfPlaneSide.sign, h]

/-- Exactly the points off the boundary belong to a unique side. -/
theorem exists_unique_kingHalfPlane_iff (K L p : PlanePoint) :
    (∃! side, InKingHalfPlane K L side p) ↔ halfPlaneCross K L p ≠ 0 := by
  constructor
  · rintro ⟨side, hs, _⟩ he
    simp [InKingHalfPlane, he] at hs
  · intro h
    rcases lt_or_gt_of_ne h with hn | hp
    · refine ⟨.negative, by simpa [InKingHalfPlane, HalfPlaneSide.sign] using hn, ?_⟩
      intro side hs
      cases side
      · simp [InKingHalfPlane, HalfPlaneSide.sign] at hs; linarith
      · rfl
    · refine ⟨.positive, by simpa [InKingHalfPlane, HalfPlaneSide.sign] using hp, ?_⟩
      intro side hs
      cases side
      · rfl
      · simp [InKingHalfPlane, HalfPlaneSide.sign] at hs; linarith

/-- Every positive point on the ray from a boundary origin has the same side
as its direction. The zero parameter is deliberately not covered. -/
theorem inKingHalfPlane_rayPoint_iff (K L a : PlanePoint) (side : HalfPlaneSide)
    (d : RayDirection) (t : ℚ) (ha : halfPlaneCross K L a = 0) (ht : 0 < t) :
    InKingHalfPlane K L side (rayPoint a d t) ↔ d ∈ halfPlaneDirections K L side := by
  simp only [InKingHalfPlane, halfPlaneCross_rayPoint, ha, zero_add,
    halfPlaneDirections, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show side.sign * (t * rayOffset K L d) = t * (side.sign * rayOffset K L d) by ring]
  exact mul_pos_iff_of_pos_left ht

theorem OnRationalRay.inKingHalfPlane_iff {K L a p : PlanePoint} {d : RayDirection}
    (hr : OnRationalRay a d p) (ha : halfPlaneCross K L a = 0) (hne : p ≠ a)
    (side : HalfPlaneSide) :
    InKingHalfPlane K L side p ↔ d ∈ halfPlaneDirections K L side := by
  have ht : 0 < rayParameter a d p := by
    refine lt_of_le_of_ne hr.1 ?_
    intro he
    apply hne
    simpa only [← he, rayPoint_zero] using hr.2
  conv_lhs => rw [hr.2]
  exact inKingHalfPlane_rayPoint_iff K L a side d _ ha ht

private theorem direction_count (x y : ℚ) (hn : x ≠ 0 ∨ y ≠ 0) :
    (Finset.univ.filter fun d : RayDirection => 0 < x * d.vector.2 - y * d.vector.1).card = 3 ∨
    (Finset.univ.filter fun d : RayDirection => 0 < x * d.vector.2 - y * d.vector.1).card = 4 := by
  have hu : (Finset.univ : Finset RayDirection) =
      {.north, .northEast, .east, .southEast, .south, .southWest, .west, .northWest} := by decide
  simp [Finset.card_filter, hu, RayDirection.vector]
  have pair (a b : ℚ) :
      (if a < b then 1 else 0) + (if b < a then 1 else 0) = (if a = b then 0 else 1 : ℕ) := by
    rcases lt_trichotomy a b with h | h | h
    · simp [h, not_lt.mpr h.le, ne_of_lt h]
    · simp [h]
    · simp [h, not_lt.mpr h.le, ne_of_gt h]
  have hx := pair 0 x
  have hy := pair y 0
  have hd := pair y x
  have ha := pair y (-x)
  simp only [show (-x < y) ↔ (-y < x) by constructor <;> intro h <;> linarith] at ha
  suffices h :
      (if 0 = x then 0 else 1) + (if y = 0 then 0 else 1) +
        (if y = x then 0 else 1) + (if y = -x then 0 else 1 : ℕ) = 3 ∨
      (if 0 = x then 0 else 1) + (if y = 0 then 0 else 1) +
        (if y = x then 0 else 1) + (if y = -x then 0 else 1 : ℕ) = 4 by omega
  split_ifs <;> first
    | omega
    | (exfalso; rcases hn with hn | hn <;> apply hn <;> linarith)

/-- A nonzero line leaves three or four queen directions in either open
half-plane. No board-boundary clipping is applied to these rational rays. -/
theorem halfPlaneDirections_card_three_or_four (K L : PlanePoint) (hne : K ≠ L)
    (side : HalfPlaneSide) :
    (halfPlaneDirections K L side).card = 3 ∨ (halfPlaneDirections K L side).card = 4 := by
  have hxy : side.sign * (L.1 - K.1) ≠ 0 ∨ side.sign * (L.2 - K.2) ≠ 0 := by
    by_contra! he
    apply hne
    cases side <;> simp [HalfPlaneSide.sign] at he <;>
      exact Prod.ext (by linarith [he.1]) (by linarith [he.2])
  have h := direction_count (side.sign * (L.1 - K.1)) (side.sign * (L.2 - K.2)) hxy
  have hf : halfPlaneDirections K L side = Finset.univ.filter
      (fun d : RayDirection => 0 < (side.sign * (L.1 - K.1)) * d.vector.2 -
        (side.sign * (L.2 - K.2)) * d.vector.1) := by
    unfold halfPlaneDirections
    congr 1
    funext d
    unfold rayOffset
    congr 1; ring
  simpa only [← hf] using h

end MPC.Chess
