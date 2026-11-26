import MPC.Chess.CheckingRayGeometry
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-! Rational points on queen rays. These rays extend beyond the board and
include non-lattice points and their origins. `OnRay` describes their strict
positive board-square portion. -/

namespace MPC.Chess

abbrev PlanePoint := ℚ × ℚ

def Pos.toPlane (p : Pos) : PlanePoint := (p.toInt.1, p.toInt.2)

def RayDirection.opposite : RayDirection → RayDirection
  | .north => .south | .northEast => .southWest | .east => .west | .southEast => .northWest
  | .south => .north | .southWest => .northEast | .west => .east | .northWest => .southEast

@[simp] theorem RayDirection.opposite_opposite (d : RayDirection) : d.opposite.opposite = d := by
  cases d <;> rfl

@[simp] theorem RayDirection.opposite_ne (d : RayDirection) : d.opposite ≠ d := by
  cases d <;> decide

def rayPoint (o : PlanePoint) (d : RayDirection) (t : ℚ) : PlanePoint :=
  (o.1 + t * d.vector.1, o.2 + t * d.vector.2)

/-- Signed unit-step parameter, even for points not on the supporting line. -/
def rayParameter (o : PlanePoint) (d : RayDirection) (p : PlanePoint) : ℚ :=
  match d with
  | .north => p.2 - o.2
  | .south => o.2 - p.2
  | .northEast | .east | .southEast => p.1 - o.1
  | .southWest | .west | .northWest => o.1 - p.1

/-- A computational form of closed, nonnegative-parameter ray membership. -/
def OnRationalRay (o : PlanePoint) (d : RayDirection) (p : PlanePoint) : Prop :=
  0 ≤ rayParameter o d p ∧ p = rayPoint o d (rayParameter o d p)

instance (o : PlanePoint) (d : RayDirection) (p : PlanePoint) : Decidable (OnRationalRay o d p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Pos.toPlane_injective : Function.Injective Pos.toPlane := by
  intro a b h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [Pos.toPlane, Pos.toInt, Int.cast_natCast] at hx hy
  apply Prod.ext <;> apply Fin.ext
  · exact_mod_cast hx
  · exact_mod_cast hy

@[simp] theorem rayParameter_rayPoint (o : PlanePoint) (d : RayDirection) (t : ℚ) :
    rayParameter o d (rayPoint o d t) = t := by
  cases d <;> simp [rayParameter, rayPoint, RayDirection.vector]

theorem rayPoint_injective (o : PlanePoint) (d : RayDirection) : Function.Injective (rayPoint o d) := by
  intro s t h
  have he := congrArg (rayParameter o d) h
  simpa only [rayParameter_rayPoint] using he

@[simp] theorem rayPoint_zero (o : PlanePoint) (d : RayDirection) : rayPoint o d 0 = o := by
  simp [rayPoint]

theorem onRationalRay_iff_nonneg_parameter (o : PlanePoint) (d : RayDirection) (p : PlanePoint) :
    OnRationalRay o d p ↔ ∃ t : ℚ, 0 ≤ t ∧ p = rayPoint o d t := by
  constructor
  · exact fun h => ⟨_, h.1, h.2⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by simpa using ht, by simp⟩

@[simp] theorem onRationalRay_rayPoint (o : PlanePoint) (d : RayDirection) (t : ℚ) :
    OnRationalRay o d (rayPoint o d t) ↔ 0 ≤ t := by
  simp only [OnRationalRay, rayParameter_rayPoint, and_true]

@[simp] theorem onRationalRay_origin (o : PlanePoint) (d : RayDirection) : OnRationalRay o d o := by
  simpa using (onRationalRay_rayPoint o d 0).mpr (le_refl 0)

private theorem positive_ray_coordinates (o p : PlanePoint) (d : RayDirection) :
    (0 < rayParameter o d p ∧ p = rayPoint o d (rayParameter o d p)) ↔
      let x := p.1 - o.1
      let y := p.2 - o.2
      match d with
      | .north => x = 0 ∧ 0 < y
      | .northEast => x = y ∧ 0 < x
      | .east => 0 < x ∧ y = 0
      | .southEast => x = -y ∧ 0 < x
      | .south => x = 0 ∧ y < 0
      | .southWest => x = y ∧ x < 0
      | .west => x < 0 ∧ y = 0
      | .northWest => x = -y ∧ x < 0 := by
  rcases o with ⟨ox, oy⟩
  rcases p with ⟨px, py⟩
  cases d <;>
    simp only [rayParameter, rayPoint, RayDirection.vector,
      Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero, mul_one, mul_neg_one,
      add_zero, Prod.mk.injEq] <;>
    constructor <;> intro h <;> constructor <;> (try constructor) <;> linarith

/-- Away from the origin, the extension agrees with board-square membership. -/
theorem positive_ray_toPlane_iff (k q : Pos) (d : RayDirection) :
    (0 < rayParameter k.toPlane d q.toPlane ∧
      q.toPlane = rayPoint k.toPlane d (rayParameter k.toPlane d q.toPlane)) ↔ OnRay k d q := by
  rw [positive_ray_coordinates]
  cases d <;> simp only [OnRay, Pos.toPlane] <;> norm_cast

/-- Closed rays add precisely the origin to the previous board predicate. -/
theorem onRationalRay_toPlane_iff (k q : Pos) (d : RayDirection) :
    OnRationalRay k.toPlane d q.toPlane ↔ q = k ∨ OnRay k d q := by
  constructor
  · intro h
    by_cases hz : rayParameter k.toPlane d q.toPlane = 0
    · left; apply Pos.toPlane_injective
      have he := h.2
      rwa [hz, rayPoint_zero] at he
    · right; exact (positive_ray_toPlane_iff k q d).mp ⟨lt_of_le_of_ne h.1 (Ne.symm hz), h.2⟩
  · rintro (rfl | h)
    · exact onRationalRay_origin _ _
    · have hp := (positive_ray_toPlane_iff k q d).mpr h
      exact ⟨le_of_lt hp.1, hp.2⟩

theorem rayPoint_add (o : PlanePoint) (d : RayDirection) (s t : ℚ) :
    rayPoint (rayPoint o d s) d t = rayPoint o d (s + t) := by
  apply Prod.ext <;> simp only [rayPoint] <;> ring

theorem rayPoint_opposite (o : PlanePoint) (d : RayDirection) (t : ℚ) :
    rayPoint o d.opposite t = rayPoint o d (-t) := by
  cases d <;> simp [rayPoint, RayDirection.opposite, RayDirection.vector]

/-- For equal directions on one supporting line, the second origin only
shifts the lower bound on the parameter. -/
theorem onRationalRay_shift_same (o : PlanePoint) (d : RayDirection) (s t : ℚ) :
    OnRationalRay (rayPoint o d s) d (rayPoint o d t) ↔ s ≤ t := by
  have he : rayPoint (rayPoint o d s) d (t - s) = rayPoint o d t := by
    rw [rayPoint_add]; congr 1; ring
  rw [← he, onRationalRay_rayPoint]
  exact sub_nonneg

/-- Oppositely directed collinear rays meet only between their origins, including the endpoints. -/
theorem onRationalRay_shift_opposite (o : PlanePoint) (d : RayDirection) (s t : ℚ) :
    OnRationalRay (rayPoint o d s) d.opposite (rayPoint o d t) ↔ t ≤ s := by
  have he : rayPoint (rayPoint o d s) d.opposite (s - t) = rayPoint o d t := by
    rw [rayPoint_opposite, rayPoint_add]; congr 1; ring
  rw [← he, onRationalRay_rayPoint]
  exact sub_nonneg

end MPC.Chess
