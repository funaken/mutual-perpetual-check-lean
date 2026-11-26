import MPC.Chess.RayAngleRank

/-! The eight symmetries of the square lattice that fix the origin. The paper
classifies the kings and checking rays "up to translation, rotation and
reflection"; a frame realizes the rotation or reflection on rational
displacements and on the eight queen directions compatibly. Translations are
kept explicit as the origin king. -/

namespace MPC.Chess

/-- Exchange of the two coordinates of a queen direction. -/
def RayDirection.transpose : RayDirection → RayDirection
  | .north => .east | .northEast => .northEast | .east => .north | .southEast => .northWest
  | .south => .west | .southWest => .southWest | .west => .south | .northWest => .southEast

/-- Negation of the first coordinate of a queen direction. -/
def RayDirection.reflectX : RayDirection → RayDirection
  | .north => .north | .northEast => .northWest | .east => .west | .southEast => .southWest
  | .south => .south | .southWest => .southEast | .west => .east | .northWest => .northEast

/-- Negation of the second coordinate of a queen direction. -/
def RayDirection.reflectY : RayDirection → RayDirection
  | .north => .south | .northEast => .southEast | .east => .east | .southEast => .northEast
  | .south => .north | .southWest => .northWest | .west => .west | .northWest => .southWest

/-- Optionally exchange the coordinates, then optionally negate each one. -/
structure LatticeFrame where
  swap : Bool
  negX : Bool
  negY : Bool
  deriving DecidableEq, Repr

namespace LatticeFrame

def flip (b : Bool) (x : ℚ) : ℚ := if b then -x else x

@[simp] theorem flip_false (x : ℚ) : flip false x = x := rfl
@[simp] theorem flip_true (x : ℚ) : flip true x = -x := rfl

def apply (F : LatticeFrame) (v : PlanePoint) : PlanePoint :=
  if F.swap then (flip F.negX v.2, flip F.negY v.1) else (flip F.negX v.1, flip F.negY v.2)

def dir (F : LatticeFrame) (d : RayDirection) : RayDirection :=
  let d₁ := if F.swap then d.transpose else d
  let d₂ := if F.negX then d₁.reflectX else d₁
  if F.negY then d₂.reflectY else d₂

/-- The point reflection of a frame: the same frame seen from the other king. -/
def neg (F : LatticeFrame) : LatticeFrame := ⟨F.swap, !F.negX, !F.negY⟩

/-- `1` for the four rotations and `-1` for the four reflections. -/
def det (F : LatticeFrame) : ℚ := flip F.swap (flip F.negX (flip F.negY 1))

theorem apply_add (F : LatticeFrame) (v w : PlanePoint) :
    F.apply (v + w) = F.apply v + F.apply w := by
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> ext <;> simp [apply] <;> ring

theorem apply_injective (F : LatticeFrame) : Function.Injective F.apply := by
  intro v w h
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> simp only [apply, Prod.mk.injEq, flip_true, flip_false,
    neg_inj, ite_true, ite_false, Bool.false_eq_true] at h <;> ext <;> simp only [h]

theorem neg_apply (F : LatticeFrame) (v : PlanePoint) : F.neg.apply v = -F.apply v := by
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> ext <;> simp [neg, apply]

theorem neg_dir (F : LatticeFrame) (d : RayDirection) : F.neg.dir d = (F.dir d).opposite := by
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> cases d <;> rfl

theorem dir_opposite (F : LatticeFrame) (d : RayDirection) :
    F.dir d.opposite = (F.dir d).opposite := by
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> cases d <;> rfl

theorem det_cases (F : LatticeFrame) : F.det = 1 ∨ F.det = -1 := by
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> norm_num [det]

theorem abs_det (F : LatticeFrame) : |F.det| = 1 := by
  rcases F.det_cases with h | h <;> simp [h]

theorem dir_vector (F : LatticeFrame) (d : RayDirection) :
    (((F.dir d).vector.1 : ℚ), ((F.dir d).vector.2 : ℚ)) =
      F.apply ((d.vector.1 : ℚ), (d.vector.2 : ℚ)) := by
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> cases d <;>
    norm_num [dir, apply, RayDirection.vector, RayDirection.transpose, RayDirection.reflectX,
      RayDirection.reflectY]

theorem apply_smul (F : LatticeFrame) (t : ℚ) (v : PlanePoint) :
    F.apply (t * v.1, t * v.2) = (t * (F.apply v).1, t * (F.apply v).2) := by
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> ext <;> simp [apply]

/-- Each coordinate of the image is a coordinate of the argument, up to sign. -/
theorem apply_fst_cases (F : LatticeFrame) (v : PlanePoint) :
    (F.apply v).1 = v.1 ∨ (F.apply v).1 = -v.1 ∨ (F.apply v).1 = v.2 ∨ (F.apply v).1 = -v.2 := by
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> simp [apply]

theorem abs_apply (F : LatticeFrame) (v : PlanePoint) :
    (|(F.apply v).1| = |v.1| ∧ |(F.apply v).2| = |v.2|) ∨
      (|(F.apply v).1| = |v.2| ∧ |(F.apply v).2| = |v.1|) := by
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> simp [apply]

end LatticeFrame

open LatticeFrame

theorem rayPoint_dir (o : PlanePoint) (F : LatticeFrame) (d : RayDirection) (t : ℚ) :
    rayPoint o (F.dir d) t = o + F.apply (rayPoint (0, 0) d t) := by
  have hv := F.dir_vector d
  have hs := F.apply_smul t ((d.vector.1 : ℚ), (d.vector.2 : ℚ))
  simp only [rayPoint, zero_add]
  rw [hs, ← hv]
  rfl

theorem onRationalRay_dir_iff (o p : PlanePoint) (F : LatticeFrame) (d : RayDirection) :
    OnRationalRay o (F.dir d) p ↔ ∃ t : ℚ, 0 ≤ t ∧ p = o + F.apply (rayPoint (0, 0) d t) := by
  rw [onRationalRay_iff_nonneg_parameter]
  simp only [rayPoint_dir]

theorem onRay_dir_iff (K q : Pos) (F : LatticeFrame) (d : RayDirection) :
    OnRay K (F.dir d) q ↔
      ∃ t : ℚ, 0 < t ∧ q.toPlane = K.toPlane + F.apply (rayPoint (0, 0) d t) := by
  rw [← positive_ray_toPlane_iff]
  constructor
  · rintro ⟨ht, he⟩
    exact ⟨_, ht, by rw [← rayPoint_dir]; exact he⟩
  · rintro ⟨t, ht, he⟩
    rw [← rayPoint_dir] at he
    rw [he, rayParameter_rayPoint]
    exact ⟨ht, rfl⟩

theorem rayDot_swap (K L : PlanePoint) (d : RayDirection) : rayDot L K d = -rayDot K L d := by
  unfold rayDot; ring

theorem rayOffset_dir {K L w : PlanePoint} {F : LatticeFrame} (hL : L = K + F.apply w)
    (m : RayDirection) :
    rayOffset K L (F.dir m) = F.det * (w.1 * m.vector.2 - w.2 * m.vector.1) := by
  have hv := F.dir_vector m
  unfold rayOffset
  rw [show ((F.dir m).vector.1 : ℚ) = _ from congrArg Prod.fst hv,
    show ((F.dir m).vector.2 : ℚ) = _ from congrArg Prod.snd hv, hL]
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> simp [apply, det] <;> ring

theorem rayDot_dir {K L w : PlanePoint} {F : LatticeFrame} (hL : L = K + F.apply w)
    (m : RayDirection) :
    rayDot K L (F.dir m) = w.1 * m.vector.1 + w.2 * m.vector.2 := by
  have hv := F.dir_vector m
  unfold rayDot
  rw [show ((F.dir m).vector.1 : ℚ) = _ from congrArg Prod.fst hv,
    show ((F.dir m).vector.2 : ℚ) = _ from congrArg Prod.snd hv, hL]
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> simp [apply] <;> ring

/-- Angle ranks are invariant under the frame: they are read off in canonical coordinates. -/
theorem kingRayRank_dir {K L w : PlanePoint} {F : LatticeFrame} (hL : L = K + F.apply w)
    (m : RayDirection) :
    kingRayRank K L (F.dir m) =
      angleRank |w.1 * m.vector.2 - w.2 * m.vector.1| (w.1 * m.vector.1 + w.2 * m.vector.2) := by
  unfold kingRayRank
  rw [rayOffset_dir hL, rayDot_dir hL, abs_mul, F.abs_det, one_mul]

theorem kingRayRank_dir_swap {K L w : PlanePoint} {F : LatticeFrame} (hL : L = K + F.apply w)
    (m : RayDirection) :
    kingRayRank L K (F.dir m) =
      angleRank |w.1 * m.vector.2 - w.2 * m.vector.1| (-(w.1 * m.vector.1 + w.2 * m.vector.2)) := by
  unfold kingRayRank
  rw [rayOffset_swap, rayDot_swap, rayOffset_dir hL, rayDot_dir hL, abs_neg, abs_mul, F.abs_det,
    one_mul]

theorem mem_halfPlaneDirections_dir {K L w : PlanePoint} {F : LatticeFrame}
    (hL : L = K + F.apply w) (side : HalfPlaneSide) (m : RayDirection) :
    F.dir m ∈ halfPlaneDirections K L side ↔
      0 < side.sign * F.det * (w.1 * m.vector.2 - w.2 * m.vector.1) := by
  rw [mem_halfPlaneDirections_iff, rayOffset_dir hL, mul_assoc]

/-- The same global side seen from the other king, with the orientation reversed. -/
theorem mem_halfPlaneDirections_swap_iff (K L : PlanePoint) (side : HalfPlaneSide)
    (d : RayDirection) :
    d ∈ halfPlaneDirections L K side ↔ d ∈ halfPlaneDirections K L side.opposite := by
  simpa using mem_halfPlaneDirections_swap K L side.opposite d

/-- Reversing a direction moves it to the opposite open side. -/
theorem mem_halfPlaneDirections_opposite (K L : PlanePoint) (side : HalfPlaneSide)
    (d : RayDirection) :
    d.opposite ∈ halfPlaneDirections K L side.opposite ↔ d ∈ halfPlaneDirections K L side := by
  have h : rayOffset K L d.opposite = -rayOffset K L d := by
    cases d <;> simp [rayOffset, RayDirection.opposite, RayDirection.vector] <;> ring
  rw [mem_halfPlaneDirections_iff, mem_halfPlaneDirections_iff, h]
  cases side <;> simp only [HalfPlaneSide.opposite, HalfPlaneSide.sign] <;>
    constructor <;> intro h <;> linarith

end MPC.Chess
