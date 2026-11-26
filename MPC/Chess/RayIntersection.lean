import MPC.Chess.RationalRay
import Mathlib.Tactic.FieldSimp

/-! Exact intersections of rational queen rays. The nonparallel solver is
separate from the full intersection relation: parallel rays can overlap. -/

namespace MPC.Chess

def rayDet (d e : RayDirection) : ℚ :=
  (d.vector.1 : ℚ) * e.vector.2 - (d.vector.2 : ℚ) * e.vector.1

/-- Signed cross product of the origin displacement with a direction. -/
def rayOffset (a b : PlanePoint) (d : RayDirection) : ℚ :=
  (b.1 - a.1) * d.vector.2 - (b.2 - a.2) * d.vector.1

def rayIntersectionParameters (a b : PlanePoint) (d e : RayDirection) : ℚ × ℚ :=
  (rayOffset a b e / rayDet d e, rayOffset a b d / rayDet d e)

/-- Only nonparallel nonnegative-parameter intersections are returned. `none` also covers
parallel overlaps and must not be read as unconditional disjointness. -/
def nonparallelIntersection (a b : PlanePoint) (d e : RayDirection) : Option PlanePoint :=
  let ts := rayIntersectionParameters a b d e
  if rayDet d e ≠ 0 ∧ 0 ≤ ts.1 ∧ 0 ≤ ts.2 then some (rayPoint a d ts.1) else none

theorem rayDet_eq_zero_iff (d e : RayDirection) : rayDet d e = 0 ↔ e = d ∨ e = d.opposite := by
  cases d <;> cases e <;> norm_num [rayDet, RayDirection.vector, RayDirection.opposite]

theorem rayOffset_eq_zero_iff (a b : PlanePoint) (d : RayDirection) :
    rayOffset a b d = 0 ↔ b = rayPoint a d (rayParameter a d b) := by
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by_⟩
  cases d <;>
    simp only [rayOffset, rayPoint, rayParameter, RayDirection.vector, Int.cast_zero,
      Int.cast_one, Int.cast_neg, mul_zero, mul_one, mul_neg_one, add_zero, Prod.mk.injEq] <;>
    constructor <;> intro h <;> (try constructor) <;> linarith

private theorem offsets_of_rayPoint_eq (a b : PlanePoint) (d e : RayDirection) (s t : ℚ)
    (h : rayPoint a d s = rayPoint b e t) :
    rayOffset a b e = s * rayDet d e ∧ rayOffset a b d = t * rayDet d e := by
  have hx : b.1 - a.1 = s * (d.vector.1 : ℚ) - t * e.vector.1 := by
    have h' := congrArg Prod.fst h
    simp only [rayPoint] at h'; linarith
  have hy : b.2 - a.2 = s * (d.vector.2 : ℚ) - t * e.vector.2 := by
    have h' := congrArg Prod.snd h
    simp only [rayPoint] at h'; linarith
  constructor <;> unfold rayOffset rayDet <;> rw [hx, hy] <;> ring

theorem rayIntersectionParameters_of_eq (a b : PlanePoint) (d e : RayDirection) (s t : ℚ)
    (hd : rayDet d e ≠ 0) (h : rayPoint a d s = rayPoint b e t) :
    s = (rayIntersectionParameters a b d e).1 ∧ t = (rayIntersectionParameters a b d e).2 := by
  obtain ⟨hs, ht⟩ := offsets_of_rayPoint_eq a b d e s t h
  exact ⟨(eq_div_iff hd).mpr hs.symm, (eq_div_iff hd).mpr ht.symm⟩

/-- Cramer's formula solves the two supporting-line equations exactly. -/
theorem rayIntersectionParameters_solve (a b : PlanePoint) (d e : RayDirection)
    (hd : rayDet d e ≠ 0) :
    rayPoint a d (rayIntersectionParameters a b d e).1 =
      rayPoint b e (rayIntersectionParameters a b d e).2 := by
  have hd' : (e.vector.2 : ℚ) * d.vector.1 - e.vector.1 * d.vector.2 ≠ 0 := by
    intro h; apply hd; dsimp only [rayDet]; linarith
  apply Prod.ext <;> dsimp only [rayPoint, rayIntersectionParameters, rayOffset, rayDet]
  all_goals dsimp only [rayDet] at hd
  all_goals (field_simp [hd, hd']; ring)

theorem nonparallelIntersection_eq_some_iff (a b p : PlanePoint) (d e : RayDirection) :
    nonparallelIntersection a b d e = some p ↔
      rayDet d e ≠ 0 ∧ OnRationalRay a d p ∧ OnRationalRay b e p := by
  constructor
  · intro h
    unfold nonparallelIntersection at h
    dsimp only at h
    split_ifs at h with hc
    · have he : rayPoint a d (rayIntersectionParameters a b d e).1 = p := Option.some.inj h
      rw [← he]
      refine ⟨hc.1, (onRationalRay_rayPoint _ _ _).mpr hc.2.1, ?_⟩
      rw [rayIntersectionParameters_solve a b d e hc.1]
      exact (onRationalRay_rayPoint _ _ _).mpr hc.2.2
  · rintro ⟨hd, hp, hq⟩
    obtain ⟨s, hs, hsp⟩ := (onRationalRay_iff_nonneg_parameter a d p).mp hp
    obtain ⟨t, ht, htp⟩ := (onRationalRay_iff_nonneg_parameter b e p).mp hq
    obtain ⟨h₁, h₂⟩ := rayIntersectionParameters_of_eq a b d e s t hd (hsp.symm.trans htp)
    subst s; subst t
    simp [nonparallelIntersection, hd, hs, ht, hsp]

theorem rationalRay_intersection_unique {a b p q : PlanePoint} {d e : RayDirection}
    (hd : rayDet d e ≠ 0) (hp : OnRationalRay a d p ∧ OnRationalRay b e p)
    (hq : OnRationalRay a d q ∧ OnRationalRay b e q) : p = q := by
  exact Option.some.inj (((nonparallelIntersection_eq_some_iff a b p d e).mpr ⟨hd, hp⟩).symm.trans
    ((nonparallelIntersection_eq_some_iff a b q d e).mpr ⟨hd, hq⟩))

theorem nonparallelIntersection_eq_none_iff (a b : PlanePoint) (d e : RayDirection)
    (hd : rayDet d e ≠ 0) : nonparallelIntersection a b d e = none ↔
      ¬ ∃ p, OnRationalRay a d p ∧ OnRationalRay b e p := by
  constructor
  · rintro h ⟨p, hp⟩
    have he := (nonparallelIntersection_eq_some_iff a b p d e).mpr ⟨hd, hp⟩
    rw [h] at he; contradiction
  · intro hn
    cases he : nonparallelIntersection a b d e with
    | none => rfl
    | some p => exact (hn ⟨p, ((nonparallelIntersection_eq_some_iff a b p d e).mp he).2⟩).elim

@[simp] theorem nonparallelIntersection_eq_none_of_parallel (a b : PlanePoint) (d e : RayDirection)
    (hd : rayDet d e = 0) : nonparallelIntersection a b d e = none := by
  simp [nonparallelIntersection, hd]

/-- Complete existence classification for parallel rays. Equal directions
on one supporting line overlap; opposite directions overlap only when their
origins face one another or coincide, with the closed segment between them as intersection. -/
theorem parallel_rays_intersect_iff (a b : PlanePoint) (d e : RayDirection)
    (hd : rayDet d e = 0) :
    (∃ p, OnRationalRay a d p ∧ OnRationalRay b e p) ↔
      rayOffset a b d = 0 ∧ (e = d ∨ (e = d.opposite ∧ 0 ≤ rayParameter a d b)) := by
  constructor
  · rintro ⟨p, hp, hq⟩
    obtain ⟨s, hs, hsp⟩ := (onRationalRay_iff_nonneg_parameter a d p).mp hp
    obtain ⟨t, _, htp⟩ := (onRationalRay_iff_nonneg_parameter b e p).mp hq
    have hoff := (offsets_of_rayPoint_eq a b d e s t (hsp.symm.trans htp)).2
    rw [hd, mul_zero] at hoff
    refine ⟨hoff, ?_⟩
    rcases (rayDet_eq_zero_iff d e).mp hd with he | he
    · exact Or.inl he
    · refine Or.inr ⟨he, ?_⟩
      have hb := (rayOffset_eq_zero_iff a b d).mp hoff
      rw [he, hb, hsp] at hq
      have ht := (onRationalRay_shift_opposite a d (rayParameter a d b) s).mp hq
      linarith
  · rintro ⟨hoff, he | ⟨he, hbpos⟩⟩
    · subst e
      let t := max 0 (rayParameter a d b) + 1
      refine ⟨rayPoint a d t, (onRationalRay_rayPoint _ _ _).mpr ?_, ?_⟩
      · have := le_max_left (0 : ℚ) (rayParameter a d b); dsimp [t]; linarith
      · rw [(rayOffset_eq_zero_iff a b d).mp hoff]
        apply (onRationalRay_shift_same a d _ t).mpr
        have := le_max_right (0 : ℚ) (rayParameter a d b); dsimp [t]; linarith
    · subst e
      refine ⟨rayPoint a d (rayParameter a d b / 2), (onRationalRay_rayPoint _ _ _).mpr (by linarith), ?_⟩
      rw [(rayOffset_eq_zero_iff a b d).mp hoff]
      apply (onRationalRay_shift_opposite a d _ _).mpr
      simp only [rayParameter_rayPoint]
      linarith

end MPC.Chess
