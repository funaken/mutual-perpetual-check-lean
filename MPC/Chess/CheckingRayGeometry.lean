import MPC.Chess.KingGeometry

/-! The eight queen rays, restricted to board squares other than their origin.
The excluded origin is occupied by the fixed king in the periodic application. -/

namespace MPC.Chess

inductive RayDirection where
  | north | northEast | east | southEast | south | southWest | west | northWest
  deriving DecidableEq, Repr

instance : Fintype RayDirection :=
  ⟨{.north, .northEast, .east, .southEast, .south, .southWest, .west, .northWest},
    fun d => by cases d <;> simp⟩

def OnRay (king : Pos) (d : RayDirection) (q : Pos) : Prop :=
  let x := q.toInt.1 - king.toInt.1
  let y := q.toInt.2 - king.toInt.2
  match d with
  | .north => x = 0 ∧ 0 < y
  | .northEast => x = y ∧ 0 < x
  | .east => 0 < x ∧ y = 0
  | .southEast => x = -y ∧ 0 < x
  | .south => x = 0 ∧ y < 0
  | .southWest => x = y ∧ x < 0
  | .west => x < 0 ∧ y = 0
  | .northWest => x = -y ∧ x < 0

instance (k : Pos) (d : RayDirection) (q : Pos) : Decidable (OnRay k d q) := by
  cases d <;> unfold OnRay <;> infer_instance

def RayDirection.vector : RayDirection → ℤ × ℤ
  | .north => (0, 1)
  | .northEast => (1, 1)
  | .east => (1, 0)
  | .southEast => (1, -1)
  | .south => (0, -1)
  | .southWest => (-1, -1)
  | .west => (-1, 0)
  | .northWest => (-1, 1)

/-- The table describes exactly positive integer steps along a queen direction.
Only the board restriction comes from the type of `q`. -/
theorem onRay_iff_positive_steps (k q : Pos) (d : RayDirection) :
    OnRay k d q ↔ ∃ n : ℤ, 0 < n ∧
      q.toInt.1 = k.toInt.1 + n * d.vector.1 ∧ q.toInt.2 = k.toInt.2 + n * d.vector.2 := by
  cases d <;> simp only [OnRay, RayDirection.vector, mul_one, mul_zero, mul_neg_one, add_zero]
  all_goals
    constructor
    · intro h
      first
      | exact ⟨q.toInt.1 - k.toInt.1, by omega, by omega, by omega⟩
      | exact ⟨k.toInt.1 - q.toInt.1, by omega, by omega, by omega⟩
      | exact ⟨q.toInt.2 - k.toInt.2, by omega, by omega, by omega⟩
      | exact ⟨k.toInt.2 - q.toInt.2, by omega, by omega, by omega⟩
    · rintro ⟨n, hn, hx, hy⟩; omega

private theorem pos_ext {a b : Pos} (hx : a.toInt.1 = b.toInt.1)
    (hy : a.toInt.2 = b.toInt.2) : a = b := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [Pos.toInt] at hx hy <;> omega

theorem OnRay.ne {k q : Pos} {d : RayDirection} (h : OnRay k d q) : q ≠ k := by
  intro he; subst q
  cases d <;> simp [OnRay] at h

theorem OnRay.aligned {k q : Pos} {d : RayDirection} (h : OnRay k d q) : q.aligned k := by
  cases d <;> simp only [OnRay] at h <;> unfold Pos.aligned <;> omega

theorem OnRay.direction_unique {k q : Pos} {d e : RayDirection}
    (hd : OnRay k d q) (he : OnRay k e q) : d = e := by
  cases d <;> cases e <;> simp_all [OnRay] <;> omega

theorem exists_onRay_of_aligned {k q : Pos} (ha : q.aligned k) (hn : q ≠ k) :
    ∃ d, OnRay k d q := by
  have hne : q.toInt.1 ≠ k.toInt.1 ∨ q.toInt.2 ≠ k.toInt.2 := by
    by_contra h; push Not at h; exact hn (pos_ext h.1 h.2)
  by_cases hnorth : OnRay k .north q
  · exact ⟨.north, hnorth⟩
  by_cases hneast : OnRay k .northEast q
  · exact ⟨.northEast, hneast⟩
  by_cases heast : OnRay k .east q
  · exact ⟨.east, heast⟩
  by_cases hseast : OnRay k .southEast q
  · exact ⟨.southEast, hseast⟩
  by_cases hsouth : OnRay k .south q
  · exact ⟨.south, hsouth⟩
  by_cases hswest : OnRay k .southWest q
  · exact ⟨.southWest, hswest⟩
  by_cases hwest : OnRay k .west q
  · exact ⟨.west, hwest⟩
  exact ⟨.northWest, by simp only [OnRay] at *; unfold Pos.aligned at ha; omega⟩

theorem OnRay.of_between {k a q : Pos} {d : RayDirection}
    (ha : OnRay k d a) (hq : Between a k q) : OnRay k d q := by
  obtain ⟨_, hqk, hc, hx0, hx1, hy0, hy1⟩ := hq
  have hne : q.toInt.1 ≠ k.toInt.1 ∨ q.toInt.2 ≠ k.toInt.2 := by
    by_contra h; push Not at h; exact hqk (pos_ext h.1 h.2)
  cases d <;> simp only [OnRay] at ha ⊢
  all_goals try omega
  all_goals
    have hx : k.toInt.1 - a.toInt.1 ≠ 0 := by omega
    have hline : q.toInt.1 - a.toInt.1 = q.toInt.2 - a.toInt.2 ∨
        q.toInt.1 - a.toInt.1 = -(q.toInt.2 - a.toInt.2) := by
      first
      | left; apply mul_right_cancel₀ hx
        rw [show k.toInt.2 - a.toInt.2 = k.toInt.1 - a.toInt.1 by omega] at hc
        exact hc
      | right; apply mul_right_cancel₀ hx
        rw [show k.toInt.2 - a.toInt.2 = -(k.toInt.1 - a.toInt.1) by omega] at hc
        nlinarith only [hc]
    omega

/-- A distance used only to order points on one ray. -/
def rayDistance (k q : Pos) : ℤ := |q.toInt.1 - k.toInt.1| + |q.toInt.2 - k.toInt.2|

theorem OnRay.between_iff_distance {k a q : Pos} {d : RayDirection}
    (ha : OnRay k d a) (hq : OnRay k d q) :
    Between a k q ↔ rayDistance k q < rayDistance k a := by
  have hqk := hq.ne
  have hcross : (q.toInt.1 - a.toInt.1) * (k.toInt.2 - a.toInt.2) =
      (q.toInt.2 - a.toInt.2) * (k.toInt.1 - a.toInt.1) := by
    cases d <;> simp only [OnRay] at ha hq <;> nlinarith [ha.1, ha.2, hq.1, hq.2]
  constructor
  · intro hb
    have hn : q.toInt.1 ≠ a.toInt.1 ∨ q.toInt.2 ≠ a.toInt.2 := by
      by_contra h; push Not at h; exact hb.1 (pos_ext h.1 h.2)
    obtain ⟨_, _, _, hb⟩ := hb
    cases d <;> simp only [OnRay] at ha hq <;>
      simp only [rayDistance, abs_eq_max_neg] <;> omega
  · intro hr
    have hqa : q ≠ a := by intro h; subst q; exact (lt_irrefl _ hr)
    refine ⟨hqa, hqk, hcross, ?_⟩
    cases d <;> simp only [OnRay] at ha hq <;>
      simp only [rayDistance, abs_eq_max_neg] at hr <;> omega

theorem OnRay.eq_of_distance_eq {k a q : Pos} {d : RayDirection}
    (ha : OnRay k d a) (hq : OnRay k d q) (he : rayDistance k a = rayDistance k q) : a = q := by
  apply pos_ext <;> cases d <;> simp only [OnRay] at ha hq <;>
    simp only [rayDistance, abs_eq_max_neg] at he <;> omega

set_option maxHeartbeats 800000 in
/-- Ordered points on one ray form an open segment in the same order. -/
theorem OnRay.between_of_distance_lt {k a b q : Pos} {d : RayDirection}
    (ha : OnRay k d a) (hb : OnRay k d b) (hq : OnRay k d q)
    (h₁ : rayDistance k a < rayDistance k q) (h₂ : rayDistance k q < rayDistance k b) :
    Between a b q := by
  have hqa : q ≠ a := by intro h; subst q; exact lt_irrefl _ h₁
  have hqb : q ≠ b := by intro h; subst q; exact lt_irrefl _ h₂
  refine ⟨hqa, hqb, ?_, ?_⟩
  · cases d <;> simp only [OnRay] at ha hb hq <;>
      nlinarith [ha.1, ha.2, hb.1, hb.2, hq.1, hq.2]
  · cases d <;> simp only [OnRay] at ha hb hq <;>
      simp only [rayDistance, abs_eq_max_neg] at h₁ h₂ <;> omega

/-- Moving a blocker along the same ray past a checking slider would cross
that slider. The checker and landing square must be distinct. -/
theorem between_of_same_ray_exit {k a b c : Pos} {d : RayDirection}
    (ha : OnRay k d a) (hb : OnRay k d b) (hc : c.aligned k) (hck : c ≠ k)
    (h₁ : Between c k a) (h₂ : ¬ Between c k b) (hbc : b ≠ c) : Between a b c := by
  obtain ⟨e, he⟩ := exists_onRay_of_aligned hc hck
  have hed : e = d := (he.of_between h₁).direction_unique ha
  subst e
  have hlt := (he.between_iff_distance ha).mp h₁
  have hn : ¬ rayDistance k b < rayDistance k c := fun h => h₂ ((he.between_iff_distance hb).mpr h)
  have hne : rayDistance k b ≠ rayDistance k c := fun h => hbc (hb.eq_of_distance_eq he h)
  exact ha.between_of_distance_lt hb he hlt (by omega)

/-- A non-king, non-pawn attack cannot jump over pieces when its endpoints
lie on one queen ray. In particular, the knight case is impossible. -/
theorem pathClear_of_attack_onRay {board : Board} {p : Piece} {k a b : Pos}
    {d : RayDirection} (ha : OnRay k d a) (hb : OnRay k d b)
    (hnk : p.kind ≠ .king) (hnp : p.kind ≠ .pawn) (hm : attacks board p a b) :
    pathClear board a b := by
  cases hp : p.kind with
  | king => exact (hnk hp).elim
  | pawn => exact (hnp hp).elim
  | queen | rook | bishop => simp only [attacks, hp] at hm; exact hm.2.2
  | knight =>
    simp only [attacks, hp, Pos.delta, abs_eq_max_neg] at hm
    cases d <;> simp only [OnRay] at ha hb <;> omega

theorem Between.symm {a b q : Pos} (h : Between a b q) : Between b a q := by
  obtain ⟨hqa, hqb, hc, hb⟩ := h
  refine ⟨hqb, hqa, ?_, ?_⟩
  · nlinarith only [hc]
  · simpa only [min_comm, max_comm] using hb

/-- On one ray, a sliding piece's direction condition is unchanged when its
source changes. Actual attacks additionally need the supplied clear path. -/
theorem slider_attack_onRay {board board' : Board} {p : Piece} {k a b : Pos}
    {d : RayDirection} (ha : OnRay k d a) (hb : OnRay k d b)
    (hs : p.kind = .queen ∨ p.kind = .rook ∨ p.kind = .bishop)
    (hat : attacks board p a k) (hclear : pathClear board' b k) : attacks board' p b k := by
  rcases hs with hs | hs | hs <;>
    simp only [attacks, hs, Pos.delta, abs_eq_abs] at hat ⊢ <;>
    refine ⟨hb.ne, ?_, hclear⟩ <;>
    cases d <;> simp only [OnRay] at ha hb <;> omega

/-- A move within a ray cannot create a clear path from a formerly blocked
source when the landing square was empty and the moving piece cannot jump. -/
theorem pathClear_source_of_move_onRay {board : Board} {k src dst : Pos}
    {d : RayDirection} (hs : OnRay k d src) (hd : OnRay k d dst)
    (he : board dst = none) (hm : pathClear board src dst)
    (ha : pathClear (board.relocate src dst none) dst k) : pathClear board src k := by
  intro q hq
  by_cases hqd : q = dst
  · subst q; exact he
  have hr := hs.of_between hq
  by_cases hlt : rayDistance k q < rayDistance k dst
  · have hqa := ha q ((hd.between_iff_distance hr).mpr hlt)
    simpa only [Board.relocate_other board src dst q none hq.1 hqd] using hqa
  · have hne : rayDistance k q ≠ rayDistance k dst := fun h => hqd (hr.eq_of_distance_eq hd h)
    have hbetween := hd.between_of_distance_lt hs hr (by omega) ((hs.between_iff_distance hr).mp hq)
    exact hm q hbetween.symm

end MPC.Chess
