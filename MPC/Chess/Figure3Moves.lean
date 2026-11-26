import MPC.Chess.Figure3Candidates

/-! Moves in the Figure 3 candidates. Lemma 6.2 puts every move between two
crossings on different checking rays of each king, and the mover is a queen,
rook, bishop or knight, so its displacement is a line or a knight jump. In
canonical coordinates the three upper candidates leave a single possible move
pair, between `A = (0, 1)` and `B = (2, 2)` for `(a, b) = (3, 1)`, and none for
`(5, 1)` and `(4, 2)`. A knight shuttling between two squares cannot serve both
players, so the opposite half-plane must contain checking rays as well. -/

namespace MPC.Chess

open LatticeFrame

/-- Displacements of queen, rook, bishop and knight moves, stated through
absolute values so that it is invariant under lattice frames. -/
def StepShape (x y : ℚ) : Prop :=
  |x| = 0 ∨ |y| = 0 ∨ |x| = |y| ∨ (|x| = 1 ∧ |y| = 2) ∨ (|x| = 2 ∧ |y| = 1)

theorem stepShape_frame (F : LatticeFrame) (w : PlanePoint) :
    StepShape (F.apply w).1 (F.apply w).2 ↔ StepShape w.1 w.2 := by
  rcases F.abs_apply w with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simp only [StepShape, h₁, h₂]
  · simp only [StepShape, h₁, h₂]
    constructor <;> rintro (h | h | h | ⟨h, h'⟩ | ⟨h, h'⟩)
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr (Or.inl h.symm)),
      Or.inr (Or.inr (Or.inr (Or.inr ⟨h', h⟩))), Or.inr (Or.inr (Or.inr (Or.inl ⟨h', h⟩))),
      Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr (Or.inl h.symm)),
      Or.inr (Or.inr (Or.inr (Or.inr ⟨h', h⟩))), Or.inr (Or.inr (Or.inr (Or.inl ⟨h', h⟩)))]

theorem LatticeFrame.apply_sub (F : LatticeFrame) (v w : PlanePoint) :
    F.apply (v - w) = F.apply v - F.apply w := by
  obtain ⟨s, x, y⟩ := F
  cases s <;> cases x <;> cases y <;> ext <;> simp [LatticeFrame.apply] <;> ring

/-- Board squares in canonical coordinates keep the displacement shape. -/
theorem stepShape_canonical {K src dst : Pos} {F : LatticeFrame} {p p' : PlanePoint}
    (hs : src.toPlane = K.toPlane + F.apply p) (hd : dst.toPlane = K.toPlane + F.apply p')
    (h : StepShape (dst.toPlane.1 - src.toPlane.1) (dst.toPlane.2 - src.toPlane.2)) :
    StepShape (p'.1 - p.1) (p'.2 - p.2) := by
  have hw : dst.toPlane - src.toPlane = F.apply (p' - p) := by
    rw [hs, hd, F.apply_sub, add_sub_add_left_eq_sub]
  have := (stepShape_frame F (p' - p)).mp
    (by rw [← hw]; simpa only [Prod.fst_sub, Prod.snd_sub] using h)
  simpa only [Prod.fst_sub, Prod.snd_sub] using this

namespace MoveTrace

/-- Kings do not move and pawns do not move, so every move is a line move of a
queen, rook or bishop, or a knight jump. -/
theorem move_stepShape_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) :
    StepShape (dst.toPlane.1 - src.toPlane.1) (dst.toPlane.2 - src.toPlane.2) := by
  obtain ⟨src', dst', p, hm', -, -, hking, hpawn, -, -, ha⟩ :=
    tr.ordinary_nonKing_nonPawn_move_of_periodic_checks kp hl hk hc hp i
  rw [hm] at hm'
  obtain ⟨rfl, rfl, -⟩ := Move.boardMove.inj hm'
  have hz : StepShape ((dst.toInt.1 - src.toInt.1 : ℤ) : ℚ) ((dst.toInt.2 - src.toInt.2 : ℤ) : ℚ) := by
    simp only [StepShape, ← Int.cast_abs]
    obtain ⟨-, ha⟩ := ha
    simp only [Pos.delta] at ha
    rcases p with ⟨o, kind⟩
    cases kind with
    | king => exact absurd rfl hking
    | pawn => exact absurd rfl hpawn
    | queen =>
      rcases ha.1 with h | h | h
      · exact Or.inl (by rw [h]; simp)
      · exact Or.inr (Or.inl (by rw [h]; simp))
      · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast h)))
    | rook =>
      rcases ha.1 with h | h
      · exact Or.inl (by rw [h]; simp)
      · exact Or.inr (Or.inl (by rw [h]; simp))
    | bishop => exact Or.inr (Or.inr (Or.inl (by exact_mod_cast ha.1)))
    | knight =>
      rcases ha with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩)))
  simpa only [Pos.toPlane, Int.cast_sub] using hz

end MoveTrace

section UpperCrossings

variable {K L q : Pos} {F : LatticeFrame} {a b : ℚ}

/-- The four crossings of an upper half-plane in canonical coordinates. -/
theorem crossing_northEast_west (hL : L.toPlane = K.toPlane + F.apply (a, b))
    (h₁ : OnRay K (F.dir .northEast) q) (h₂ : OnRay L (F.dir .west) q) :
    q.toPlane = K.toPlane + F.apply (b, b) := by
  obtain ⟨t, s, -, -, hq, he⟩ := frame_crossing_eq hL h₁ h₂
  simp only [rayPoint, RayDirection.vector, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at he
  norm_num at he
  rw [hq]; congr 2; simp only [rayPoint, RayDirection.vector]; ext <;> norm_num <;> linarith

theorem crossing_northEast_northWest (hL : L.toPlane = K.toPlane + F.apply (a, b))
    (h₁ : OnRay K (F.dir .northEast) q) (h₂ : OnRay L (F.dir .northWest) q) :
    q.toPlane = K.toPlane + F.apply ((a + b) / 2, (a + b) / 2) := by
  obtain ⟨t, s, -, -, hq, he⟩ := frame_crossing_eq hL h₁ h₂
  simp only [rayPoint, RayDirection.vector, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at he
  norm_num at he
  rw [hq]; congr 2; simp only [rayPoint, RayDirection.vector]; ext <;> norm_num <;> linarith

theorem crossing_north_west (hL : L.toPlane = K.toPlane + F.apply (a, b))
    (h₁ : OnRay K (F.dir .north) q) (h₂ : OnRay L (F.dir .west) q) :
    q.toPlane = K.toPlane + F.apply (0, b) := by
  obtain ⟨t, s, -, -, hq, he⟩ := frame_crossing_eq hL h₁ h₂
  simp only [rayPoint, RayDirection.vector, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at he
  norm_num at he
  rw [hq]; congr 2; simp only [rayPoint, RayDirection.vector]; ext <;> norm_num; linarith

theorem crossing_north_northWest (hL : L.toPlane = K.toPlane + F.apply (a, b))
    (h₁ : OnRay K (F.dir .north) q) (h₂ : OnRay L (F.dir .northWest) q) :
    q.toPlane = K.toPlane + F.apply (0, a + b) := by
  obtain ⟨t, s, -, -, hq, he⟩ := frame_crossing_eq hL h₁ h₂
  simp only [rayPoint, RayDirection.vector, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at he
  norm_num at he
  rw [hq]; congr 2; simp only [rayPoint, RayDirection.vector]; ext <;> norm_num; linarith

end UpperCrossings

namespace MoveTrace

/-- If every move goes between two fixed squares, one piece shuttles between
them. The second move would need the other player's piece there. -/
theorem false_of_two_square_moves (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (A B : Pos)
    (h : ∀ i, ∃ src dst, tr.moves i = .boardMove src dst none ∧
      (src = A ∨ src = B) ∧ (dst = A ∨ dst = B)) : False := by
  have h₂ : 1 < tr.len := by
    by_contra h₁
    have hlen : tr.len = 1 := by omega
    have ht := tr.turn_after_of_legal hl ⟨0, hn⟩
    have hlast : tr.after ⟨0, hn⟩ = tr.states (Fin.last tr.len) := by
      unfold MoveTrace.after; congr 1; ext; simp [hlen]
    rw [hlast, hp.2] at ht
    exact Color.opponent_ne _ ht.symm
  let i₀ : Fin tr.len := ⟨0, hn⟩
  let i₁ : Fin tr.len := ⟨1, h₂⟩
  have hmid : tr.after i₀ = tr.before i₁ := rfl
  obtain ⟨s₀, d₀, hm₀, hs₀, hd₀⟩ := h i₀
  obtain ⟨s₁, d₁, hm₁, hs₁, -⟩ := h i₁
  obtain ⟨_, hv₀, he₀⟩ := hl i₀
  have hv₀' : PseudoLegal (tr.before i₀) (.boardMove s₀ d₀ none) := by
    simpa only [hm₀] using hv₀.movement
  obtain ⟨p₀, hp₀, ho₀, hne₀, -⟩ := hv₀'
  have hafter_s : (tr.after i₀).board s₀ = none := by
    rw [he₀, hm₀]; exact Board.relocate_source _ _ _ _ hne₀
  have hafter_d : (tr.after i₀).board d₀ = some p₀ := by
    rw [he₀, hm₀]; simp [applyMove, applyBoard, hp₀, Piece.promote]
  have hturn := tr.turn_after_of_legal hl i₀
  obtain ⟨_, hv₁, -⟩ := hl i₁
  have hv₁' : PseudoLegal (tr.before i₁) (.boardMove s₁ d₁ none) := by
    simpa only [hm₁] using hv₁.movement
  obtain ⟨p₁, hp₁, ho₁, -, -⟩ := hv₁'
  rw [← hmid] at hp₁ ho₁
  have hcover : s₁ = s₀ ∨ s₁ = d₀ := by
    rcases hs₀ with rfl | rfl <;> rcases hd₀ with rfl | rfl <;>
      first | exact absurd rfl hne₀ | tauto
  rcases hcover with rfl | rfl
  · rw [hafter_s] at hp₁; cases hp₁
  · rw [hafter_d] at hp₁
    cases hp₁
    rw [hturn, ← ho₀] at ho₁
    exact Color.opponent_ne _ ho₁.symm

/-- The upper candidates of Figure 3: with checking rays only in one
half-plane, Lemma 6.2 and the move shapes leave the knight move between
`A = K + F(0, 1)` and `B = K + F(2, 2)` for `(a, b) = (3, 1)` and nothing for
`(5, 1)` and `(4, 2)`, which is impossible. -/
theorem false_of_upper_candidate (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (F : LatticeFrame) (a b : ℤ)
    (hab : (a = 3 ∧ b = 1) ∨ (a = 5 ∧ b = 1) ∨ (a = 4 ∧ b = 2))
    (hL : (kp 0 c.opponent).toPlane = (kp 0 c).toPlane + F.apply ((a : ℚ), (b : ℚ)))
    (hu : ∀ d, tr.CheckingRay (kp 0 c) c d → d = F.dir .northEast ∨ d = F.dir .north)
    (hv : ∀ e, tr.CheckingRay (kp 0 c.opponent) c.opponent e →
      e = F.dir .west ∨ e = F.dir .northWest) : False := by
  set PA := (kp 0 c).toPlane + F.apply (0, 1)
  set PB := (kp 0 c).toPlane + F.apply (2, 2)
  have hmove (i : Fin tr.len) : ∃ src dst, tr.moves i = .boardMove src dst none ∧
      ((src.toPlane = PA ∧ dst.toPlane = PB) ∨ (src.toPlane = PB ∧ dst.toPlane = PA)) := by
    obtain ⟨src, dst, hm, hr⟩ := tr.every_move_between_distinct_checkingRays kp hl hk hc hp i
    obtain ⟨ds, dd, hne₁, hds, hdd, hsK, hdK⟩ := hr c
    obtain ⟨es, ed, hne₂, hes, hed, hsL, hdL⟩ := hr c.opponent
    have hstep := tr.move_stepShape_of_periodic_checks kp hl hk hc hp i src dst hm
    refine ⟨src, dst, hm, ?_⟩
    rcases hu ds hds with rfl | rfl <;> rcases hu dd hdd with rfl | rfl <;>
      (try exact absurd rfl hne₁) <;>
      rcases hv es hes with rfl | rfl <;> rcases hv ed hed with rfl | rfl <;>
      (try exact absurd rfl hne₂)
    · have h₁ := crossing_northEast_west hL hsK hsL
      have h₂ := crossing_north_northWest hL hdK hdL
      have := stepShape_canonical h₁ h₂ hstep
      exfalso
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num [StepShape] at this
    · have h₁ := crossing_northEast_northWest hL hsK hsL
      have h₂ := crossing_north_west hL hdK hdL
      have := stepShape_canonical h₁ h₂ hstep
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨by rw [h₁]; norm_num [PB], by rw [h₂]; norm_num [PA]⟩
      all_goals exfalso; norm_num [StepShape] at this
    · have h₁ := crossing_north_west hL hsK hsL
      have h₂ := crossing_northEast_northWest hL hdK hdL
      have := stepShape_canonical h₁ h₂ hstep
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨by rw [h₁]; norm_num [PA], by rw [h₂]; norm_num [PB]⟩
      all_goals exfalso; norm_num [StepShape] at this
    · have h₁ := crossing_north_northWest hL hsK hsL
      have h₂ := crossing_northEast_west hL hdK hdL
      have := stepShape_canonical h₁ h₂ hstep
      exfalso
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num [StepShape] at this
  obtain ⟨s₀, d₀, -, h₀⟩ := hmove ⟨0, hn⟩
  have hcover (x : Pos) (hx : x.toPlane = PA ∨ x.toPlane = PB) : x = s₀ ∨ x = d₀ := by
    rcases h₀ with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rcases hx with hx | hx
    · exact Or.inl (Pos.toPlane_injective (hx.trans e₁.symm))
    · exact Or.inr (Pos.toPlane_injective (hx.trans e₂.symm))
    · exact Or.inr (Pos.toPlane_injective (hx.trans e₂.symm))
    · exact Or.inl (Pos.toPlane_injective (hx.trans e₁.symm))
  refine tr.false_of_two_square_moves hl hp hn s₀ d₀ fun i => ?_
  obtain ⟨src, dst, hm, hsd⟩ := hmove i
  refine ⟨src, dst, hm, ?_, ?_⟩
  · rcases hsd with ⟨h, -⟩ | ⟨h, -⟩
    exacts [hcover src (Or.inl h), hcover src (Or.inr h)]
  · rcases hsd with ⟨-, h⟩ | ⟨-, h⟩
    exacts [hcover dst (Or.inr h), hcover dst (Or.inl h)]

/-- Only the lower candidate of Figure 3 remains: the kings are at `K` and
`K + F(3, 1)`, and both half-planes contain the four checking rays. -/
theorem figure3_lower_candidate_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) :
    ∃ (c : Color) (F : LatticeFrame),
      (kp 0 c.opponent).toPlane = (kp 0 c).toPlane + F.apply (3, 1) ∧
      (∀ d, tr.CheckingRay (kp 0 c) c d ↔ d = F.dir .northEast ∨ d = F.dir .north ∨
        d = F.dir .east ∨ d = F.dir .southEast) ∧
      (∀ e, tr.CheckingRay (kp 0 c.opponent) c.opponent e ↔ e = F.dir .west ∨
        e = F.dir .northWest ∨ e = F.dir .south ∨ e = F.dir .southWest) := by
  obtain ⟨c, F, a, b, both, hab, hboth, hL, hu, hv⟩ :=
    tr.figure3_candidates_of_periodic_checks kp hl hk hc hp hn
  by_cases hb : both
  · obtain ⟨rfl, rfl⟩ := hboth hb
    refine ⟨c, F, by simpa using hL, fun d => ?_, fun e => ?_⟩
    · simp only [hu d, hb, true_and]
    · simp only [hv e, hb, true_and]
  · exfalso
    refine tr.false_of_upper_candidate kp hl hk hc hp hn c F a b hab hL (fun d h => ?_)
      (fun e h => ?_)
    · rcases (hu d).mp h with h | h | ⟨h', -⟩
      exacts [Or.inl h, Or.inr h, absurd h' hb]
    · rcases (hv e).mp h with h | h | ⟨h', -⟩
      exacts [Or.inl h, Or.inr h, absurd h' hb]

end MoveTrace

end MPC.Chess
