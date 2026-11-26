import MPC.Chess.TraceGlare

/-! Local check classification and the paper's Lemmas 2.4–2.6. The two checker
classes form an inclusive disjunction. An unblocked checker is new at the same
target, not merely a checker away from the destination. -/

namespace MPC.Chess

/-- The actual piece on the destination attacks the designated enemy target. -/
def hasDestinationChecker (b : Board) (dst : Pos) (kingOwner : Color) (target : Pos) : Prop :=
  ∃ p, b dst = some p ∧ p.owner = kingOwner.opponent ∧ attacks b p dst target

/-- A retained non-endpoint piece acquires an attack through the vacated source. -/
def hasUnblockedChecker (before after : Board) (src dst : Pos)
    (kingOwner : Color) (target : Pos) : Prop :=
  ∃ q p, q ≠ src ∧ q ≠ dst ∧ before q = some p ∧ after q = some p ∧
    p.owner = kingOwner.opponent ∧ ¬ attacks before p q target ∧
    attacks after p q target ∧ Between q target src ∧ ¬ Between q target dst

instance (b : Board) (dst : Pos) (c : Color) (t : Pos) :
    Decidable (hasDestinationChecker b dst c t) :=
  inferInstanceAs (Decidable (∃ p, b dst = some p ∧ p.owner = c.opponent ∧ attacks b p dst t))

instance (b a : Board) (s d : Pos) (c : Color) (t : Pos) :
    Decidable (hasUnblockedChecker b a s d c t) :=
  inferInstanceAs (Decidable (∃ q p, q ≠ s ∧ q ≠ d ∧ b q = some p ∧ a q = some p ∧
    p.owner = c.opponent ∧ ¬ attacks b p q t ∧ attacks a p q t ∧
    Between q t s ∧ ¬ Between q t d))

/-- For an unchecked fixed target, every new checker is the moved piece or a
retained piece whose line was blocked by the source. No legality or recurrence
premise is needed for this local board statement. -/
theorem inCheck_relocate_iff_destination_or_unblocked (b : Board) (src dst : Pos)
    (moving : Piece) (c : Color) (target : Pos) (hs : b src = some moving)
    (hne : src ≠ dst) (hb : ¬ inCheck b c target) :
    inCheck (b.relocate src dst none) c target ↔
      hasDestinationChecker (b.relocate src dst none) dst c target ∨
      hasUnblockedChecker b (b.relocate src dst none) src dst c target := by
  constructor
  · rintro ⟨q, p, hq, ho, ha⟩
    by_cases hd : q = dst
    · subst q; exact Or.inl ⟨p, hq, ho, ha⟩
    · right
      have hqs : q ≠ src := by
        intro he; subst q
        rw [Board.relocate_source _ _ _ _ hne] at hq
        contradiction
      have hp : b q = some p := by rwa [Board.relocate_other _ _ _ _ _ hqs hd] at hq
      have hn : ¬ attacks b p q target := fun h => hb ⟨q, p, hp, ho, h⟩
      have hg := new_attack_source_between b src dst moving p q target hs hn ha
      exact ⟨q, p, hqs, hd, hp, hq, ho, hn, ha, hg.2⟩
  · rintro (⟨p, hp, ho, ha⟩ | ⟨q, p, _, _, _, hp, ho, _, ha, _⟩)
    · exact ⟨dst, p, hp, ho, ha⟩
    · exact ⟨q, p, hp, ho, ha⟩

theorem attacks_of_pathClear (S b : Board) (p : Piece) (src dst : Pos)
    (ha : attacks S p src dst) (hc : pathClear b src dst) : attacks b p src dst := by
  rcases p with ⟨c, kind⟩
  cases kind with
  | king | knight | pawn => exact ha
  | queen | rook | bishop => exact ⟨ha.1, ha.2.1, hc⟩

private theorem pos_ext {a b : Pos} (hx : a.toInt.1 = b.toInt.1)
    (hy : a.toInt.2 = b.toInt.2) : a = b := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [Pos.toInt] at hx hy <;> omega

private theorem between_line_cases {a t s : Pos} (ha : a.aligned t) (hs : Between a t s) :
    (a.toInt.1 = t.toInt.1 ∧ s.toInt.1 = a.toInt.1) ∨
    (a.toInt.2 = t.toInt.2 ∧ s.toInt.2 = a.toInt.2) ∨
    (t.toInt.1 - a.toInt.1 = t.toInt.2 - a.toInt.2 ∧
      s.toInt.1 - a.toInt.1 = s.toInt.2 - a.toInt.2) ∨
    (t.toInt.1 - a.toInt.1 = -(t.toInt.2 - a.toInt.2) ∧
      s.toInt.1 - a.toInt.1 = -(s.toInt.2 - a.toInt.2)) := by
  obtain ⟨_, _, hc, hx0, hx1, hy0, hy1⟩ := hs
  rcases ha with h | h | h | h
  · left; constructor; exact h; rw [h] at hx0 hx1; simp only [min_self, max_self] at hx0 hx1; omega
  · right; left; constructor; exact h; rw [h] at hy0 hy1; simp only [min_self, max_self] at hy0 hy1; omega
  · by_cases hz : t.toInt.1 - a.toInt.1 = 0
    · left; constructor; omega; have he : a.toInt.1 = t.toInt.1 := by omega
      rw [he] at hx0 hx1; simp only [min_self, max_self] at hx0 hx1; omega
    · right; right; left; refine ⟨h, ?_⟩
      apply mul_right_cancel₀ hz
      rwa [← h] at hc
  · by_cases hz : t.toInt.1 - a.toInt.1 = 0
    · left; constructor; omega; have he : a.toInt.1 = t.toInt.1 := by omega
      rw [he] at hx0 hx1; simp only [min_self, max_self] at hx0 hx1; omega
    · right; right; right; refine ⟨h, ?_⟩
      apply mul_right_cancel₀ hz
      rw [show t.toInt.2 - a.toInt.2 = -(t.toInt.1 - a.toInt.1) by omega] at hc
      nlinarith only [hc]

/-- The tail of an aligned open segment remains inside it. This covers all
files, ranks and diagonals, in either direction. -/
theorem between_of_between_tail {a t s q : Pos} (ha : a.aligned t)
    (hs : Between a t s) (hq : Between s t q) : Between a t q ∧ q ≠ s := by
  have hl := between_line_cases ha hs
  have hlq := between_line_cases (aligned_of_between ha hs) hq
  have hst : s.toInt.1 ≠ t.toInt.1 ∨ s.toInt.2 ≠ t.toInt.2 := by
    by_contra hn
    push Not at hn
    exact hs.2.1 (pos_ext hn.1 hn.2)
  have hline :
      (a.toInt.1 = t.toInt.1 ∧ q.toInt.1 = a.toInt.1) ∨
      (a.toInt.2 = t.toInt.2 ∧ q.toInt.2 = a.toInt.2) ∨
      (t.toInt.1 - a.toInt.1 = t.toInt.2 - a.toInt.2 ∧
        q.toInt.1 - a.toInt.1 = q.toInt.2 - a.toInt.2) ∨
      (t.toInt.1 - a.toInt.1 = -(t.toInt.2 - a.toInt.2) ∧
        q.toInt.1 - a.toInt.1 = -(q.toInt.2 - a.toInt.2)) := by
    clear ha hs hq
    rcases hl with ⟨h, he⟩ | ⟨h, he⟩ | ⟨h, he⟩ | ⟨h, he⟩
    · left; refine ⟨h, ?_⟩; omega
    · right; left; refine ⟨h, ?_⟩; omega
    · right; right; left; refine ⟨h, ?_⟩; omega
    · right; right; right; refine ⟨h, ?_⟩; omega
  refine ⟨⟨?_, hq.2.1, ?_, ?_⟩, hq.1⟩
  · intro he; subst q
    apply hs.1
    have hb := hs.2.2.2
    have hb' := hq.2.2.2
    clear ha hs hq hl hlq hst hline
    apply pos_ext <;> omega
  · rcases hline with ⟨h, he⟩ | ⟨h, he⟩ | ⟨h, he⟩ | ⟨h, he⟩
    · rw [← h, he]; ring
    · rw [← h, he]; ring
    · rw [h, he]
    · rw [h, he]; ring
  · have hb := hs.2.2.2
    have hb' := hq.2.2.2
    clear ha hs hq hl hlq hst hline
    omega

theorem pathClear_source_of_unblockedChecker (b : Board) (src dst target : Pos)
    (c : Color) (h : hasUnblockedChecker b (b.relocate src dst none) src dst c target) :
    pathClear b src target := by
  obtain ⟨a, p, _, _, _, _, _, hn, ha, hs, hd⟩ := h
  have hk : p.kind = .queen ∨ p.kind = .rook ∨ p.kind = .bishop := by
    cases he : p.kind with
    | king | knight | pawn => exact (hn (by simpa only [attacks, he] using ha)).elim
    | queen => exact Or.inl rfl
    | rook => exact Or.inr (Or.inl rfl)
    | bishop => exact Or.inr (Or.inr rfl)
  have hal := attacks_aligned_of_slider hk ha
  have hc : pathClear (b.relocate src dst none) a target := by
    rcases hk with hk | hk | hk <;> simp only [attacks, hk] at ha <;> exact ha.2.2
  intro q hq
  obtain ⟨hq', hqs⟩ := between_of_between_tail hal hs hq
  have hqd : q ≠ dst := fun he => hd (he ▸ hq')
  simpa only [Board.relocate_other _ _ _ _ _ hqs hqd] using hc q hq'

/-- Lemma 2.5 on boards. Reaching the enemy target on any board (in particular
the stripped board) rules out source-unblocking from a safe before position. -/
theorem not_unblockedChecker_of_source_attacks (b S : Board) (src dst target : Pos)
    (c : Color) (p : Piece) (hs : b src = some p) (ho : p.owner = c.opponent)
    (ha : attacks S p src target) (hb : ¬ inCheck b c target) :
    ¬ hasUnblockedChecker b (b.relocate src dst none) src dst c target := by
  intro hu
  exact hb ⟨src, p, hs, ho, attacks_of_pathClear S b p src target ha
    (pathClear_source_of_unblockedChecker b src dst target c hu)⟩

namespace MoveTrace

/-- A destination checker is a glare; the reverse direction needs more than
removing movable blockers. -/
theorem glares_of_destinationChecker (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (k : Fin (tr.len + 1))
    (dst : Pos) (c : Color)
    (h : hasDestinationChecker (tr.states k).board dst c (kp k c)) :
    tr.GlaresAtEnemyKing kp k dst := by
  obtain ⟨p, hs, ho, ha⟩ := h
  apply tr.glares_of_attacks kp k dst p hs
  simpa only [ho, Color.opponent_opponent] using ha

private theorem boardMove_check_facts (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) :
    ∃ p, (tr.before i).board src = some p ∧ p.owner = (tr.before i).turn ∧ src ≠ dst ∧
      (tr.after i).board = (tr.before i).board.relocate src dst none ∧
      ¬ inCheck (tr.before i).board (tr.before i).turn.opponent
        (kp i.succ (tr.before i).turn.opponent) := by
  obtain ⟨_, hv, he⟩ := hl i
  have hv' : PseudoLegal (tr.before i) (.boardMove src dst none) := by
    simpa only [hm] using hv.movement
  obtain ⟨p, hs, ho, hne, _⟩ := hv'
  refine ⟨p, hs, ho, hne, ?_, ?_⟩
  · rw [he, hm]; rfl
  · rw [tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp i.succ i.castSucc]
    exact tr.opponent_safe_of_periodic kp hl hk hp
      (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt) i.castSucc

theorem destination_or_unblocked_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) :
    hasDestinationChecker (tr.after i).board dst (tr.before i).turn.opponent
        (kp i.succ (tr.before i).turn.opponent) ∨
      hasUnblockedChecker (tr.before i).board (tr.after i).board src dst
        (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) := by
  obtain ⟨p, hs, _, hne, he, hb⟩ := tr.boardMove_check_facts kp hl hk hc hp i src dst hm
  have hcheck := hc i
  rw [he] at hcheck ⊢
  exact (inCheck_relocate_iff_destination_or_unblocked _ src dst p _ _ hs hne hb).mp hcheck

/-- Lemma 2.4: a checking move to a non-glaring square unblocks another piece. -/
theorem unblockedChecker_of_destination_not_glares (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none)
    (hg : ¬ tr.GlaresAtEnemyKing kp i.succ dst) :
    hasUnblockedChecker (tr.before i).board (tr.after i).board src dst
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) := by
  apply (tr.destination_or_unblocked_of_periodic_checks kp hl hk hc hp i src dst hm).resolve_left
  exact fun hd => hg (tr.glares_of_destinationChecker kp i.succ dst _ hd)

/-- Lemma 2.5, with the safe fixed target derived from periodic legal checks. -/
theorem not_unblockedChecker_of_source_glares (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none)
    (hg : tr.GlaresAtEnemyKing kp i.castSucc src) :
    ¬ hasUnblockedChecker (tr.before i).board (tr.after i).board src dst
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) := by
  obtain ⟨p, hs, ho, _, he, hb⟩ := tr.boardMove_check_facts kp hl hk hc hp i src dst hm
  obtain ⟨q, hq, ha⟩ := hg
  have heq : q = p := Option.some.inj (hq.symm.trans hs)
  subst q
  have hat : attacks (tr.strippedBoard i.castSucc src) p src
      (kp i.succ (tr.before i).turn.opponent) := by
    rw [tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp i.succ i.castSucc, ← ho]
    exact ha
  rw [he]
  exact not_unblockedChecker_of_source_attacks _ _ src dst _ _ p hs
    (by simpa using ho) hat hb

theorem destinationChecker_of_source_glares (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none)
    (hg : tr.GlaresAtEnemyKing kp i.castSucc src) :
    hasDestinationChecker (tr.after i).board dst (tr.before i).turn.opponent
      (kp i.succ (tr.before i).turn.opponent) :=
  (tr.destination_or_unblocked_of_periodic_checks kp hl hk hc hp i src dst hm).resolve_right
    (tr.not_unblockedChecker_of_source_glares kp hl hk hc hp i src dst hm hg)

/-- Lemma 2.6. The converse is deferred to the periodic classification argument. -/
theorem destination_glares_of_source_glares (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none)
    (hg : tr.GlaresAtEnemyKing kp i.castSucc src) :
    tr.GlaresAtEnemyKing kp i.succ dst :=
  tr.glares_of_destinationChecker kp i.succ dst _
    (tr.destinationChecker_of_source_glares kp hl hk hc hp i src dst hm hg)

end MoveTrace
end MPC.Chess
