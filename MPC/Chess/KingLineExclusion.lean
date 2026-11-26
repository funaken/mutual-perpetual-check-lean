import MPC.Chess.CheckingCrossing
import MPC.Chess.KingLineGeometry

/-! Propositions 3.5 and 3.6 for chess. King-line exclusion follows from
periodic legal mutual checks, with no extra immobility or geometric premise. -/

namespace MPC.Chess.MoveTrace

private theorem slider_path {b : Board} {p : Piece} {a k : Pos}
    (hs : p.kind = .queen ∨ p.kind = .rook ∨ p.kind = .bishop)
    (ha : attacks b p a k) : pathClear b a k := by
  rcases hs with hs | hs | hs <;> simp only [attacks, hs] at ha <;> exact ha.2.2

private theorem king_ne_slider (b : Board) (kp : Color → Pos) (hk : MPC.Chess.KingsWellPlaced b kp)
    (c : Color) (q : Pos) (p : Piece) (hq : b q = some p)
    (hs : p.kind = .queen ∨ p.kind = .rook ∨ p.kind = .bishop) : kp c ≠ q := by
  intro he
  have h := hk.king_present c
  rw [he, hq] at h
  have ht := congrArg Piece.kind (Option.some.inj h)
  rcases hs with hs | hs | hs <;> simp [hs] at ht

/-- Proposition 3.5: a non-glaring mover cannot land on the line through the
kings. The same-side witness is already present, and the stripped board retains
the immovable own king; one of them would block the actual before check. -/
theorem openable_destination_off_kingLine_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    ¬ (kp 0 (tr.before i).turn.opponent).collinear (kp 0 (tr.before i).turn) dst := by
  intro hcol
  have hkp := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp
  have hng' : ¬ tr.GlaresAtEnemyKing kp i.succ dst := fun h =>
    hng (tr.glares_source_of_destination_of_periodic_checks kp hl hk hc hp i src dst hm h)
  obtain ⟨j, _, B, Q, _, ho, hs, hA, hall, _⟩ :=
    tr.openable_line_cyclic_of_periodic_checks kp hl hk hc hp i src dst hm hng'
  obtain ⟨_, hQ, Q', hQ', haQ⟩ := hall i.succ (cyclicBetween_self_left _ _)
  have heq : Q' = Q := Option.some.inj (hQ'.symm.trans hQ)
  subst Q'
  rw [ho] at hA
  rw [hkp i.succ 0, ho] at haQ
  have hclearQ := slider_path hs haQ
  have hLnot : ¬ Between B (kp 0 (tr.before i).turn.opponent) (kp 0 (tr.before i).turn) := by
    intro h
    have hz := hclearQ _ h
    have himm := tr.immovableAt_kingPos_of_periodic_checks kp hl hk hc hp 0 (tr.before i).turn
    simp only [strippedBoard, ite_eq_left (Or.inr himm)] at hz
    rw [← hkp i.succ 0, (hk i.succ).king_present] at hz
    contradiction
  have hLK : kp 0 (tr.before i).turn ≠ kp 0 (tr.before i).turn.opponent := by
    intro h
    exact (tr.before i).turn.opponent_ne ((hk 0).positions_injective h).symm
  have hLB : kp 0 (tr.before i).turn ≠ B := by
    rw [← hkp i.succ 0]
    exact king_ne_slider _ _ (hk i.succ) _ B Q hQ hs
  have hblocks := kingLine_blocker_between (attacks_aligned_of_slider hs haQ) hA hcol hLK hLB hLnot
  obtain ⟨C, X, hX, hXo, hslider, haX⟩ := tr.exists_slider_checker_of_periodic_checks kp hl hk hc hp
    (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt) i.castSucc
  have hdst := tr.destination_between_checker_of_periodic_checks kp hl hk hc hp i src dst C X hm hX hXo haX
  rw [hkp i.castSucc 0] at haX
  have hclearX := slider_path hslider haX
  obtain ⟨_, hv, he⟩ := hl i
  have hv' : PseudoLegal (tr.before i) (.boardMove src dst none) := by simpa only [hm] using hv.movement
  obtain ⟨_, _, _, hne, _⟩ := hv'
  have hBs : B ≠ src := by
    intro h; subst B
    have hz : (tr.after i).board src = none := by rw [he, hm]; exact Board.relocate_source _ _ _ _ hne
    change (tr.states i.succ).board src = none at hz
    rw [hQ] at hz; contradiction
  have hBd : B ≠ dst := Ne.symm hA.1
  have hQbefore : (tr.before i).board B = some Q := by
    change (tr.after i).board B = some Q at hQ
    rw [he, hm, show (applyMove (tr.before i) (.boardMove src dst none)).board =
      (tr.before i).board.relocate src dst none from rfl, Board.relocate_other _ _ _ _ _ hBs hBd] at hQ
    exact hQ
  rcases hblocks with hblock | hblock
  · have hz := hclearX _ (between_of_between_tail (attacks_aligned_of_slider hslider haX) hdst hblock).1
    rw [← hkp i.castSucc 0, (hk i.castSucc).king_present] at hz
    contradiction
  · have hz := hclearX _ (between_of_between_tail (attacks_aligned_of_slider hslider haX) hdst hblock).1
    change (tr.before i).board B = none at hz
    rw [hQbefore] at hz; contradiction

private theorem checker_off_kingLine_before (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (q : Pos) (p : Piece)
    (hq : (tr.before i).board q = some p) (ho : p.owner = (tr.before i).turn.opponent)
    (ha : attacks (tr.before i).board p q (kp i.castSucc (tr.before i).turn)) :
    ¬ (kp 0 (tr.before i).turn).collinear (kp 0 (tr.before i).turn.opponent) q := by
  intro hcol
  have hkp := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp
  have hlen : 0 < tr.len := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hslider := tr.checking_piece_is_slider_of_periodic_checks kp hl hk hc hp hlen
    i.castSucc (tr.before i).turn q p hq ho ha
  obtain ⟨src, dst, mover, hm, hsrc, hown, _, _, _, hempty, _⟩ :=
    tr.ordinary_nonKing_nonPawn_move_of_periodic_checks kp hl hk hc hp i
  have hdst := tr.destination_between_checker_of_periodic_checks kp hl hk hc hp i src dst q p hm hq ho ha
  rw [hkp i.castSucc 0] at ha
  have hclear := slider_path hslider ha
  obtain ⟨d, hr⟩ := exists_onRay_of_aligned (attacks_aligned_of_slider hslider ha) ha.1
  obtain ⟨n, hn, hnx, hny⟩ := (onRay_iff_positive_steps _ q d).mp hr
  obtain ⟨j, _, hjx, hjy⟩ := (onRay_iff_positive_steps _ dst d).mp (hr.of_between hdst)
  have hQ : q.toInt = ((kp 0 (tr.before i).turn).toInt.1 + n * d.vector.1,
      (kp 0 (tr.before i).turn).toInt.2 + n * d.vector.2) := Prod.ext hnx hny
  have hD : dst.toInt = ((kp 0 (tr.before i).turn).toInt.1 + j * d.vector.1,
      (kp 0 (tr.before i).turn).toInt.2 + j * d.vector.2) := Prod.ext hjx hjy
  obtain ⟨t, hL⟩ := exists_line_parameter_of_collinear _ _ q d n (by omega) hQ hcol
  have hcolD : (kp 0 (tr.before i).turn).collinear (kp 0 (tr.before i).turn.opponent) dst :=
    collinear_of_line_parameters _ _ _ dst d 0 t j (by simp) hL hD
  have hg : tr.GlaresAtEnemyKing kp i.castSucc src := by
    by_contra hng
    exact tr.openable_destination_off_kingLine_of_periodic_checks kp hl hk hc hp i src dst hm hng
      ((Pos.collinear_swap _ _ _).mp hcolD)
  obtain ⟨p', hp', ho', ha'⟩ := tr.destinationChecker_of_source_glares kp hl hk hc hp i src dst hm hg
  have hs' := tr.checking_piece_is_slider_of_periodic_checks kp hl hk hc hp hlen
    i.succ (tr.before i).turn.opponent dst p' hp' ho' ha'
  rw [hkp i.succ 0] at ha'
  have hclear' := slider_path hs' ha'
  have hLK : kp 0 (tr.before i).turn.opponent ≠ kp 0 (tr.before i).turn := by
    intro h; exact (tr.before i).turn.opponent_ne ((hk 0).positions_injective h)
  have hLQ : kp 0 (tr.before i).turn.opponent ≠ q := by
    rw [← hkp i.castSucc 0]
    exact king_ne_slider _ _ (hk i.castSucc) _ q p hq hslider
  have hLnot : ¬ Between q (kp 0 (tr.before i).turn) (kp 0 (tr.before i).turn.opponent) := by
    intro h
    have hz := hclear _ h
    change (tr.states i.castSucc).board _ = none at hz
    rw [← hkp i.castSucc 0, (hk i.castSucc).king_present] at hz
    contradiction
  have hblocks := kingLine_blocker_between (attacks_aligned_of_slider hslider ha) hdst hcolD hLK hLQ hLnot
  have hqs : q ≠ src := by
    intro h; subst q
    have heq := Option.some.inj (hq.symm.trans hsrc)
    have heo := congrArg Piece.owner heq
    rw [ho, hown] at heo
    exact (tr.before i).turn.opponent_ne heo
  have hqd : q ≠ dst := by intro h; rw [h, hempty] at hq; contradiction
  have hqa : (tr.after i).board q = some p := by
    obtain ⟨_, _, he⟩ := hl i
    rw [he, hm]
    exact (Board.relocate_other _ _ _ _ _ hqs hqd).trans hq
  rcases hblocks with hb | hb
  · have hz := hclear' _ hb
    change (tr.states i.succ).board _ = none at hz
    rw [← hkp i.succ 0, (hk i.succ).king_present] at hz
    contradiction
  · have hz := hclear' _ hb
    rw [hqa] at hz; contradiction

/-- Proposition 3.6 in the capture-free chess period. Every actual checker in
every state is off the line through the kings. Positive length supplies a
reply at the final/initial boundary; it cannot be omitted for empty traces. -/
theorem checker_off_kingLine_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (k : Fin (tr.len + 1))
    (c : Color) (q : Pos) (p : Piece) (hq : (tr.states k).board q = some p)
    (ho : p.owner = c.opponent) (ha : attacks (tr.states k).board p q (kp k c)) :
    ¬ (kp 0 c).collinear (kp 0 c.opponent) q := by
  by_cases he : c = (tr.states k).turn
  · subst c
    revert hq ho ha
    refine Fin.lastCases ?_ (fun i hq ho ha => ?_) k
    · intro hq ho ha
      let first : Fin tr.len := ⟨0, hn⟩
      have hpos := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp (Fin.last tr.len) 0
      rw [hp.1] at hq ha
      rw [hp.2] at ho ha ⊢
      rw [hpos] at ha
      exact tr.checker_off_kingLine_before kp hl hk hc hp first q p hq ho ha
    · exact tr.checker_off_kingLine_before kp hl hk hc hp i q p hq ho ha
  · have he' : c = (tr.states k).turn.opponent := by
      cases c <;> cases ht : (tr.states k).turn <;> simp_all [Color.opponent]
    subst c
    exact (tr.opponent_safe_of_periodic kp hl hk hp hn k ⟨q, p, hq, ho, ha⟩).elim

end MPC.Chess.MoveTrace
