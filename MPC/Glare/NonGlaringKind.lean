import MPC.Trace.MutualCheck
/-!
# MPC.Glare.NonGlaringKind

Non-glaring pieces keep their kind in a periodic trace.

For a property `P` of pieces, count the occupied non-glaring squares whose piece
satisfies `P` (`nonGlaringSquaresOf`). The counting argument of Lemmas 2.8/2.9
(`NonGlaringCount`) carries over to this count while the kings stay put, provided
no board move from a non-glaring square turns a piece without `P` into one with
`P` (`NonGlaringMoveReflects`). Each square counted after a move maps to a
different square counted before it:
- a board move's destination maps back to its source, every other square to itself;
- a drop's destination glares (Lemma 2.7), so it is not counted.
So the count never rises. Promotion is the only way a moved piece changes.

Take for `P` "equal to the piece `p`", where `p` can still promote. A promoted
kind never promotes again, so no move produces `p` and the count never rises. A
non-glaring `p` that promotes leaves the count, so the count drops. In a periodic
trace the count returns to its start, so a non-glaring piece never promotes
(`afterMove_eq_of_not_glares_of_periodic`). Then every board move from a
non-glaring square keeps its piece, and for every `P` the count is the same in
every state (`nonGlaringSquaresOf_card_eq_of_periodic`), as is the count of
openable squares (`openableSquaresOf_card_eq_of_periodic`). Owner and kind
together are one such `P`. -/

namespace MPC

/-- The piece a board move puts on its destination. -/
def Piece.afterMove (p : Piece) (promote : Bool) : Piece :=
  { p with pieceType := if promote then p.pieceType.promote else p.pieceType }

theorem Piece.afterMove_false (p : Piece) : p.afterMove false = p := rfl

/-- Promoted kinds never promote again. -/
theorem PieceType.promote_promote (pt : PieceType) : pt.promote.promote = pt.promote := by
  cases pt <;> rfl

/-- Nothing promotes to a kind that can still promote. -/
theorem PieceType.promote_ne_of_promote_ne {pt pt' : PieceType} (h : pt'.promote ≠ pt') :
    pt.promote ≠ pt' := by
  intro he
  apply h
  rw [← he, PieceType.promote_promote]

/-- A piece of a kind that cannot promote is unchanged by a board move. -/
theorem Piece.afterMove_eq_self {p : Piece} (h : p.pieceType.promote = p.pieceType)
    (promote : Bool) : p.afterMove promote = p := by
  cases promote
  · rfl
  · cases p with
    | mk o pt =>
      show Piece.mk o (if true = true then pt.promote else pt) = Piece.mk o pt
      rw [ite_eq_left rfl]
      exact congrArg (Piece.mk o) h

/-- A board move produces a piece of a kind that can still promote only from that
    same piece. -/
theorem Piece.eq_of_afterMove_eq {p q : Piece} {promote : Bool}
    (hq : q.pieceType.promote ≠ q.pieceType) (h : p.afterMove promote = q) : p = q := by
  cases promote
  · exact h
  · subst h
    exact absurd rfl (PieceType.promote_ne_of_promote_ne (pt := p.pieceType) hq)

namespace MoveTrace

/-- The destination of a board move holds the moved piece. -/
theorem boardMove_grid_dst_of_some (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote) {p : Piece}
    (hp : (tr.before i).board.grid src = some p) :
    (tr.after i).board.grid dst = some (p.afterMove promote) := by
  have h := tr.boardMove_grid_dst ht i src dst promote hm
  rw [hp] at h
  exact h

open Classical in
/-- Occupied squares of state `k` whose piece satisfies `P` and does not glare at
    its enemy king. -/
noncomputable def nonGlaringSquaresOf (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (P : Piece → Prop) (k : Fin (tr.len + 1)) : Finset Pos :=
  Finset.univ.filter fun q =>
    (∃ p, (tr.states k).board.grid q = some p ∧ P p) ∧ ¬ tr.GlaresAtEnemyKing kp k q

theorem mem_nonGlaringSquaresOf (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (P : Piece → Prop) (k : Fin (tr.len + 1)) (q : Pos) :
    q ∈ tr.nonGlaringSquaresOf kp P k ↔
      (∃ p, (tr.states k).board.grid q = some p ∧ P p) ∧ ¬ tr.GlaresAtEnemyKing kp k q := by
  simp only [nonGlaringSquaresOf, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Board move `i` from a non-glaring square never turns a piece without `P` into
    one with `P`. -/
def NonGlaringMoveReflects (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (P : Piece → Prop) (i : Fin tr.len) : Prop :=
  ∀ (src dst : Pos) (promote : Bool) (p : Piece), tr.moves i = .boardMove src dst promote →
    (tr.before i).board.grid src = some p → ¬ tr.GlaresAtEnemyKing kp i.castSucc src →
      P (p.afterMove promote) → P p

/-- A square of the count after a board move is not the move's source. -/
private theorem ne_src_of_mem (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (P : Piece → Prop) (i : Fin tr.len) (src dst : Pos)
    (promote : Bool) (hm : tr.moves i = .boardMove src dst promote) (hsd : src ≠ dst) (q : Pos)
    (hq : q ∈ tr.nonGlaringSquaresOf kp P i.succ) : q ≠ src := by
  rintro rfl
  obtain ⟨⟨p, hp, _⟩, _⟩ := (tr.mem_nonGlaringSquaresOf kp P i.succ q).mp hq
  have h : (tr.states i.succ).board.grid q = none := tr.boardMove_grid_src ht i q dst promote hm hsd
  rw [h] at hp
  cases hp

/-- For a board move, sending the destination back to the source maps the counted
    squares after the move into those before it. -/
private theorem boardMove_mapsTo_of (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (P : Piece → Prop) (i : Fin tr.len) (src dst : Pos)
    (promote : Bool) (hm : tr.moves i = .boardMove src dst promote) (hsd : src ≠ dst)
    (hkp : kp i.succ = kp i.castSucc) (hP : tr.NonGlaringMoveReflects kp P i) (q : Pos)
    (hq : q ∈ tr.nonGlaringSquaresOf kp P i.succ) :
    (if q = dst then src else q) ∈ tr.nonGlaringSquaresOf kp P i.castSucc := by
  obtain ⟨⟨p', hp', hP'⟩, hng⟩ := (tr.mem_nonGlaringSquaresOf kp P i.succ q).mp hq
  by_cases hqd : q = dst
  · subst hqd
    rw [ite_eq_left rfl]
    obtain ⟨piece, hp, _⟩ := hs i src q promote hm
    have hsng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src := fun hg =>
      hng (tr.destination_glares_of_source_glares kp ht hs hk hsafe h0 hc i src q promote hm hg)
    have hdst : (tr.states i.succ).board.grid q = some (piece.afterMove promote) :=
      tr.boardMove_grid_dst_of_some ht i src q promote hm hp
    rw [hdst] at hp'
    have he : piece.afterMove promote = p' := Option.some.inj hp'
    refine (tr.mem_nonGlaringSquaresOf kp P i.castSucc src).mpr ⟨⟨piece, hp, ?_⟩, hsng⟩
    exact hP src q promote piece hm hp hsng (he ▸ hP')
  · rw [ite_eq_right hqd]
    have hqs := ne_src_of_mem tr kp ht P i src dst promote hm hsd q hq
    have hg : (tr.states i.succ).board.grid q = (tr.states i.castSucc).board.grid q :=
      tr.boardMove_grid_other ht i src dst promote q hm hqs hqd
    refine (tr.mem_nonGlaringSquaresOf kp P i.castSucc q).mpr
      ⟨⟨p', hg.symm.trans hp', hP'⟩, ?_⟩
    exact fun h => hng ((tr.glaresAtEnemyKing_congr kp ht hg hkp).mpr h)

private theorem boardMove_injOn_of (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (P : Piece → Prop) (i : Fin tr.len) (src dst : Pos)
    (promote : Bool) (hm : tr.moves i = .boardMove src dst promote) (hsd : src ≠ dst) :
    Set.InjOn (fun q => if q = dst then src else q)
      (tr.nonGlaringSquaresOf kp P i.succ : Set Pos) := by
  intro q₁ h₁ q₂ h₂ he
  have hsrc := ne_src_of_mem tr kp ht P i src dst promote hm hsd
  simp only at he
  by_cases e₁ : q₁ = dst <;> by_cases e₂ : q₂ = dst
  · rw [e₁, e₂]
  · rw [ite_eq_left e₁, ite_eq_right e₂] at he
    exact absurd he.symm (hsrc q₂ h₂)
  · rw [ite_eq_right e₁, ite_eq_left e₂] at he
    exact absurd he (hsrc q₁ h₁)
  · rwa [ite_eq_right e₁, ite_eq_right e₂] at he

/-- A drop's destination glares afterwards, and every other square keeps its piece
    and its glare. -/
private theorem dropMove_subset_of (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (P : Piece → Prop) (i : Fin tr.len) (pt : PieceType)
    (dst : Pos) (hm : tr.moves i = .dropMove pt dst) (hkp : kp i.succ = kp i.castSucc) :
    tr.nonGlaringSquaresOf kp P i.succ ⊆ (tr.nonGlaringSquaresOf kp P i.castSucc).erase dst := by
  intro q hq
  obtain ⟨⟨p', hp', hP'⟩, hng⟩ := (tr.mem_nonGlaringSquaresOf kp P i.succ q).mp hq
  have hqd : q ≠ dst := by
    rintro rfl
    exact hng (tr.dropMove_glares_of_everyMoveChecksOpponent kp ht hs hk hsafe h0 hc i pt q hm)
  have hg : (tr.states i.succ).board.grid q = (tr.states i.castSucc).board.grid q :=
    tr.dropMove_grid_other ht i pt dst q hm hqd
  refine Finset.mem_erase.mpr ⟨hqd, (tr.mem_nonGlaringSquaresOf kp P i.castSucc q).mpr
    ⟨⟨p', hg.symm.trans hp', hP'⟩, ?_⟩⟩
  exact fun h => hng ((tr.glaresAtEnemyKing_congr kp ht hg hkp).mpr h)

/-- While the kings stay put, a move that reflects `P` never raises the count of
    non-glaring squares whose piece satisfies `P`. -/
theorem nonGlaringSquaresOf_card_succ_le (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hd : tr.BoardMoveEndpointsDistinct)
    (P : Piece → Prop) (i : Fin tr.len) (hkp : kp i.succ = kp i.castSucc)
    (hP : tr.NonGlaringMoveReflects kp P i) :
    (tr.nonGlaringSquaresOf kp P i.succ).card ≤
      (tr.nonGlaringSquaresOf kp P i.castSucc).card := by
  rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
  · have hsd := hd i src dst promote hm
    exact Finset.card_le_card_of_injOn _
      (fun q hq => boardMove_mapsTo_of tr kp ht hs hk hsafe h0 hc P i src dst promote hm hsd hkp
        hP q hq)
      (boardMove_injOn_of tr kp ht P i src dst promote hm hsd)
  · exact (Finset.card_le_card
      (dropMove_subset_of tr kp ht hs hk hsafe h0 hc P i pt dst hm hkp)).trans Finset.card_erase_le

/-- Under the same conditions, a board move from a counted square to a square that
    is not counted afterwards lowers the count. -/
theorem nonGlaringSquaresOf_card_succ_lt (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hd : tr.BoardMoveEndpointsDistinct)
    (P : Piece → Prop) (i : Fin tr.len) (hkp : kp i.succ = kp i.castSucc)
    (hP : tr.NonGlaringMoveReflects kp P i) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hsrc : src ∈ tr.nonGlaringSquaresOf kp P i.castSucc)
    (hdst : dst ∉ tr.nonGlaringSquaresOf kp P i.succ) :
    (tr.nonGlaringSquaresOf kp P i.succ).card < (tr.nonGlaringSquaresOf kp P i.castSucc).card := by
  have hsd := hd i src dst promote hm
  refine lt_of_le_of_lt (Finset.card_le_card_of_injOn (fun q => if q = dst then src else q) ?_
    (boardMove_injOn_of tr kp ht P i src dst promote hm hsd)) (Finset.card_erase_lt_of_mem hsrc)
  intro q hq
  have hmap := boardMove_mapsTo_of tr kp ht hs hk hsafe h0 hc P i src dst promote hm hsd hkp hP q hq
  have hqd : q ≠ dst := by
    rintro rfl
    exact hdst hq
  have hqs := ne_src_of_mem tr kp ht P i src dst promote hm hsd q hq
  simp only [ite_eq_right hqd] at hmap ⊢
  exact Finset.mem_erase.mpr ⟨hqs, hmap⟩

/-- A count that never rises along a trace and ends where it started is the same in
    every state. -/
theorem count_eq_initial_of_step_le (n : ℕ) (f : Fin (n + 1) → ℕ)
    (hstep : ∀ i : Fin n, f i.succ ≤ f i.castSucc) (hlast : f (Fin.last n) = f 0)
    (k : Fin (n + 1)) : f k = f 0 := by
  have hmono : ∀ {j l : Fin (n + 1)}, j ≤ l → f l ≤ f j := by
    intro j l hjl
    revert hjl
    induction l using Fin.induction with
    | zero =>
      intro hjl
      rw [Fin.le_zero_iff.mp hjl]
    | succ i ih =>
      intro hjl
      by_cases he : j = i.succ
      · rw [he]
      · have hlt : j < i.succ := Nat.lt_of_le_of_ne hjl fun hv => he (Fin.ext hv)
        exact (hstep i).trans (ih (Fin.le_castSucc_iff.mpr hlt))
  have h1 := hmono (Fin.zero_le k)
  have h2 := hmono (Fin.le_last k)
  omega

private theorem nonGlaringSquaresOf_last (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hk : tr.KingsWellPlaced kp) (hp : tr.IsPeriodic)
    (P : Piece → Prop) :
    tr.nonGlaringSquaresOf kp P (Fin.last tr.len) = tr.nonGlaringSquaresOf kp P 0 := by
  have hgrid : ∀ q, (tr.states (Fin.last tr.len)).board.grid q = (tr.states 0).board.grid q :=
    fun q => by rw [show tr.states (Fin.last tr.len) = tr.states 0 from hp]
  ext q
  rw [tr.mem_nonGlaringSquaresOf, tr.mem_nonGlaringSquaresOf, hgrid q,
    tr.glaresAtEnemyKing_congr kp ht (hgrid q) (hp.kingPos_last hk)]

/-- In a periodic trace, a count reflected by every move is the same in every state. -/
private theorem card_eq_of_reflects (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (P : Piece → Prop) (hP : ∀ i, tr.NonGlaringMoveReflects kp P i)
    (k : Fin (tr.len + 1)) :
    (tr.nonGlaringSquaresOf kp P k).card = (tr.nonGlaringSquaresOf kp P 0).card := by
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  have hconst := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  refine count_eq_initial_of_step_le tr.len (fun k => (tr.nonGlaringSquaresOf kp P k).card)
    (fun i => ?_) ?_ k
  · exact tr.nonGlaringSquaresOf_card_succ_le kp ht hs hk hsafe h0 hc hd P i
      ((hconst _).trans (hconst _).symm) (hP i)
  · exact congrArg Finset.card (nonGlaringSquaresOf_last tr kp ht hk hp P)

/-- Non-glaring pieces never promote: in a periodic mutual-check trace satisfying
    the periodic-check premises, a board move from a non-glaring square puts the same piece on
    its destination. -/
theorem afterMove_eq_of_not_glares_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote) {p : Piece}
    (hpc : (tr.before i).board.grid src = some p)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    p.afterMove promote = p := by
  by_contra hne
  have hpro : p.pieceType.promote ≠ p.pieceType := fun h =>
    hne (Piece.afterMove_eq_self h promote)
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  have hconst := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  -- The non-glaring copies of `p` are never produced by a move.
  have hP : ∀ j, tr.NonGlaringMoveReflects kp (fun x => x = p) j :=
    fun _ _ _ _ _ _ _ _ hx => Piece.eq_of_afterMove_eq hpro hx
  have hlt := tr.nonGlaringSquaresOf_card_succ_lt kp ht hs hk hsafe h0 hc hd (fun x => x = p) i
    ((hconst _).trans (hconst _).symm) (hP i) src dst promote hm
    ((tr.mem_nonGlaringSquaresOf kp _ i.castSucc src).mpr ⟨⟨p, hpc, rfl⟩, hng⟩)
    (by
      intro hmem
      obtain ⟨⟨p', hp', hpp'⟩, _⟩ := (tr.mem_nonGlaringSquaresOf kp _ i.succ dst).mp hmem
      have hdst : (tr.states i.succ).board.grid dst = some (p.afterMove promote) :=
        tr.boardMove_grid_dst_of_some ht i src dst promote hm hpc
      rw [hdst] at hp'
      exact hne ((Option.some.inj hp').trans hpp'))
  have e1 := card_eq_of_reflects tr kp ht hs hk hsafe h0 hc hr hp _ hP i.succ
  have e2 := card_eq_of_reflects tr kp ht hs hk hsafe h0 hc hr hp _ hP i.castSucc
  omega

/-- Under the same premises, the destination of a board move from a non-glaring
    square holds exactly the piece that stood on the source. -/
theorem boardMove_grid_dst_eq_of_not_glares_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    (tr.after i).board.grid dst = (tr.before i).board.grid src := by
  obtain ⟨p, hpc, _⟩ := hs i src dst promote hm
  rw [tr.boardMove_grid_dst_of_some ht i src dst promote hm hpc, hpc,
    tr.afterMove_eq_of_not_glares_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst promote hm
      hpc hng]

/-- Under the same premises, for every property `P` of pieces (for example a given
    owner and kind), the number of non-glaring squares whose piece satisfies `P` is
    the same in every state. -/
theorem nonGlaringSquaresOf_card_eq_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (P : Piece → Prop) (k : Fin (tr.len + 1)) :
    (tr.nonGlaringSquaresOf kp P k).card = (tr.nonGlaringSquaresOf kp P 0).card :=
  card_eq_of_reflects tr kp ht hs hk hsafe h0 hc hr hp P
    (fun i src dst promote p hm hpc hng hPp => by
      rwa [tr.afterMove_eq_of_not_glares_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst
        promote hm hpc hng] at hPp) k

open Classical in
/-- Openable squares of state `k` (`IsOpenableAt`) whose piece satisfies `P`. -/
noncomputable def openableSquaresOf (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (P : Piece → Prop) (k : Fin (tr.len + 1)) : Finset Pos :=
  Finset.univ.filter fun q =>
    (∃ p, (tr.states k).board.grid q = some p ∧ P p) ∧ tr.IsOpenableAt kp k q

theorem mem_openableSquaresOf (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (P : Piece → Prop) (k : Fin (tr.len + 1)) (q : Pos) :
    q ∈ tr.openableSquaresOf kp P k ↔
      (∃ p, (tr.states k).board.grid q = some p ∧ P p) ∧ tr.IsOpenableAt kp k q := by
  simp only [openableSquaresOf, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Under the same premises, for every property `P` of pieces, the number of
    openable squares whose piece satisfies `P` is the same in every state: the
    non-glaring squares that no move touches keep their pieces and their glare. -/
theorem openableSquaresOf_card_eq_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (P : Piece → Prop) (k : Fin (tr.len + 1)) :
    (tr.openableSquaresOf kp P k).card = (tr.openableSquaresOf kp P 0).card := by
  have hconst := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hopen : ∀ k, tr.openableSquaresOf kp P k =
      (tr.nonGlaringSquaresOf kp P k).filter fun q => ¬ tr.ImmovableAt q := by
    intro k
    ext q
    rw [mem_openableSquaresOf, Finset.mem_filter, mem_nonGlaringSquaresOf]
    constructor
    · rintro ⟨hq, _, hng, himm⟩
      exact ⟨⟨hq, hng⟩, himm⟩
    · rintro ⟨⟨⟨p, hpq, hPp⟩, hng⟩, himm⟩
      refine ⟨⟨p, hpq, hPp⟩, ?_, hng, himm⟩
      rw [hpq]
      exact Option.some_ne_none _
  have hsplit : ∀ k, (tr.openableSquaresOf kp P k).card +
      ((tr.nonGlaringSquaresOf kp P k).filter tr.ImmovableAt).card =
        (tr.nonGlaringSquaresOf kp P k).card := by
    intro k
    rw [hopen k, add_comm]
    exact Finset.card_filter_add_card_filter_not _
  have himm : ∀ k, (tr.nonGlaringSquaresOf kp P k).filter tr.ImmovableAt =
      (tr.nonGlaringSquaresOf kp P 0).filter tr.ImmovableAt := by
    intro k
    ext q
    rw [Finset.mem_filter, Finset.mem_filter]
    by_cases hi : tr.ImmovableAt q
    · have hg := tr.immovableAt_grid_eq ht hi k
      rw [mem_nonGlaringSquaresOf, mem_nonGlaringSquaresOf, hg,
        tr.glaresAtEnemyKing_congr kp ht hg (hconst k)]
    · simp only [hi, and_false]
  have hS := tr.nonGlaringSquaresOf_card_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp P k
  have h1 := hsplit k
  have h2 := hsplit 0
  rw [himm k] at h1
  omega

end MoveTrace
end MPC
