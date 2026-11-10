(* SPDX-License-Identifier: MPL-2.0
   SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

   Rocq leg (PROOF-POLICY §2, route `re-proved`) of secret-types
   N-1, N-2, N-3, N-7, N-8 and N-9.  Mirrors src/SecretTypes/Vars.agda,
   Lang.agda, Lattice/Record.agda, Typing/Generic.agda,
   Noninterference/Statement.agda, Noninterference/Generic.agda,
   Lattice.agda, Lang/Two.agda, Noninterference.agda, Countermodels.agda and
   Noninterference/OutcomeVisibility.agda.

   Prelude only: no `Require` of the standard library, the counterpart of the
   Agda gate's --no-libraries.  No axioms: the `Print Assumptions` commands
   at the end must report "Closed under the global context".

   Universe discipline: Agda's `Set` is `Type` here.  The order, an
   observer's `sees` and the typing derivations are `Type`-valued, as in
   Agda.  Equality of naturals is `Prop` here and a set in Agda; naturals
   have decidable equality, so the two readings coincide. *)

(* ---------------------------------------------------------------------- *)
(* SecretTypes.Vars and SecretTypes.Lattice.Record                         *)

Record Vars := { Var : Type; deq : forall x y : Var, {x = y} + {x <> y} }.

(* What Statement and Typing.Generic are parameterised by: no laws, so the
   countermodels (N-8) can instantiate the statement where a law fails. *)
Record Signature := {
  Carrier : Type;
  le : Carrier -> Carrier -> Type;
  join : Carrier -> Carrier -> Carrier;
  bot : Carrier
}.

Record Lattice := {
  sig :> Signature;
  le_trans : forall x y z, le sig x y -> le sig y z -> le sig x z;
  upper1 : forall x y, le sig x (join sig x y);
  upper2 : forall x y, le sig y (join sig x y)
}.

Record Observer (L : Lattice) := {
  sees : Carrier L -> Type;
  down : forall x y, le L x y -> sees y -> sees x
}.
Arguments sees {L} o _.
Arguments down {L} o {x y} _ _.

Definition principal (L : Lattice) (o : Carrier L) : Observer L :=
  {| sees := fun x => le L x o;
     down := fun x y h v => le_trans L x y o h v |}.

(* ---------------------------------------------------------------------- *)
(* SecretTypes.Lang                                                        *)

Section Lang.
Variable V : Vars.

Definition Store := Var V -> nat.

Inductive Expr := lit (n : nat) | var (x : Var V) | plus (a b : Expr).

Inductive Cmd :=
| skip
| assign (x : Var V) (e : Expr)
| seq (c1 c2 : Cmd)
| ifz (e : Expr) (c1 c2 : Cmd)
| while (e : Expr) (c : Cmd).

Fixpoint eval (s : Store) (e : Expr) : nat :=
  match e with
  | lit n => n
  | var x => s x
  | plus a b => eval s a + eval s b
  end.

(* update x n s y = select (x ≟ᵥ y) n (s y) *)
Definition update (x : Var V) (n : nat) (s : Store) : Store :=
  fun y => if deq V x y then n else s y.

Definition bind {A : Type} (m : option A) (f : A -> option A) : option A :=
  match m with None => None | Some a => f a end.

(* One step of fuel, structural in the command; `prev` is the run at one
   less fuel, None at fuel zero (where a loop does not finish). *)
Fixpoint run (prev : option (Cmd -> Store -> option Store)) (c : Cmd) (s : Store)
  : option Store :=
  match c with
  | skip => Some s
  | assign x e => Some (update x (eval s e) s)
  | seq c1 c2 => bind (run prev c1 s) (run prev c2)
  | ifz e c1 c2 => match eval s e with 0 => run prev c1 s | S _ => run prev c2 s end
  | while e c =>
      match prev with
      | None => None
      | Some p => match eval s e with
                  | 0 => bind (p c s) (p (while e c))
                  | S _ => Some s
                  end
      end
  end.

(* exec of SecretTypes.Lang, clause by clause: sequence and ifz keep the
   fuel; a loop at S f runs its body and re-enters at f; at 0 it is None. *)
Fixpoint exec (f : nat) : Cmd -> Store -> option Store :=
  match f with 0 => run None | S f' => run (Some (exec f')) end.

End Lang.

Arguments lit {V} n.
Arguments var {V} x.
Arguments plus {V} a b.
Arguments skip {V}.
Arguments assign {V} x e.
Arguments seq {V} c1 c2.
Arguments ifz {V} e c1 c2.
Arguments while {V} e c.
Arguments eval {V} s e.
Arguments update {V} x n s _.
Arguments exec {V} f _ _.

(* ---------------------------------------------------------------------- *)
(* SecretTypes.Typing.Generic and Noninterference.Statement                *)

Section Typing.
Context {V : Vars} (S : Signature) (label : Var V -> Carrier S).

Fixpoint lab (e : Expr V) : Carrier S :=
  match e with
  | lit _ => bot S
  | var x => label x
  | plus a b => join S (lab a) (lab b)
  end.

Inductive Typed : Carrier S -> Cmd V -> Type :=
| t_skip : forall pc, Typed pc skip
| t_assign : forall pc x e, le S (join S pc (lab e)) (label x) -> Typed pc (assign x e)
| t_seq : forall pc c1 c2, Typed pc c1 -> Typed pc c2 -> Typed pc (seq c1 c2)
| t_ifz : forall pc e c1 c2, Typed (join S pc (lab e)) c1 ->
    Typed (join S pc (lab e)) c2 -> Typed pc (ifz e c1 c2)
| t_while : forall pc e c, Typed (join S pc (lab e)) c -> Typed pc (while e c).

Definition Agree (sees : Carrier S -> Type) (s s' : Store V) : Prop :=
  forall x, sees (label x) -> s x = s' x.

Definition TINI (sees : Carrier S -> Type) : Prop :=
  forall pc c fuel fuel' s s' t t', Typed pc c -> Agree sees s s' ->
    exec fuel c s = Some t -> exec fuel' c s' = Some t' -> Agree sees t t'.

End Typing.

Arguments t_skip {V S label pc}.
Arguments t_assign {V S label pc x e} _.
Arguments t_seq {V S label pc c1 c2} _ _.
Arguments t_ifz {V S label pc e c1 c2} _ _.
Arguments t_while {V S label pc e c} _.

(* ---------------------------------------------------------------------- *)
(* SecretTypes.Noninterference.Generic                                     *)

Section Proof.
Context {V : Vars} (L : Lattice) (label : Var V -> Carrier L) (O : Observer L).

Notation agree := (Agree L label (sees O)).
Notation typed := (Typed L label).
Notation labe := (lab L label).

Lemma bind_some {A : Type} (m : option A) (f : A -> option A) t :
  bind m f = Some t -> {a : A & (m = Some a) * (f a = Some t)}%type.
Proof. destruct m as [a|]; simpl; intro h; [exists a; split; auto | discriminate]. Defined.

Definition branch (n : nat) (c1 c2 : Cmd V) : Cmd V :=
  match n with 0 => c1 | S _ => c2 end.

Lemma exec_skip f (s : Store V) : exec f skip s = Some s.
Proof. destruct f; reflexivity. Qed.

Lemma exec_assign f x e (s : Store V) : exec f (assign x e) s = Some (update x (eval s e) s).
Proof. destruct f; reflexivity. Qed.

Lemma exec_seq f (c1 c2 : Cmd V) (s : Store V) : exec f (seq c1 c2) s = bind (exec f c1 s) (exec f c2).
Proof. destruct f; reflexivity. Qed.

Lemma exec_ifz f e (c1 c2 : Cmd V) (s : Store V) : exec f (ifz e c1 c2) s = exec f (branch (eval s e) c1 c2) s.
Proof. destruct f; simpl; destruct (eval s e); reflexivity. Qed.

Lemma exec_while_succ f e (c : Cmd V) (s : Store V) :
  exec (S f) (while e c) s =
  match eval s e with 0 => bind (exec f c s) (exec f (while e c)) | S _ => Some s end.
Proof. reflexivity. Qed.

Definition branch_typed pc n c1 c2 (d1 : typed pc c1) (d2 : typed pc c2)
  : typed pc (branch n c1 c2) :=
  match n with 0 => d1 | S _ => d2 end.

Lemma unseen_join pc y : (sees O pc -> False) -> sees O (join L pc y) -> False.
Proof. intros np v. exact (np (down O (upper1 L pc y) v)). Qed.

(* N-2, eval-low *)
Lemma eval_low : forall (e : Expr V) (s s' : Store V), sees O (labe e) -> agree s s' -> eval s e = eval s' e.
Proof.
  induction e as [n|x|a IHa b IHb]; intros s s' v eq; simpl.
  - reflexivity.
  - exact (eq x v).
  - rewrite (IHa s s' (down O (upper1 L _ _) v) eq).
    rewrite (IHb s s' (down O (upper2 L _ _) v) eq). reflexivity.
Qed.

Lemma agree_refl (s : Store V) : agree s s.
Proof. intros x _; reflexivity. Qed.
Lemma agree_symm (s s' : Store V) : agree s s' -> agree s' s.
Proof. intros h x v; symmetry; exact (h x v). Qed.
Lemma agree_trans (s s' s'' : Store V) : agree s s' -> agree s' s'' -> agree s s''.
Proof. intros h k x v; rewrite (h x v); exact (k x v). Qed.

Lemma confine_assign pc x e n (s : Store V) :
  (sees O pc -> False) -> le L (join L pc (labe e)) (label x) -> agree (update x n s) s.
Proof.
  intros np ok y v. unfold update. destruct (deq V x y) as [hxy|hxy].
  - subst y. destruct (unseen_join pc (labe e) np (down O ok v)).
  - reflexivity.
Qed.

(* N-3, confine *)
Lemma confine : forall fuel pc (c : Cmd V) (s t : Store V),
  (sees O pc -> False) -> typed pc c -> exec fuel c s = Some t -> agree t s.
Proof.
  induction fuel as [|f IHf]; intros pc c s t np d; revert s t np;
    induction d as [pc|pc x e ok|pc c1 c2 d1 IH1 d2 IH2|pc e c1 c2 d1 IH1 d2 IH2|pc e c d IH];
    intros s t np h.
  all: try (rewrite exec_skip in h; injection h as <-; apply agree_refl).
  all: try (rewrite exec_assign in h; injection h as <-; exact (confine_assign pc x e _ s np ok)).
  all: try (rewrite exec_seq in h; destruct (bind_some _ _ _ h) as [s1 [h1 h2]];
            exact (agree_trans _ _ _ (IH2 _ _ np h2) (IH1 _ _ np h1))).
  all: try (rewrite exec_ifz in h; pose proof (unseen_join pc (labe e) np) as np';
            destruct (eval s e); [exact (IH1 _ _ np' h) | exact (IH2 _ _ np' h)]).
  - discriminate h.
  - rewrite exec_while_succ in h. pose proof (unseen_join pc (labe e) np) as np'.
    destruct (eval s e).
    + destruct (bind_some _ _ _ h) as [s1 [h1 h2]].
      exact (agree_trans _ _ _ (IHf _ _ _ _ np (t_while d) h2) (IHf _ _ _ _ np' d h1)).
    + injection h as <-; apply agree_refl.
Qed.

(* confineL: a loop whose body is typed under an unseen counter, re-entered
   without re-typing the loop. *)
Lemma confine_loop : forall fuel l (e : Expr V) (c : Cmd V) (s t : Store V),
  (sees O l -> False) -> typed l c -> exec fuel (while e c) s = Some t -> agree t s.
Proof.
  induction fuel as [|f IHf]; intros l e c s t np d h.
  - discriminate h.
  - rewrite exec_while_succ in h. destruct (eval s e).
    + destruct (bind_some _ _ _ h) as [s1 [h1 h2]].
      exact (agree_trans _ _ _ (IHf _ _ _ _ _ np d h2) (confine f _ _ _ _ np d h1)).
    + injection h as <-; apply agree_refl.
Qed.

Fixpoint nat_eq_dec (n m : nat) : {n = m} + {n <> m}.
Proof. decide equality. Defined.

(* Agreement is a family of equations between naturals, hence stable under
   double negation (as in the Agda proof). *)
Lemma agree_stable (s s' : Store V) : ((agree s s' -> False) -> False) -> agree s s'.
Proof.
  intros h x v. destruct (nat_eq_dec (s x) (s' x)) as [e|ne]; [exact e|].
  destruct (h (fun a => ne (a x v))).
Qed.

Lemma by_cases_sees (s s' : Store V) j :
  (sees O j -> agree s s') -> ((sees O j -> False) -> agree s s') -> agree s s'.
Proof.
  intros yes no. apply agree_stable. intro bad.
  apply bad. apply no. intro v. apply bad. exact (yes v).
Qed.

(* N-7, tini *)
Theorem tini : TINI L label (sees O).
Proof.
  intros pc c fuel. revert pc c.
  induction fuel as [|f IHf]; intros pc c fuel' s s' t t' d; revert fuel' s s' t t';
    induction d as [pc|pc x e ok|pc c1 c2 d1 IH1 d2 IH2|pc e c1 c2 d1 IH1 d2 IH2|pc e c d IH];
    intros fuel' s s' t t' eq h h'.
  all: try (rewrite exec_skip in h, h'; injection h as <-; injection h' as <-; exact eq).
  all: try (rewrite exec_assign in h, h'; injection h as <-; injection h' as <-;
            intros y v; unfold update; destruct (deq V x y) as [hxy|hxy];
            [subst y; exact (eval_low e s s' (down O (upper2 L _ _) (down O ok v)) eq)
            | exact (eq y v)]).
  all: try (rewrite exec_seq in h, h';
            destruct (bind_some _ _ _ h) as [s1 [h1 h2]];
            destruct (bind_some _ _ _ h') as [s1' [h1' h2']];
            exact (IH2 _ _ _ _ _ (IH1 _ _ _ _ _ eq h1 h1') h2 h2')).
  all: try (rewrite exec_ifz in h, h';
            apply (by_cases_sees _ _ (join L pc (labe e)));
            [ intro v; pose proof (eval_low e s s' (down O (upper2 L _ _) v) eq) as ge;
              rewrite <- ge in h'; destruct (eval s e);
              [exact (IH1 _ _ _ _ _ eq h h') | exact (IH2 _ _ _ _ _ eq h h')]
            | intro nv;
              exact (agree_trans _ _ _ (confine _ _ _ _ _ nv (branch_typed _ _ _ _ d1 d2) h)
                       (agree_trans _ _ _ eq
                          (agree_symm _ _ (confine _ _ _ _ _ nv (branch_typed _ _ _ _ d1 d2) h')))) ]).
  - discriminate h.
  - destruct fuel' as [|f']; [discriminate h'|].
    apply (by_cases_sees _ _ (join L pc (labe e))).
    + intro v. pose proof (eval_low e s s' (down O (upper2 L _ _) v) eq) as ge.
      rewrite exec_while_succ in h, h'. rewrite <- ge in h'. destruct (eval s e).
      * destruct (bind_some _ _ _ h) as [s1 [h1 h2]].
        destruct (bind_some _ _ _ h') as [s1' [h1' h2']].
        exact (IHf _ _ _ _ _ _ _ (t_while d) (IHf _ _ _ _ _ _ _ d eq h1 h1') h2 h2').
      * injection h as <-; injection h' as <-; exact eq.
    + intro nv.
      exact (agree_trans _ _ _ (confine_loop _ _ _ _ _ _ nv d h)
               (agree_trans _ _ _ eq (agree_symm _ _ (confine_loop _ _ _ _ _ _ nv d h')))).
Qed.

End Proof.

(* ---------------------------------------------------------------------- *)
(* The two-point lattice (SecretTypes.Lattice, Lang.Two, Typing,           *)
(* Noninterference): N-1, and N-2/N-3 at that lattice                      *)

Module Two.

Inductive Label := L | H.

(* A computed predicate, as in SecretTypes.Lattice. *)
Definition le2 (x y : Label) : Type :=
  match x, y with L, _ => unit | H, L => Empty_set | H, H => unit end.

Definition join2 (x y : Label) : Label := match x with L => y | H => H end.

Definition le2_trans x y z : le2 x y -> le2 y z -> le2 x z :=
  match x, y, z with
  | L, _, _ => fun _ _ => tt
  | H, H, H => fun _ _ => tt
  | H, H, L => fun _ k => k
  | H, L, _ => fun h _ => match h with end
  end.

Definition up1 x y : le2 x (join2 x y) := match x with L => match y with L => tt | H => tt end | H => tt end.
Definition up2 x y : le2 y (join2 x y) :=
  match x, y with L, L => tt | L, H => tt | H, L => tt | H, H => tt end.

Definition twoSig : Signature := {| Carrier := Label; le := le2; join := join2; bot := L |}.
Definition twoPoint : Lattice := {| sig := twoSig; le_trans := le2_trans; upper1 := up1; upper2 := up2 |}.

Inductive TVar := lo | hi.
Definition tdeq (x y : TVar) : {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition two : Vars := {| Var := TVar; deq := tdeq |}.

Definition label (x : Var two) : Carrier twoPoint := match x with lo => L | hi => H end.

Definition pair (l h : nat) : Store two := fun x => match x with lo => l | hi => h end.
Definition low (s : Store two) : nat := s lo.
Definition LowEq (s s' : Store two) : Prop := low s = low s'.

Definition publicObserver : Observer twoPoint := principal twoPoint L.

Lemma lowEq_agree s s' : LowEq s s' -> Agree twoPoint label (sees publicObserver) s s'.
Proof. intros eq [|] v; [exact eq | destruct v]. Qed.

Lemma agree_lowEq s s' : Agree twoPoint label (sees publicObserver) s s' -> LowEq s s'.
Proof. intro f. exact (f lo tt). Qed.

(* N-2 at the two-point lattice *)
Lemma eval_low_two (e : Expr two) s s' :
  lab twoPoint label e = L -> LowEq s s' -> eval s e = eval s' e.
Proof.
  intros p eq. apply (eval_low twoPoint label publicObserver e s s').
  - change (le2 (lab twoPoint label e) L). rewrite p. exact tt.
  - exact (lowEq_agree _ _ eq).
Qed.

(* N-3 at the two-point lattice *)
Lemma confine_two (c : Cmd two) fuel s t :
  Typed twoPoint label H c -> exec fuel c s = Some t -> low t = low s.
Proof.
  intros d h. exact (confine twoPoint label publicObserver fuel H c s t
                       (fun v : Empty_set => match v with end) d h lo tt).
Qed.

(* N-1, tini of SecretTypes.Noninterference *)
Theorem tini_two pc (c : Cmd two) fuel fuel' s s' t t' :
  Typed twoPoint label pc c -> LowEq s s' ->
  exec fuel c s = Some t -> exec fuel' c s' = Some t' -> LowEq t t'.
Proof.
  intros d eq h h'. apply agree_lowEq.
  exact (tini twoPoint label publicObserver pc c fuel fuel' s s' t t' d (lowEq_agree _ _ eq) h h').
Qed.

(* N-9, SecretTypes.Noninterference.OutcomeVisibility *)
Definition secretLoop : Cmd two := while (@var two hi) skip.
Definition secretLoopTyped : Typed twoPoint label L secretLoop := t_while t_skip.
Definition s0 : Store two := pair 0 0.
Definition s1 : Store two := pair 0 1.
Lemma lowEquivalent : LowEq s0 s1.
Proof. reflexivity. Qed.

Definition publicOutcome fuel (c : Cmd two) s : option nat :=
  match exec fuel c s with None => None | Some t => Some (low t) end.

Lemma secretLoop_never_finishes : forall fuel, exec fuel secretLoop s0 = None.
Proof.
  induction fuel as [|f IH]; [reflexivity|].
  change (bind (exec f skip s0) (exec f secretLoop) = None).
  rewrite exec_skip. exact IH.
Qed.

Lemma secretLoop_stops fuel : exec (S fuel) secretLoop s1 = Some s1.
Proof. reflexivity. Qed.

Lemma outcome_different : publicOutcome 3 secretLoop s0 <> publicOutcome 3 secretLoop s1.
Proof. discriminate. Qed.

Definition TSNI : Prop :=
  forall pc (c : Cmd two) fuel s s', Typed twoPoint label pc c -> LowEq s s' ->
    publicOutcome fuel c s = publicOutcome fuel c s'.

Theorem termination_sensitive_fails : TSNI -> False.
Proof. intro h. exact (outcome_different (h L secretLoop 3 s0 s1 secretLoopTyped lowEquivalent)). Qed.

End Two.

(* ---------------------------------------------------------------------- *)
(* N-8, SecretTypes.Countermodels                                         *)

Module Countermodels.
Import Two.

Definition std (x : Var two) : Label := match x with lo => L | hi => H end.
Definition withJoin (j : Label -> Label -> Label) : Signature :=
  {| Carrier := Label; le := le2; join := j; bot := L |}.
Definition belowL (x : Label) : Type := le2 x L.

Lemma agree01 (S : Signature) (lb : Var two -> Carrier S) (sees : Carrier S -> Type) :
  (sees (lb hi) -> False) -> Agree S lb sees s0 s1.
Proof. intros n [|] v; [reflexivity | destruct (n v)]. Qed.

Module NoUpper1.
  Definition joinR (x y : Label) : Label := y.
  Definition S := withJoin joinR.
  Lemma not_upper1 : (forall x y, le2 x (joinR x y)) -> False.
  Proof. intro h. destruct (h H L). Qed.
  Definition implicitFlow : Cmd two := ifz (@var two hi) (@assign two lo (lit 0)) (@assign two lo (lit 1)).
  Definition typed : Typed S std L implicitFlow.
  Proof. apply t_ifz; apply t_assign; exact tt. Defined.
  Theorem refutes : TINI S std belowL -> False.
  Proof.
    intro tini. pose proof (tini L implicitFlow 1 1 s0 s1 _ _ typed
      (agree01 S std belowL (fun v : Empty_set => match v with end)) eq_refl eq_refl lo tt) as e.
    discriminate e.
  Qed.
End NoUpper1.

Module NoUpper2.
  Definition joinL (x y : Label) : Label := x.
  Definition S := withJoin joinL.
  Lemma not_upper2 : (forall x y, le2 y (joinL x y)) -> False.
  Proof. intro h. destruct (h L H). Qed.
  Definition explicitFlow : Cmd two := @assign two lo (@var two hi).
  Definition typed : Typed S std L explicitFlow.
  Proof. apply t_assign; exact tt. Defined.
  Theorem refutes : TINI S std belowL -> False.
  Proof.
    intro tini. pose proof (tini L explicitFlow 1 1 s0 s1 _ _ typed
      (agree01 S std belowL (fun v : Empty_set => match v with end)) eq_refl eq_refl lo tt) as e.
    discriminate e.
  Qed.
End NoUpper2.

Module NoDownClosure.
  Definition seesH (x : Label) : Type := x = H.
  Lemma not_down_closed : (forall x y, le2 x y -> seesH y -> seesH x) -> False.
  Proof. intro h. discriminate (h L H tt eq_refl). Qed.
  Definition S := withJoin join2.
  Definition up : Cmd two := @assign two hi (@var two lo).
  Definition typed : Typed S std L up.
  Proof. apply t_assign; exact tt. Defined.
  Definition t0 : Store two := pair 0 0.
  Definition t1 : Store two := pair 1 0.
  Lemma agree : Agree S std seesH t0 t1.
  Proof. intros [|] v; [discriminate v | reflexivity]. Qed.
  Theorem refutes : TINI S std seesH -> False.
  Proof.
    intro tini. pose proof (tini L up 1 1 t0 t1 _ _ typed agree eq_refl eq_refl hi eq_refl) as e.
    discriminate e.
  Qed.
End NoDownClosure.

Module NoTrans.
  Inductive P := B | H' | M | L' | T.
  Inductive Le : P -> P -> Type :=
  | le_refl : forall x, Le x x
  | le_bot : forall x, Le B x
  | le_top : forall x, Le x T
  | le_HM : Le H' M
  | le_ML : Le M L'.
  Definition joinP (x y : P) : P :=
    match x, y with
    | B, y => y | T, _ => T
    | H', B => H' | H', H' => H' | H', M => M | H', L' => T | H', T => T
    | M, B => M | M, H' => M | M, M => M | M, L' => L' | M, T => T
    | L', B => L' | L', H' => T | L', M => L' | L', L' => L' | L', T => T
    end.
  Lemma not_trans : (forall x y z, Le x y -> Le y z -> Le x z) -> False.
  Proof. intro t. pose proof (t _ _ _ le_HM le_ML) as k. inversion k. Qed.
  Definition S : Signature := {| Carrier := P; le := Le; join := joinP; bot := B |}.
  Definition labelP (x : Var two) : P := match x with lo => M | hi => H' end.
  Definition explicitFlow : Cmd two := @assign two lo (@var two hi).
  Definition typed : Typed S labelP B explicitFlow.
  Proof. apply t_assign; exact le_HM. Defined.
  Definition belowL' (x : P) : Type := Le x L'.
  Lemma agree : Agree S labelP belowL' s0 s1.
  Proof. intros [|] v; [reflexivity | inversion v]. Qed.
  Theorem refutes : TINI S labelP belowL' -> False.
  Proof.
    intro tini. pose proof (tini B explicitFlow 1 1 s0 s1 _ _ typed agree eq_refl eq_refl lo le_ML) as e.
    discriminate e.
  Qed.
End NoTrans.

End Countermodels.

(* Axioms each theorem rests on (PROOF-POLICY §8.4): every line must read
   "Closed under the global context". *)
Print Assumptions eval_low.
Print Assumptions confine.
Print Assumptions tini.
Print Assumptions Two.eval_low_two.
Print Assumptions Two.confine_two.
Print Assumptions Two.tini_two.
Print Assumptions Two.termination_sensitive_fails.
Print Assumptions Countermodels.NoUpper1.refutes.
Print Assumptions Countermodels.NoUpper2.refutes.
Print Assumptions Countermodels.NoDownClosure.refutes.
Print Assumptions Countermodels.NoTrans.refutes.
