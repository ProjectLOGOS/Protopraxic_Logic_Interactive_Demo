(**
  Modal_Decidability_Skeleton.v

  Constructive decision procedures for propositional S5 over a finite model.
  The functions below produce executable witnesses (either satisfaction proofs
  or concrete countermodels) without using classical axioms beyond the finite
  decidability hypotheses supplied to the section.
*)

From Stdlib Require Import List.
Import ListNotations.

From PXL.option_b Require Import Modal_Syntax Modal_Semantics.

Section Decidability.
  (* Finite worlds are represented by a list. *)
  Variable W : Type.
  Variable worlds : list W.

  Variable R : W -> W -> Prop.
  Variable V : nat -> W -> Prop.

  (* Decidability assumptions for the finite model mechanics. *)
  Hypothesis W_eq_dec : forall (x y : W), {x = y} + {x <> y}.
  Hypothesis R_dec    : forall (x y : W), {R x y} + {~ R x y}.
  Hypothesis V_dec    : forall (n : nat) (w : W), {V n w} + {~ V n w}.

  (* Finite cover: every world is listed. This is used to close Box/Dia cases. *)
  Hypothesis worlds_cover : forall w : W, In w worlds.

  (* Local copy of the semantics so we can recurse structurally and stay constructive. *)
  Fixpoint eval (w : W) (phi : MForm) : Prop :=
    match phi with
    | Atom n => V n w
    | Bot    => False
    | And a b => eval w a /\ eval w b
    | Or a b  => eval w a \/ eval w b
    | Imp a b => eval w a -> eval w b
    | Not a   => ~ eval w a
    | Box a   => forall u, R w u -> eval u a
    | Dia a   => exists u, R w u /\ eval u a
    end.

  Lemma eval_atom_conv : forall n w, eval w (Atom n) = V n w.
  Proof. reflexivity. Qed.

  Lemma eval_holds : forall w phi, eval w phi <-> holds W R V w phi.
  Proof.
    intros w phi; revert w.
    induction phi; intro w; simpl.
    - reflexivity.
    - tauto.
    - specialize (IHphi1 w); specialize (IHphi2 w); tauto.
    - specialize (IHphi1 w); specialize (IHphi2 w); tauto.
    - specialize (IHphi1 w); specialize (IHphi2 w); tauto.
    - specialize (IHphi w); tauto.
    - split; intro H.
      + intro u; intro Hr. apply (IHphi u). apply H. exact Hr.
      + intro u; intro Hr. apply (IHphi u). apply H. exact Hr.
    - split; intro H.
      + destruct H as [u [Hr Hu]]. exists u. split; [exact Hr|]. apply (IHphi u). exact Hu.
      + destruct H as [u [Hr Hu]]. exists u. split; [exact Hr|]. apply (IHphi u). exact Hu.
  Qed.

  (* Decide satisfaction for the restricted modal syntax over a finite model. *)
    Fixpoint holds_dec (w : W) (phi : MForm) : {eval w phi} + {~ eval w phi} :=
    match phi with
    | Atom n =>
      match V_dec n w return {eval w (Atom n)} + {~ eval w (Atom n)} with
      | left Hv => left Hv
      | right Hnv => right Hnv
      end
    | Bot    => right (fun H => H)
    | And a b =>
      match holds_dec w a, holds_dec w b with
      | left Ha, left Hb => left (conj Ha Hb)
      | right Hna, _ => right (fun H => Hna (proj1 H))
      | _, right Hnb => right (fun H => Hnb (proj2 H))
      end
    | Or a b =>
      match holds_dec w a, holds_dec w b with
      | left Ha, _ => left (or_introl Ha)
      | _, left Hb => left (or_intror Hb)
      | right Hna, right Hnb =>
        right (fun H => match H with
                   | or_introl Ha => Hna Ha
                   | or_intror Hb => Hnb Hb
                 end)
      end
    | Imp a b =>
      match holds_dec w a, holds_dec w b with
      | left Ha, left Hb => left (fun _ => Hb)
      | left Ha, right Hnb => right (fun H => Hnb (H Ha))
      | right Hna, _ => left (fun Ha => False_rect _ (Hna Ha))
      end
    | Not a =>
      match holds_dec w a with
      | left Ha => right (fun H => H Ha)
      | right Hna => left Hna
      end
    | Box a =>
      let fix check_all (ws : list W) : {forall u, In u ws -> R w u -> eval u a} + {exists u, In u ws /\ R w u /\ ~ eval u a} :=
        match ws with
        | [] => left (fun u Hin _ => False_ind _ (in_nil (A:=W) (a:=u) Hin))
        | u :: ws' =>
          match R_dec w u with
          | left Hru =>
            match holds_dec u a with
            | left Hua =>
              match check_all ws' with
              | left Hall => left (fun u0 Hin Hru0 =>
                match Hin with
                | or_introl Heq =>
                  match Heq in _ = u' return eval u' a with
                  | eq_refl => Hua
                  end
                | or_intror Hin' => Hall u0 Hin' Hru0
                end)
              | right Hex => right (match Hex with
                | ex_intro _ u0 (conj Hin (conj Hru0 Hnua0)) =>
                  ex_intro (fun u1 => In u1 (u :: ws') /\ R w u1 /\ ~ eval u1 a)
                          u0 (conj (or_intror Hin) (conj Hru0 Hnua0))
                end)
              end
            | right Hnua => right (ex_intro (fun u1 => In u1 (u :: ws') /\ R w u1 /\ ~ eval u1 a)
                                         u (conj (or_introl eq_refl) (conj Hru Hnua)))
            end
          | right Hnru =>
            match check_all ws' with
            | left Hall => left (fun u0 Hin Hru0 =>
              match Hin with
              | or_introl Heq =>
                match Heq in _ = u' return R w u' -> eval u' a with
                | eq_refl => fun Hru' => False_rect _ (Hnru Hru')
                end Hru0
              | or_intror Hin' => Hall u0 Hin' Hru0
              end)
            | right Hex => right (match Hex with
              | ex_intro _ u0 (conj Hin (conj Hru0 Hnua0)) =>
                ex_intro (fun u1 => In u1 (u :: ws') /\ R w u1 /\ ~ eval u1 a)
                        u0 (conj (or_intror Hin) (conj Hru0 Hnua0))
              end)
            end
          end
        end in
      match check_all worlds with
      | left Hall =>
        left (fun u Hru => Hall u (worlds_cover u) Hru)
      | right Hex =>
        right (fun Hbox =>
          match Hex with
          | ex_intro _ u (conj Hin (conj Hru Hnha)) => Hnha (Hbox u Hru)
          end)
      end
    | Dia a =>
      let fix find_any (ws : list W) : {exists u, In u ws /\ R w u /\ eval u a} + {forall u, In u ws -> ~ (R w u /\ eval u a)} :=
        match ws with
        | [] => right (fun u Hin => False_ind _ (in_nil (A:=W) (a:=u) Hin))
        | u :: ws' =>
          match R_dec w u with
          | left Hru =>
            match holds_dec u a with
            | left Hua => left (ex_intro (fun u1 => In u1 (u :: ws') /\ R w u1 /\ eval u1 a)
                                      u (conj (or_introl eq_refl) (conj Hru Hua)))
            | right Hnua =>
              match find_any ws' with
              | left Hex => left (match Hex with
                | ex_intro _ u0 (conj Hin (conj Hru0 Hua0)) =>
                  ex_intro (fun u1 => In u1 (u :: ws') /\ R w u1 /\ eval u1 a)
                          u0 (conj (or_intror Hin) (conj Hru0 Hua0))
                end)
              | right Hnone => right (fun u0 Hin =>
                match Hin with
                | or_introl Heq =>
                  match Heq in _ = u' return ~(R w u' /\ eval u' a) with
                  | eq_refl => fun Hpair => Hnua (proj2 Hpair)
                  end
                | or_intror Hin' => Hnone u0 Hin'
                end)
              end
            end
          | right Hnru =>
            match find_any ws' with
            | left Hex => left (match Hex with
              | ex_intro _ u0 (conj Hin (conj Hru0 Hua0)) =>
                ex_intro (fun u1 => In u1 (u :: ws') /\ R w u1 /\ eval u1 a)
                        u0 (conj (or_intror Hin) (conj Hru0 Hua0))
              end)
            | right Hnone => right (fun u0 Hin =>
              match Hin with
              | or_introl Heq =>
                match Heq in _ = u' return ~(R w u' /\ eval u' a) with
                | eq_refl => fun Hpair => Hnru (proj1 Hpair)
                end
              | or_intror Hin' => Hnone u0 Hin'
              end)
            end
          end
        end in
      match find_any worlds with
      | left Hex => left (match Hex with
        | ex_intro _ u (conj _ (conj Hru Hua)) => ex_intro _ u (conj Hru Hua)
        end)
      | right Hnone =>
        right (fun Hdia =>
          match Hdia with
          | ex_intro _ u (conj Hru Hua) =>
            let Hin := worlds_cover u in
            Hnone u Hin (conj Hru Hua)
          end)
      end
    end.

  Lemma holds_dec_total : forall w phi,
    {holds W R V w phi} + {~ holds W R V w phi}.
  Proof.
    intros w phi.
    destruct (holds_dec w phi) as [Heval|Hneval].
    - left. apply (proj1 (eval_holds w phi)). exact Heval.
    - right. intro Hholds. apply Hneval. apply (proj2 (eval_holds w phi)). exact Hholds.
  Qed.

  Definition valid_over (phi : MForm) : Prop :=
    forall w, In w worlds -> eval w phi.

  Definition valid_over_dec (phi : MForm) : {valid_over phi} + {~ valid_over phi}.
  Proof.
  unfold valid_over.
  refine (
    let fix decide (ws : list W) : {forall w, In w ws -> eval w phi} + {~ forall w, In w ws -> eval w phi} :=
      match ws with
      | [] => left (fun w Hin => False_ind _ (in_nil (A:=W) (a:=w) Hin))
      | w :: ws' =>
        match holds_dec w phi with
        | left Hw =>
          match decide ws' with
          | left Hall => left (fun w0 Hin =>
            match Hin with
            | or_introl Heq =>
              match Heq in _ = u return eval u phi with
              | eq_refl => Hw
              end
            | or_intror Hin' => Hall w0 Hin'
            end)
          | right Hnall => right (fun Hforall => Hnall (fun w0 Hin => Hforall w0 (or_intror Hin)))
          end
        | right Hnw => right (fun Hforall => Hnw (Hforall w (or_introl eq_refl)))
        end
      end
    in decide worlds).
  Defined.

  (*
    Stronger decision: either the formula is valid over the finite model, or we return
    a concrete world witnessing failure. Useful for audits and runtime explanations.
  *)
  Definition valid_over_dec_cex (phi : MForm)
    : {valid_over phi} + {exists w, In w worlds /\ ~ eval w phi}.
  Proof.
    unfold valid_over.
    refine (
      let fix decide (ws : list W)
        : {forall w, In w ws -> eval w phi} + {exists w, In w ws /\ ~ eval w phi} :=
        match ws with
        | [] => left (fun w Hin => False_ind _ (in_nil (A:=W) (a:=w) Hin))
        | w :: ws' =>
          match holds_dec w phi with
          | left Hw =>
            match decide ws' with
            | left Hall => left (fun w0 Hin =>
              match Hin with
              | or_introl Heq =>
                match Heq in _ = u return eval u phi with
                | eq_refl => Hw
                end
              | or_intror Hin' => Hall w0 Hin'
              end)
            | right Hex => right (match Hex with
              | ex_intro _ w0 (conj Hin Hn) =>
                ex_intro _ w0 (conj (or_intror Hin) Hn)
              end)
            end
          | right Hnw => right (ex_intro _ w (conj (or_introl eq_refl) Hnw))
          end
        end
      in decide worlds).
  Defined.

  Theorem valid_over_sound : forall phi, valid_over phi -> valid W R V phi.
  Proof.
    intros phi H w.
    unfold valid_over in H.
    specialize (H w (worlds_cover w)).
    apply (proj1 (eval_holds w phi)).
    exact H.
  Qed.
End Decidability.
