Require Import String.
Require Import List.
Require Import Omega.

Inductive exp :=
| EVar (n: nat)
| EApp (e1 e2: exp)
| ELam (e0: exp)
| ELet (e1 e2: exp)
| ELift (e1: exp)
| ERun (e0 e1: exp)
| EError (msg: string).

Inductive val :=
| VClo (env: list val) (e0: exp)
| VCode (e0: exp)
| VError (msg: string)
.

Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | nil => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

Definition state := (nat * list exp)%type.

Definition fresh (s: state) :=
  match s with
  | (n, acc) => ((n + 1, acc), EVar(n))
  end.

Definition reflect (s: state) (e: exp) :=
  match s with
  | (n, acc) => fresh (n, e::acc)
  end.

Definition reify (se: state * exp) :=
  match se with
  | (s, e) => fold_right ELet e (snd s)
  end.

Fixpoint anf (s: state) (env: list exp) (e: exp): (state * exp) :=
  match e with
  | EVar n => (s, match index n env with
                  | Some v => v
                  | None => EError "unbound var"
                  end)        
  | EApp e1 e2 =>
    match anf s env e1 with
    | (s1, r1) =>
      match anf s1 env e2 with
      | (s2, r2) => reflect s2 (EApp r1 r2)
    end
  end
  | ELam e0 =>
    match fresh s with
    | (s1,v1) =>
      match fresh s1 with
      | (s2, v2) =>
        match anf (fst s2, nil) (v2::v1::env) e0 with
        | (s0, v0) => reflect (fst s, snd s2) (ELam (reify (s0,v0)))
        end
      end
    end
  | ELet e1 e2 =>
    match anf s env e1 with
    | (s1, v1) => anf s1 (v1::env) e2
    end
  | ELift e1 =>
    match anf s env e1 with
    | (s1, v1) => reflect s1 (ELift v1)
    end
  | ERun e0 e1 =>
    match anf s env e0 with
    | (s0, v0) =>
      match anf s0 env e1 with
      | (s1, v1) => reflect s1 (ERun v0 v1)
      end
    end
  | EError msg => (s, e)
  end.

Definition anf0 (e: exp) := reify (anf (0, nil) nil e).

Eval vm_compute in (anf0 (ELam (EVar 1))).

Definition reifyc (sv: state * val) :=
  match sv with
  | (s, VError msg) => EError msg
  | (s, VCode e) => reify (s,e)
  | (s, _) => EError "expected code"
  end.
Definition reflectc s e :=
  match reflect s e with
  | (s, EError msg) => (s, VError msg)
  | (s, v) => (s, VCode v)
  end.
Definition reifyv (sv: state * val) :=
  match sv with
  | ((_, nil), v) => v
  | (s, VError msg) => VError msg
  | (s, VCode e) =>  VCode(reify (s,e))
  | (s, _) => VError "expected code"
  end.

Fixpoint lift (s: state) (fuel: nat) (v: val): (state * exp) :=
  match fuel with
  | 0 => (s, EError "run out of fuel")
  | S fuel =>
    match v with
    | VClo env0 e0 =>
      match fresh s with
      | (s1,v1) =>
        match fresh s1 with
        | (s2, v2) =>
          match ev (fst s2, nil) fuel ((VCode v2)::(VCode v1)::env0) e0 with
          | (s0, VCode r0) => reflect (fst s, snd s2) (ELam (reify (s0,r0)))
          | (s0, VError msg) => (s0, EError msg)
          | (s0, _) => (s0, EError "expected code")
          end
        end
      end
    | VCode e0 => reflect s (ELift e0)
    | VError msg => (s, EError msg)
    end
  end
with ev (s: state) (fuel: nat) (env: list val) (e: exp): (state * val) :=
  match fuel with
  | 0 => (s, VError "run out of fuel")
  | S fuel =>
    match e with
    | EVar n =>
      match index n env with
      | Some v => (s, v)
      | None => (s, VError "unbound var")
      end
    | EApp e1 e2 =>
      match ev s fuel env e1 with
      | (s0, VError msg) => (s0, VError msg)
      | (s0, VClo env0 e0) =>
        match ev s0 fuel env e2 with
        | (s2, VError msg) => (s2, VError msg)
        | (s2, v2) => ev s2 fuel (v2::(VClo env0 e0)::env0) e0
        end
      | (s0, VCode e1) =>
        match ev s0 fuel env e2 with
        | (s2, VError msg) => (s2, VError msg)
        | (s2, VCode e2) => reflectc s2 (EApp e1 e2)
        | (s2, _) => (s2, VError "expected code")
        end
      (*| (s0, _) => (s0, VError "app expected function")*)
      end
    | ELam e0 => (s, VClo env e0)
    | ELet e1 e2 =>
      match ev s fuel env e1 with
      | (s1, VError msg) => (s1, VError msg)
      | (s1, v1) => ev s1 fuel (v1::env) e2
      end
    | ELift e1 =>
      match ev s fuel env e1 with
      | (s1, VError msg) => (s1, VError msg)
      | (s1, v1) =>
        match lift s1 fuel v1 with
        | (s2, EError msg) => (s2, VError msg)
        | (s2, v2) => (s2, VCode v2)
        end
      end
    | ERun e0 e1 =>
      match ev s fuel env e0 with
      | (s0, VError msg) => (s0, VError msg)
      | (s0, VCode v0) =>
        match ev (fst s0, nil) fuel env e1 with
        | (s1, v1) => reflectc s0 (ERun v0 (reifyc (s1,v1)))
        end
      | (s0, _) =>
        match reifyc (ev (length env, snd s0) fuel env e1) with
        | code => (s0, reifyv (ev (fst s0, nil) fuel env code))
        end
      end
    | EError msg => (s, VError msg)
    end
  end.

Definition ev0 e := ev (0, nil) 100 nil e.

Eval vm_compute in ev0 (ELam (EVar 1)).
Eval vm_compute in ev0 (anf0 (ELam (EVar 1))).
Eval vm_compute in ev0 (ELam (ELam (EVar 1))).
Eval vm_compute in ev0 (anf0 (ELam (ELam (EVar 1)))).
Eval vm_compute in reifyc (ev0 (ELift (ELam (EVar 1)))).
Eval vm_compute in (anf0 (ELam (EVar 1))).
Eval vm_compute in reifyc (ev0 (ELift (ELam (ELift (ELam (EVar 1)))))).
Eval vm_compute in (anf0 (ELam (ELam (EVar 1)))).
Eval vm_compute in (ev0 (ERun (ELam (EVar 1)) (ELift (ELam (EVar 1))))).
Eval vm_compute in reifyc (ev0 (ELift (ELam (EApp (EVar 0) (EVar 1))))).

Fixpoint to_lifted (e: exp): exp :=
  match e with
  | EVar n => e
  | EApp e1 e2 => EApp (to_lifted e1) (to_lifted e2)
  | ELam e0 => ELift (ELam (to_lifted e0))
  | ELet e1 e2 => ELet (to_lifted e1) (to_lifted e2)
  | ELift e1 => EError "liftlam: lift not allowed"
  | ERun e0 e1 => EError "liftlam: run not allowed"
  | EError msg => e
  end.

Eval vm_compute in (anf0 (ELam (ELam (EApp (EVar 3) (EVar 1))))).
(* ELet (ELam (ELet (ELam (ELet (EApp (EVar 3) (EVar 1)) (EVar 4))) (EVar 2))) (EVar 0) *)
Eval vm_compute in (reifyc (ev0 (to_lifted (ELam (ELam (EApp (EVar 3) (EVar 1))))))).

Lemma env_inv1_extend: forall env1 x1,
  (forall n v1, index n env1 = Some v1 -> exists x, v1 = VCode (EVar x)) ->
  (forall n v1, index n ((VCode (EVar x1))::env1) = Some v1 -> exists x, v1 = VCode (EVar x)).
Proof.
  intros.
  simpl in H0.
  case_eq (n =? Datatypes.length env1); intros E.
  rewrite E in H0. inversion H0. eexists. reflexivity.
  rewrite E in H0. eapply H. eapply H0.
Qed.

Lemma env_inv2_extend: forall env1 env2 x1,
    (length env1 = length env2) ->
    (forall n x, index n env1 = Some (VCode (EVar x)) -> index n env2 = Some (EVar x)) ->
    (forall n x, index n ((VCode (EVar x1))::env1) = Some (VCode (EVar x)) -> index n ((EVar x1)::env2) = Some (EVar x)).
Proof.
  intros.
  simpl in H1.
  case_eq (n =? Datatypes.length env1); intros E.
  rewrite E in H1. inversion H1. subst.
  simpl. rewrite <- H. rewrite E. reflexivity.
  simpl. rewrite <- H. rewrite E.
  rewrite E in H1. apply H0. apply H1.
Qed.

Theorem anf_like_lift: forall n, forall fuel, fuel < n -> forall e s env1 env2,
    (length env1 = length env2) ->
    (forall n v1, index n env1 = Some v1 -> exists x, v1 = VCode (EVar x)) ->
    (forall n x, index n env1 = Some (VCode (EVar x)) -> index n env2 = Some (EVar x)) ->
    (exists s' msg, (ev s fuel env1 (to_lifted e)) = (s', VError msg)) \/
    (exists s' n', (ev s fuel env1 (to_lifted e)) = (s', VCode (EVar n')) /\ (anf s env2 e) = (s', (EVar n'))).
Proof.
  intros nMax. induction nMax; intros fuel Hfuel.
  inversion Hfuel.
  intros.
  destruct fuel.
  simpl. left. repeat eexists.
  destruct e.
  - simpl.
    case_eq (index n env1).
    intros v1 Hv.
    specialize (H0 n v1 Hv). destruct H0 as [x1 Hx1].
    rewrite Hx1 in Hv.
    specialize (H1 n x1 Hv). subst. right.
    eexists. eexists. split. reflexivity. rewrite H1. reflexivity.
    intros Hv. left. repeat eexists.
  - simpl.
    edestruct IHnMax; eauto. instantiate (1:=fuel). omega. instantiate (1:=e1) in H2. destruct H2 as [s1 [msg Herr]].
    rewrite Herr. left. repeat eexists.
    destruct H2 as [s1 [n1 [Hev1 Ha1]]].
    rewrite Hev1.
    edestruct IHnMax; eauto. instantiate (1:=fuel). omega. instantiate (1:=e2) in H2. destruct H2 as [s2 [msg Herr]].
    rewrite Herr. left. repeat eexists.
    destruct H2 as [s2 [n2 [Hev2 Ha2]]].
    rewrite Hev2. right. rewrite Ha1. rewrite Ha2.
    unfold reflectc. unfold reflect. simpl.
    destruct s2 as [n2' acc2].
    eexists. eexists. split. reflexivity. reflexivity.
  - simpl. destruct fuel as [| fuel].
    simpl. left. repeat eexists.
    simpl. destruct s as [ns accs]. simpl.
    edestruct IHnMax with (env1:=(VCode (EVar (ns + 1)) :: VCode (EVar ns) :: env1)) (env2:=(EVar (ns + 1))::(EVar ns)::env2); eauto.
    instantiate (1:=fuel). omega.
    simpl. omega.
    apply env_inv1_extend. apply env_inv1_extend. auto.
    apply env_inv2_extend. simpl. omega. apply env_inv2_extend. simpl. omega. auto.
    instantiate (1:=e) in H2. destruct H2 as [s1 [msg Herr]].
    rewrite Herr. left. repeat eexists.
    destruct H2 as [s' [n' [Hev Ha]]].
    rewrite Hev. rewrite Ha. right. repeat eexists.
  - simpl.
    edestruct IHnMax; eauto. instantiate (1:=fuel). omega.
    instantiate (1:=e1) in H2. destruct H2 as [s' [msg Herr]].
    rewrite Herr. left. repeat eexists.
    destruct H2 as [s' [n' [Hev1 Ha1]]].
    rewrite Hev1. rewrite Ha1.
    edestruct IHnMax with (env1:=(VCode (EVar n') :: env1)) (env2:=(EVar n' :: env2)).
    instantiate (1:=fuel). omega.
    simpl. omega.
    apply env_inv1_extend. auto.
    apply env_inv2_extend. simpl. omega. auto.
    destruct H2 as [? [msg Herr]].
    rewrite Herr. left. repeat eexists.
    destruct H2 as [? [? [Hev2 Ha2]]].
    rewrite Hev2. rewrite Ha2. right. repeat eexists.
  - simpl. left. repeat eexists.
  - simpl. left. repeat eexists.
  - simpl. left. repeat eexists.
Qed.

Theorem anf_like_lift0: forall e,
    (exists msg, reifyc (ev0 (to_lifted e)) = EError msg) \/ reifyc (ev0 (to_lifted e)) = anf0 e.
Proof.
  intros. unfold ev0. unfold anf0.
  destruct anf_like_lift with (n:=101) (fuel:=100) (s:=(0,nil):state) (env1:=nil:list val) (env2:=nil:list exp) (e:=e); auto.
  - intros. simpl in H. inversion H.
  - intros. simpl in H. inversion H.
  - destruct H as [s' [msg Herr]].
    rewrite Herr. simpl. left. exists msg. reflexivity.
  - destruct H as [s' [n' [Hev Ha]]].
    rewrite Hev. rewrite Ha. simpl. right. reflexivity.
Qed.