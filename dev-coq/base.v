Require Import Arith.
Require Import String.
Require Import List.
Export List ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Require Import Omega.

Inductive op1 :=
| OCar
| OCdr
| OIsNat
| OIsStr
| OIsPair
.

Inductive op2 :=
| OEq
| OPlus
| OMinus
| OTimes
.

Inductive exp :=
| EVar (n: nat)
| EApp (e1 e2: exp)
| ELam (e0: exp)
| ELet (e1 e2: exp)
| ELift (e1: exp)
| ERun (e0 e1: exp)
| ENat (n: nat)
| EStr (t: string)
| EIf (e0 e1 e2: exp)
| ECons (e1 e2: exp)
| EOp1 (op: op1) (e1: exp)
| EOp2 (op: op2) (e1 e2: exp)
| EError (msg: string)
.

Inductive val :=
| VClo (env: list val) (e0: exp)
| VCode (e0: exp)
| VNat (n: nat)
| VStr (t: string)
| VPair (va vd: val)
| VError (msg: string)
.

Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | nil => None
    | cons a l'  => if beq_nat n (length l') then Some a else index n l'
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
  | (s, e) => fold_right ELet e (rev (snd s))
  end.

Fixpoint anf (s: state) (env: list exp) (e: exp): (state * exp) :=
  match e with
  | ENat n => (s, ENat n)
  | EStr t => (s, EStr t)
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
  | EIf e0 e1 e2 =>
    match anf s env e0 with
    | (s0, v0) =>
      reflect s0 (EIf v0
               (reify (anf (fst s0,nil) env e1))
               (reify (anf (fst s0,nil) env e2)))
    end
    | ECons e1 e2 =>
    match anf s env e1 with
    | (s, v1) =>
      match anf s env e2 with
      | (s, v2) => reflect s (ECons v1 v2)
      end
    end
  | EOp1 op e1 =>
    match anf s env e1 with
    | (s, v1) => reflect s (EOp1 op v1)
    end
    | EOp2 op e1 e2 =>
    match anf s env e1 with
    | (s, v1) =>
      match anf s env e2 with
      | (s, v2) => reflect s (EOp2 op v1 v2)
      end
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
    | VNat n => (s, ENat n)
    | VStr t => (s, EStr t)
    | VPair v1 v2 =>
      match (v1, v2) with
      | (VCode e1, VCode e2) => reflect s (ECons e1 e2)
      | _ => (s, EError "expected code")
      end
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
    | ENat n => (s, VNat n)
    | EStr t => (s, VStr t)
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
      | (s0, _) => (s0, VError "app expected function")
      end
    | ELam e0 => (s, VClo env e0)
    | ELet e1 e2 =>
      match ev s fuel env e1 with
      | (s1, VError msg) => (s1, VError msg)
      | (s1, v1) => ev s1 fuel (v1::env) e2
      end
    | EIf e0 e1 e2 =>
      match ev s fuel env e0 with
      | (s0, VNat (S _)) => ev s0 fuel env e1
      | (s0, VNat 0) => ev s0 fuel env e2
      | (s0, VCode v0) =>
        match ((ev (fst s0,nil) fuel env e1),
               (ev (fst s0,nil) fuel env e2)) with
        | ((_, VError msg), _) => (s0, VError msg)
        | (_, (_, VError msg)) => (s0, VError msg)
        | (r1, r2) => reflectc s0 (EIf v0 (reifyc r1) (reifyc r2))
        end
      | (s0, VError msg) => (s0, VError msg)
      | (s0, _) => (s0, VError "expected nat")
      end
    | ECons e1 e2 =>
      match ev s fuel env e1 with
      | (s, VError msg) => (s, VError msg)
      | (s, v1) =>
        match ev s fuel env e2 with
        | (s, VError msg) => (s, VError msg)
        | (s, v2) => (s, VPair v1 v2)
        end
      end
      | EOp1 op e1 =>
      match ev s fuel env e1 with
      | (s, v1) =>
        match (op, v1) with
        | (_, VError msg) => (s, VError msg)
        | (_, VCode v1) => reflectc s (EOp1 op v1)
        | (OCar, VPair va vd) => (s, va)
        | (OCdr, VPair va vd) => (s, vd)
        | (OIsNat, VNat _) => (s, VNat 1)
        | (OIsNat, _) => (s, VNat 0)
        | (OIsStr, VStr _) => (s, VNat 1)
        | (OIsStr, _) => (s, VNat 0)
        | (OIsPair, VPair _ _) => (s, VNat 1)
        | (OIsPair, _) => (s, VNat 0)
        | _ => (s, VError "unexpected op")
        end
      end
    | EOp2 op e1 e2 =>
      match ev s fuel env e1 with
      | (s, v1) =>
        match ev s fuel env e2 with
        | (s, v2) =>
          match (op, v1, v2) with
          | (_, VError msg, _) => (s, VError msg)
          | (_, _, VError msg) => (s, VError msg)
          | (_, VCode v1, VCode v2) => reflectc s (EOp2 op v1 v2)
          | (_, VCode v1, _) => (s, VError "stage error")
          | (_, _, VCode v2) => (s, VError "stage error")
          | (OPlus, VNat n1, VNat n2) => (s, VNat (n1 + n2))
          | (OMinus, VNat n1, VNat n2) => (s, VNat (n1 - n2))
          | (OTimes, VNat n1, VNat n2) => (s, VNat (n1 * n2))
          | (OEq, v1, v2) =>
            (s, VNat (
                    match (v1,v2) with
                    | (VNat n1, VNat n2) => if (beq_nat n1 n2) then 1 else 0
                    | (VStr t1, VStr t2) => if (string_dec t1 t2) then 1 else 0
                    | _ => 0
                    end))
          | _ => (s, VError "unexpected op ")
          end
        end
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
        | (s1, VError msg) => (s1, VError msg)
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
  | ENat n => ELift e
  | EStr t => ELift e
  | EIf e0 e1 e2 => EIf (to_lifted e0) (to_lifted e1) (to_lifted e2)
  | EOp1 op e1 => EOp1 op (to_lifted e1)
  | ECons e1 e2 => ELift (ECons (to_lifted e1) (to_lifted e2))
  | EOp2 op e1 e2 => EOp2 op (to_lifted e1) (to_lifted e2)
  | EError msg => e
  end.

Eval vm_compute in (anf0 (ELam (ELam (EApp (EVar 3) (EVar 1))))).
(* ELet (ELam (ELet (ELam (ELet (EApp (EVar 3) (EVar 1)) (EVar 4))) (EVar 2))) (EVar 0) *)
Eval vm_compute in (reifyc (ev0 (to_lifted (ELam (ELam (EApp (EVar 3) (EVar 1))))))).

Lemma env_inv1_extend: forall env1 e1,
  (forall n v1, index n env1 = Some v1 -> exists e, v1 = VCode e) ->
  (forall n v1, index n ((VCode e1)::env1) = Some v1 -> exists e, v1 = VCode e).
Proof.
  intros.
  simpl in H0.
  case_eq ((n =? Datatypes.length env1)%nat); intros E.
  rewrite E in H0. inversion H0. eexists. reflexivity.
  rewrite E in H0. eapply H. eapply H0.
Qed.

Lemma env_inv2_extend: forall env1 env2 e1,
    (length env1 = length env2) ->
    (forall n e, index n env1 = Some (VCode e) -> index n env2 = Some e) ->
    (forall n e, index n ((VCode e1)::env1) = Some (VCode e) -> index n (e1::env2) = Some e).
Proof.
  intros.
  simpl in H1.
  case_eq ((n =? Datatypes.length env1)%nat); intros E.
  rewrite E in H1. inversion H1. subst.
  simpl. rewrite <- H. rewrite E. reflexivity.
  simpl. rewrite <- H. rewrite E.
  rewrite E in H1. apply H0. apply H1.
Qed.

Theorem anf_like_lift: forall n, forall fuel, fuel < n -> forall e s env1 env2,
    (length env1 = length env2) ->
    (forall n v1, index n env1 = Some v1 -> exists e, v1 = VCode e) ->
    (forall n e, index n env1 = Some (VCode e) -> index n env2 = Some e) ->
    (exists s' msg, (ev s fuel env1 (to_lifted e)) = (s', VError msg)) \/
    (exists s' e', (ev s fuel env1 (to_lifted e)) = (s', VCode e') /\ (anf s env2 e) = (s', e')).
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
    edestruct IHnMax with (env1:=(VCode n' :: env1)) (env2:=(n' :: env2)).
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
  - simpl.
    destruct fuel as [|fuel].
    simpl. left. repeat eexists.
    simpl. right. exists s. exists (ENat n). split. reflexivity. reflexivity.
  - simpl.
    destruct fuel as [|fuel].
    simpl. left. repeat eexists.
    simpl. right. exists s. exists (EStr t). split. reflexivity. reflexivity.
  - simpl.
    edestruct IHnMax; eauto. instantiate (1:=fuel). omega. instantiate (1:=e1) in H2. destruct H2 as [s1 [msg Herr]].
    rewrite Herr. left. repeat eexists.
    destruct H2 as [? [? [Hev Ha]]].
    rewrite Hev. rewrite Ha.
    unfold reflectc. unfold reflect. destruct x. simpl.
    edestruct IHnMax with (fuel:=fuel) (e:=e2) (s:=(n,[]):state); eauto.
    omega. destruct H2 as [? [msg Herr]]. rewrite Herr.
    left. repeat eexists.
    destruct H2 as [? [? [Hev1 Ha1]]].
    rewrite Hev1. rewrite Ha1.
    edestruct IHnMax with (fuel:=fuel) (e:=e3) (s:=(n,[]):state); eauto.
    omega. destruct H2 as [? [msg Herr]]. rewrite Herr.
    left. repeat eexists.
    destruct H2 as [? [? [Hev2 Ha2]]].
    rewrite Hev2. rewrite Ha2.
    right. simpl. repeat eexists.
  - cbv [to_lifted]. fold to_lifted.
    simpl.
    destruct fuel as [| fuel].
    { simpl. left. repeat eexists. }
    simpl.
    edestruct IHnMax with (fuel:=fuel) (e:=e1); eauto. omega.
    destruct H2 as [? [msg Herr]]. rewrite Herr.
    { simpl. left. repeat eexists. }
    destruct H2 as [? [? [Hev Ha]]].
    rewrite Hev. rewrite Ha.
    edestruct IHnMax with (fuel:=fuel) (e:=e2); eauto. omega.
    destruct H2 as [? [? Herr2]]. rewrite Herr2.
    { simpl. left. repeat eexists. }
    destruct H2 as [? [? [Hev2 Ha2]]].
    rewrite Hev2. rewrite Ha2.
    unfold reflectc. unfold reflect. destruct x1. simpl.
    right. repeat eexists.
  - simpl.
    edestruct IHnMax with (fuel:=fuel) (e:=e); eauto. omega.
    destruct H2 as [? [msg Herr]]. rewrite Herr.
    destruct op; left; repeat eexists; reflexivity.
    destruct H2 as [s' [e' [Hev Ha]]].
    rewrite Hev. rewrite Ha.
    unfold reflectc. unfold reflect. destruct s'. simpl.
    destruct op; right; repeat eexists.
  - simpl.
    edestruct IHnMax with (fuel:=fuel) (e:=e1); eauto. omega.
    destruct H2 as [? [msg Herr]]. rewrite Herr.
    edestruct IHnMax with (fuel:=fuel) (e:=e2); eauto. omega.
    destruct H2 as [? [? Herr2]]. rewrite Herr2.
    destruct op; left; repeat eexists; reflexivity.
    destruct H2 as [? [? [Hev2 Ha2]]].
    rewrite Hev2.
    destruct op; left; repeat eexists; reflexivity.
    destruct H2 as [? [? [Hev Ha]]].
    rewrite Hev. rewrite Ha.
    edestruct IHnMax with (fuel:=fuel) (e:=e2); eauto. omega.
    destruct H2 as [? [? Herr2]]. rewrite Herr2.
    destruct op; left; repeat eexists; reflexivity.
    destruct H2 as [? [? [Hev2 Ha2]]].
    rewrite Hev2. rewrite Ha2.
    unfold reflectc. unfold reflect. destruct x1. simpl.
    destruct op; right; repeat eexists.
  - simpl. left. repeat eexists.
Qed.

Theorem anf_like_lift0: forall e,
    (exists msg, reifyc (ev0 (to_lifted e)) = EError msg) \/ reifyc (ev0 (to_lifted e)) = anf0 e.
Proof.
  intros. unfold ev0. unfold anf0.
  edestruct anf_like_lift with (fuel:=100) (s:=(0,nil):state) (env1:=nil:list val) (env2:=nil:list exp) (e:=e); auto.
  - intros. simpl in H. inversion H.
  - intros. simpl in H. inversion H.
  - destruct H as [s' [msg Herr]].
    rewrite Herr. simpl. left. exists msg. reflexivity.
  - destruct H as [s' [n' [Hev Ha]]].
    rewrite Hev. rewrite Ha. simpl. right. reflexivity.
Qed.

Section test_factorial.
  Definition f_self := EVar 0.
  Definition n := EVar 1.
  Definition fac := ELam (EIf n (EOp2 OTimes n (EApp f_self (EOp2 OMinus n (ENat 1)))) (ENat 1)).
  Definition fac4 := Eval vm_compute in ev0 (EApp fac (ENat 4)).
  Print fac4.
  Definition fac_lifted := Eval vm_compute in to_lifted fac.
  Print fac_lifted.
  Definition fac_staged := Eval vm_compute in reifyc (ev0 fac_lifted).
  Print fac_staged.
  Definition fac4' := Eval vm_compute in ev0 (EApp fac_staged (ENat 4)).
  Print fac4'.
  Definition fac_anf := Eval vm_compute in anf0 fac.
  Print fac_anf.
End test_factorial.


Definition n_l := 1.
Definition n_ev := 2.
Definition n_exp := 3.
Definition n_env := 5.
Definition n_end := n_env.

Definition evl_body :=
   (EIf (EOp1 OIsNat (EVar n_exp)) (EApp (EVar n_l) (EVar n_exp))
   (EIf (EOp1 OIsStr (EVar n_exp)) (EApp (EVar n_env) (EVar n_exp))
   (EIf (EOp2 OEq (EStr "quote") (EOp1 OCar (EVar n_exp))) (EApp (EVar n_l) (EOp1 OCar (EOp1 OCdr (EVar n_exp))))
   (EIf (EOp2 OEq (EStr "plus")  (EOp1 OCar (EVar n_exp))) (EOp2 OPlus  (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar n_env)))
   (EIf (EOp2 OEq (EStr "minus") (EOp1 OCar (EVar n_exp))) (EOp2 OMinus (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar n_env)))
   (EIf (EOp2 OEq (EStr "times") (EOp1 OCar (EVar n_exp))) (EOp2 OTimes (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar n_env)))
   (EIf (EOp2 OEq (EStr "eq")    (EOp1 OCar (EVar n_exp))) (EOp2 OEq    (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar n_env)))
   (EIf (EOp2 OEq (EStr "if")    (EOp1 OCar (EVar n_exp))) (EIf (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar n_env)) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EOp1 OCdr (EVar n_exp)))))) (EVar n_env)))
   (EIf (EOp2 OEq (EStr "lam")   (EOp1 OCar (EVar n_exp))) (EApp (EVar n_l) (ELam (*"f" "x"*) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EOp1 OCdr (EVar n_exp)))))) (ELam (*"_" "y"*) (EIf (EOp2 OEq (EVar (n_end+4)(*y*)) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar (n_end+1)(*f*)) (EIf (EOp2 OEq (EVar (n_end+4)(*y*)) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar (n_end+2)(*x*)) (EApp (EVar n_env) (EVar (n_end+4)(*y*)))))))))
   (EIf (EOp2 OEq (EStr "let")   (EOp1 OCar (EVar n_exp))) (ELet (*"x"*) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar n_env)) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EOp1 OCdr (EVar n_exp)))))) (ELam (*"_" "y"*) (EIf (EOp2 OEq (EVar (n_end+3)(*y*)) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar (n_end+1)(*x*)) (EApp (EVar n_env) (EVar (n_end+3)(*y*)))))))
   (EIf (EOp2 OEq (EStr "lift")  (EOp1 OCar (EVar n_exp))) (ELift  (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)))
   (EIf (EOp2 OEq (EStr "isNat") (EOp1 OCar (EVar n_exp))) (EOp1 OIsNat (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)))
   (EIf (EOp2 OEq (EStr "isStr") (EOp1 OCar (EVar n_exp))) (EOp1 OIsStr (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)))
   (EIf (EOp2 OEq (EStr "cons")  (EOp1 OCar (EVar n_exp))) (EApp (EVar n_l) (ECons  (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar n_env))))
   (EIf (EOp2 OEq (EStr "car")   (EOp1 OCar (EVar n_exp))) (EOp1 OCar (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)))
   (EIf (EOp2 OEq (EStr "cdr")   (EOp1 OCar (EVar n_exp))) (EOp1 OCdr (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)))
   (EIf (EOp2 OEq (EStr "app")   (EOp1 OCar (EVar n_exp))) (EApp (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar n_env)))
   (EError "error")
))))))))))))))))).

Definition evl := (ELam (ELam (ELam evl_body))).

Eval vm_compute in (ev0 (EApp (EApp (EApp evl (ELam (EVar 1))) (ENat 5)) (ELam (EError "unbound")))).
Eval vm_compute in (ev0 (EApp (EApp (EApp evl (ELam (EVar 1))) (ECons (EStr "cons") (ECons (ENat 5) (ECons (ENat 6) (EStr "."))))) (ELam (EError "unbound")))).
Eval vm_compute in (ev0 (EApp (EApp (EApp evl (ELam (EVar 1))) (ECons (EStr "app") (ECons (ECons (EStr "lam") (ECons (EStr "_") (ECons (EStr "x") (ECons (ECons (EStr "plus") (ECons (EStr "x") (ECons (ENat 1) (EStr ".")))) (EStr "."))))) (ECons (ENat 2) (EStr (".")))))) (ELam (EError "unbound")))).

Definition op1_to_src (o: op1) := EStr (
  match o with
  | OCar => "car"
  | OCdr => "cdr"
  | OIsNat => "isNat"
  | OIsStr => "isStr"
  | OIsPair => "isPair"
  end).

Definition op2_to_src (o: op2) := EStr (
  match o with
  | OEq => "eq"
  | OPlus => "plus"
  | OMinus => "minus"
  | OTimes => "times"
  end).

Fixpoint to_src (names: list string) (env: list string) (p: exp): exp :=
  match p with
  | EVar x =>
    match index x env with
    | None => EError "unbound var"
    | Some t => EStr t
    end
  | ELam body =>
    match names with
    | [] => EError "name ran out"
    | f::names =>
      match names with
      | [] => EError "name ran out"
      | x::names => ECons (EStr "lam") (ECons (EStr f) (ECons (EStr x) (ECons (to_src names (x::f::env) body) (EStr "."))))
      end
    end
  | ENat n => ENat n
  | EStr s => ECons (EStr "quote") (ECons (EStr s) (EStr "."))
  | ELet e1 e2 =>
    match names with
    | [] => EError "name ran out"
    | x1::names => ECons (EStr "let") (ECons (EStr x1) (ECons (to_src names env e1) (ECons (to_src names env e2) (EStr "."))))
    end
  | EApp e1 e2 => ECons (EStr "app") (ECons (to_src names env e1) (ECons (to_src names env e2) (EStr ".")))
  | EIf e0 e1 e2 => ECons (EStr "if") (ECons (to_src names env e0) (ECons (to_src names env e1) (ECons (to_src names env e2) (EStr "."))))
  | ECons e1 e2 => ECons (EStr "cons") (ECons (to_src names env e1) (ECons (to_src names env e2) (EStr ".")))
  | EOp1 o e1 => ECons (op1_to_src o) (ECons (to_src names env e1) (EStr "."))
  | EOp2 o e1 e2 => ECons (op2_to_src o) (ECons (to_src names env e1) (ECons (to_src names env e2) (EStr ".")))
  | ELift e1 => ECons (EStr "lift") (ECons (to_src names env e1) (EStr "."))
  | ERun e0 e1 => ECons (EStr "run") (ECons (to_src names env e0) (ECons (to_src names env e1) (EStr ".")))
  | EError msg => EError msg
end.

Definition to_src0 e :=
  to_src
    ["x1";"x2";"x3";"x4";"x5";"x6";"x7";"x8";"x9";"x10";"x11";"x12"]
    []
    e.
Definition fac4_src := Eval vm_compute in to_src0 (EApp fac (ENat 4)).
Eval vm_compute in (ev (0,[]) 1000 [] (EApp (EApp (EApp evl (ELam (EVar 1))) fac4_src) (ELam (EError "unbound")))).

(* Proposition 4.2 (Correctness of Interpretation). For any Pink program p, evaluating its
source is observationally equivalent to the program itself: ⟦ (eval p-src) ⟧ ≡ ⟦ p ⟧. *)

(* Proposition 4.3 (Correctness of Compilation). For any Pink program p, compiling and running
its source is observationally equivalent to the program itself: ⟦ (run 0 (evalc p-src)) ⟧ ≡ ⟦ p ⟧. *)

(* Proposition 4.4 (Optimality of Compilation). For any Pink program p, compiling its source
yields exactly the program itself (in ANF): ⟦ (evalc p-src) ⟧ ⇓ ⟦ p ⟧. *)

Lemma inv_app: forall s fuel env e1 e2 r,
  ev s (S fuel) env (EApp e1 e2) = r ->
  (exists s' msg, r = (s', VError msg)) \/
  (exists s0 env0 e0 s2 v2,
      ev s fuel env e1 = (s0, VClo env0 e0) /\
      ev s0 fuel env e2 = (s2, v2) /\
      ev s2 fuel (v2::(VClo env0 e0)::env0) e0 = r) \/
  (exists s0 v1 s2 v2,
      ev s fuel env e1 = (s0, VCode v1) /\
      ev s0 fuel env e2 = (s2, VCode v2) /\
      reflectc s2 (EApp v1 v2) = r).
Proof.
  intros. simpl in H.
  remember (ev s fuel env e1) as r1.
  destruct r1 as [s0 v0].
  remember (ev s0 fuel env e2) as r2.
  destruct r2 as [s2 v2].
  destruct v0; try solve [
                     destruct v2; try solve [right; left; repeat eexists; [symmetry; eapply Heqr2 | subst; reflexivity]];
                     try solve [left; repeat eexists; subst; reflexivity]].
  destruct v2; try solve [left; repeat eexists; subst; reflexivity].
  right. right. repeat eexists. symmetry. eapply Heqr2. eapply H.
Qed.

Lemma inv_app_lam: forall s fuel env e0 e2 r,
    ev s (S fuel) env (EApp (ELam e0) e2) = r ->
    (exists s' msg, r = (s', VError msg)) \/ (exists v2 s2 v1, ev s fuel env e2 = (s2, v2) /\ ev s2 fuel (v2::v1::env) e0 = r).
Proof.
  intros. simpl in H.
  destruct fuel as [| fuel].
  { simpl in H. left. repeat eexists. subst. reflexivity. }
  remember (ev s (S fuel) env (ELam e0)) as rLam.
  simpl in HeqrLam. rewrite HeqrLam in H.
  remember (ev s (S fuel) env e2) as r2.
  destruct r2 as [s2 v2].
  destruct v2; try solve [right; repeat eexists; subst; reflexivity].
  left. repeat eexists. subst. reflexivity.
Qed.

Lemma inv_if_true:  forall s fuel env e0 e1 e2 r s0,
    ev s (S fuel) env (EIf e0 e1 e2) = r ->
    ev s fuel env e0 = (s0, VNat 1) ->
    (ev s0 fuel env e1 = r).
Proof.
  intros. simpl in H. rewrite H0 in H. apply H.
Qed.

Lemma inv_cons: forall s fuel env e1 e2 r,
  ev s (S fuel) env (ECons e1 e2) = r ->
  (exists s' msg, r = (s', VError msg)) \/
  (exists s1 v1 s2 v2,
      ev s  fuel env e1 = (s1,v1) /\
      ev s1 fuel env e2 = (s2,v2) /\
      r = (s2, VPair v1 v2)).
Proof.
  intros. simpl in H.
  remember (ev s fuel env e1) as r1.
  destruct r1 as [s1 v1].
  remember (ev s1 fuel env e2) as r2.
  destruct r2 as [s2 v2].
  destruct v1;
    destruct v2;
    try solve [subst; right; repeat eexists; auto];
    try solve [subst; left; repeat eexists; auto].
Qed.

Fixpoint src_to_val p_src :=
  match p_src with
  | ENat n => VNat n
  | EStr t => VStr t
  | ECons a d => VPair (src_to_val a) (src_to_val d)
  | EError msg => VError msg
  | _ => VError "not source"
  end.

Lemma econs_ind: forall fuel env p1 p2 s v1 v2 r,
    ev s fuel env p1 = (s, v1) ->
    ev s fuel env p2 = (s, v2) ->
    ev s (S fuel) env (ECons p1 p2) = r ->
    (exists msg, (s, VError msg) = r) \/ ((s, VPair v1 v2) = r).
Proof.
  intros. subst. simpl. rewrite H. rewrite H0.
  destruct v1; destruct v2; try solve [right; reflexivity]; try solve [left; eexists; reflexivity].
Qed.

Lemma econs_ind2: forall fuel env p1 p2 s v1 v2 r,
    ev s fuel env p1 = (s, v1) ->
    ev s fuel env p2 = (s, v2) ->
    ev s (S fuel) env (ECons p1 p2) = r ->
    ((exists msg, (VError msg = v1)) /\ (s, v1) = r) \/
    ((forall msg1, (VError msg1 <> v1)) /\ (exists msg, VError msg = v2) /\ (s, v2) = r) \/
    ((forall msg1, (VError msg1 <> v1)) /\ (forall msg2, VError msg2 <> v2) /\ (s, VPair v1 v2) = r).
Proof.
  intros. subst. simpl. rewrite H. rewrite H0.
  destruct v1; destruct v2;
    try solve [right; right; split; try split; try congruence; try reflexivity];
    try solve [right; left; split; try split; try eexists; try congruence; try reflexivity];
    try solve [left; split; try eexists; try congruence; try reflexivity].
Qed.

Lemma econs_ind1err: forall fuel env p1 p2 s msg1,
    ev s fuel env p1 = (s, VError msg1) ->
    ev s (S fuel) env (ECons p1 p2) = (s, VError msg1).
Proof.
  intros. subst. simpl. rewrite H. reflexivity.
Qed.

Lemma econs_ind2err: forall fuel env p1 p2 s v1 msg2,
    ev s fuel env p1 = (s, v1) ->
    (forall msg1, v1 <> VError msg1) ->
    ev s fuel env p2 = (s, VError msg2) ->
    ev s (S fuel) env (ECons p1 p2) = (s, VError msg2).
Proof.
  intros. subst. simpl. rewrite H. rewrite H1.
  destruct v1; try solve [reflexivity].
  congruence.
Qed.

Lemma econs_indv: forall fuel env p1 p2 s v1 v2 r,
    ev s fuel env p1 = (s, v1) ->
    (forall msg1, v1 <> VError msg1) ->
    ev s fuel env p2 = (s, v2) ->
    (forall msg2, v2 <> VError msg2) ->
    ev s (S fuel) env (ECons p1 p2) = r ->
    (s, VPair v1 v2) = r.
Proof.
  intros. subst. simpl. rewrite H. rewrite H1.
  destruct v1; destruct v2; try reflexivity; try congruence.
Qed.

Lemma error_or_not: forall p,
    (exists msg, p = VError msg) \/ (forall msg, p <> VError msg).
Proof.
  intros. destruct p;
            try solve [left; eexists; reflexivity];
            try solve [right; intros; congruence].
Qed.

Lemma src_to_val_not: forall p_src,
    (forall env0 e0, src_to_val p_src <> VClo env0 e0) /\
    (forall e0, src_to_val p_src <> VCode e0).
Proof.
  destruct 0; simpl; split; congruence.
Qed.

Eval vm_compute in ev (0,[]) 100 [(src_to_val (to_src0 (EOp2 OPlus (ENat 1) (ENat 1))));VClo [VClo [] (EVar 1);VNat 0] (ELam evl_body);VClo [] (EVar 1);VNat 0] (EApp (EApp (EVar n_ev) (EVar (n_ev+1))) (ELam (EVar 1))).

Lemma ev_var: forall s fuel env n v,
    index n env = Some v ->
    ev s (S fuel) env (EVar n) = (s, v).
Proof.
  intros. simpl. rewrite H. reflexivity.
Qed.

Lemma ev_str: forall s fuel env t,
    ev s (S fuel) env (EStr t) = (s, VStr t).
Proof.
  intros. simpl. reflexivity.
Qed.

Definition Vid := VClo [] (EVar 1).
Definition Venv := VClo [] (EError "unbound var").
Definition Vev := VClo [Vid;Vid] (ELam evl_body).

Eval vm_compute in ev (0,[]) 100 [Venv;Vid;(src_to_val (to_src0 (EOp2 OPlus (ENat 1) (ENat 1))));Vev;Vid;Vid] evl_body.

Ltac simpl1 H p0 Heqp0 :=
  match goal with
  | [ H : (let (s, v) := ?e in ?body1) = ?r |- _ ] =>
    remember (e) as p0;
    simpl in Heqp0;
    rewrite Heqp0 in H;
    clear Heqp0; clear p0
  end.
Ltac simpl2 H p0 Heqp0 :=
  match goal with
  | [ H : (let (s, v) := let (s2, v2) := ?e in ?body1 in ?body2) = ?r |- _ ] =>
    remember (e) as p0;
    simpl in Heqp0;
    rewrite Heqp0 in H;
    clear Heqp0; clear p0
  end.
Ltac simpl3 H p0 Heqp0 :=
  match goal with
  | [ H : (let (s, v) := let (s2, v2) := let (s3,v3) := ?e in ?body1 in ?body2 in ?body3) = ?r |- _ ] =>
    remember (e) as p0;
    simpl in Heqp0;
    rewrite Heqp0 in H;
    clear Heqp0; clear p0
  end.

Lemma exp_apart_car: forall venv nocare s fuel a d,
    ev s (S (S fuel)) [venv; nocare; VPair a d; Vev; Vid; Vid] (EOp1 OCar (EVar n_exp)) = (s, a).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma exp_apart_cdr: forall venv nocare s fuel a d,
    ev s (S (S fuel)) [venv; nocare; VPair a d; Vev; Vid; Vid] (EOp1 OCdr (EVar n_exp)) = (s, d).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma all_mono: forall fuel0,
    (forall s fuel env e s' v,
        ev s fuel env e = (s', v) -> fuel < fuel0 ->
        (forall msg, v <> VError msg) ->
        ev s (S fuel) env e = (s', v)) /\
    (forall s fuel v s' e,
        lift s fuel v = (s', e) ->  fuel < fuel0 ->
        (forall msg, e <> EError msg) ->
        lift s (S fuel) v = (s', e)).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; destruct fuel; try solve [simpl in H; congruence];
  [destruct e | destruct v].
  - simpl in H.
    case_eq (index n1 env).
    intros v1 E. simpl. rewrite E in *. inversion H. subst. reflexivity.
    intros E. simpl. rewrite E in *. inversion H. congruence.
  - destruct IHn as [IHn1 IHn2].
    remember (S fuel) as Sfuel.
    simpl. rewrite HeqSfuel in *.
    simpl in H.
    remember (ev s fuel env e1) as ev1.
    destruct ev1 as [s1 v1].
    symmetry in Heqev1.
    apply IHn1 in Heqev1.
    rewrite Heqev1.
    remember (ev s1 fuel env e2) as ev2.
    destruct ev2 as [s2 v2].
    symmetry in Heqev2.
    apply IHn1 in Heqev2.
    rewrite Heqev2.
    destruct v1; destruct v2; simpl in H;
      try solve [apply IHn1 in H; [apply H | omega | apply H1]];
      try solve [inversion H; congruence].
    omega.
    destruct v1; destruct v2; simpl in H; congruence.
    omega.
    destruct v1; simpl in H; congruence.
  - simpl in H. simpl. apply H.
  - destruct IHn as [IHn1 IHn2].
    remember (S fuel) as Sfuel.
    simpl. rewrite HeqSfuel in *.
    simpl in H.
    remember (ev s fuel env e1) as ev1.
    destruct ev1 as [s1 v1].
    symmetry in Heqev1.
    apply IHn1 in Heqev1.
    rewrite Heqev1.
    destruct v1; simpl in H;
      try solve [apply IHn1 in H; [apply H | omega | apply H1]];
      try solve [inversion H; congruence].
    omega.
    destruct v1; simpl in H; congruence.
  - destruct IHn as [IHn1 IHn2].
    remember (S fuel) as Sfuel.
    simpl. rewrite HeqSfuel in *.
    simpl in H.
    remember (ev s fuel env e) as ev1.
    destruct ev1 as [s1 v1].
    symmetry in Heqev1.
    apply IHn1 in Heqev1.
    rewrite Heqev1.
    remember (lift s1 fuel v1) as lift1.
    destruct lift1 as [s2 e2].
    symmetry in Heqlift1.
    apply IHn2 in Heqlift1.
    rewrite Heqlift1.
    apply H.
    omega.
    destruct v1; destruct e2; simpl in H; congruence.
    omega.
    destruct v1; simpl in H; congruence.
  - destruct IHn as [IHn1 IHn2].
    remember (S fuel) as Sfuel.
    simpl. rewrite HeqSfuel in *.
    simpl in H.
    remember (ev s fuel env e1) as ev1.
    destruct ev1 as [s1 v1].
    symmetry in Heqev1.
    apply IHn1 in Heqev1.
    rewrite Heqev1.

    unfold reifyv in *. unfold reifyc in *.

    destruct v1.

    remember (ev (Datatypes.length env, snd s1) fuel env e2) as ev2'.
    destruct ev2' as [ s2' v2'].
    symmetry in Heqev2'.
    apply IHn1 in Heqev2'.
    rewrite Heqev2'.
    remember (    ev (fst s1, []) fuel env
      match v2' with
      | VCode e => reify (s2', e)
      | VError msg => EError msg
      | _ => EError "expected code"
      end) as ev2''.
    destruct ev2'' as [s2'' v2''].
    symmetry in Heqev2''.
    apply IHn1 in Heqev2''.
    rewrite Heqev2''. apply H.

    omega. destruct s2''. destruct l. inversion H. subst. apply H1.
    destruct v2''. inversion H. subst. congruence. congruence. congruence. congruence. congruence.
    inversion H. subst. congruence.
    omega.
    destruct v2'. destruct fuel. simpl in H. congruence. congruence. congruence. congruence. congruence. congruence.
    destruct fuel. simpl in H. inversion H. subst. congruence. simpl in H. inversion H. subst. congruence.

    remember (ev (fst s1, []) fuel env e2) as ev2.
    destruct ev2 as [s2 v2].
    symmetry in Heqev2.
    apply IHn1 in Heqev2.
    rewrite Heqev2.
    apply H.
    omega. destruct v2; simpl in H. congruence. congruence. congruence. congruence. congruence. unfold reflectc in H. unfold reflect in H. simpl in H.
    inversion H. subst. apply H1.

    remember (ev (Datatypes.length env, snd s1) fuel env e2) as ev2'.
    destruct ev2' as [ s2' v2'].
    symmetry in Heqev2'.
    apply IHn1 in Heqev2'.
    rewrite Heqev2'.
    remember (    ev (fst s1, []) fuel env
      match v2' with
      | VCode e => reify (s2', e)
      | VError msg => EError msg
      | _ => EError "expected code"
      end) as ev2''.
    destruct ev2'' as [s2'' v2''].
    symmetry in Heqev2''.
    apply IHn1 in Heqev2''.
    rewrite Heqev2''. apply H.

    omega. destruct s2''. destruct l. inversion H. subst. apply H1.
    destruct v2''. inversion H. subst. congruence. congruence. congruence. congruence. congruence.
    inversion H. subst. congruence.
    omega.
    destruct v2'. destruct fuel. simpl in H. congruence. congruence. congruence. congruence. congruence. congruence.
    destruct fuel. simpl in H. inversion H. subst. congruence. simpl in H. inversion H. subst. congruence.

    remember (ev (Datatypes.length env, snd s1) fuel env e2) as ev2'.
    destruct ev2' as [ s2' v2'].
    symmetry in Heqev2'.
    apply IHn1 in Heqev2'.
    rewrite Heqev2'.
    remember (    ev (fst s1, []) fuel env
      match v2' with
      | VCode e => reify (s2', e)
      | VError msg => EError msg
      | _ => EError "expected code"
      end) as ev2''.
    destruct ev2'' as [s2'' v2''].
    symmetry in Heqev2''.
    apply IHn1 in Heqev2''.
    rewrite Heqev2''. apply H.

    omega. destruct s2''. destruct l. inversion H. subst. apply H1.
    destruct v2''. inversion H. subst. congruence. congruence. congruence. congruence. congruence.
    inversion H. subst. congruence.
    omega.
    destruct v2'. destruct fuel. simpl in H. congruence. congruence. congruence. congruence. congruence. congruence.
    destruct fuel. simpl in H. inversion H. subst. congruence. simpl in H. inversion H. subst. congruence.

    remember (ev (Datatypes.length env, snd s1) fuel env e2) as ev2'.
    destruct ev2' as [ s2' v2'].
    symmetry in Heqev2'.
    apply IHn1 in Heqev2'.
    rewrite Heqev2'.
    remember (    ev (fst s1, []) fuel env
      match v2' with
      | VCode e => reify (s2', e)
      | VError msg => EError msg
      | _ => EError "expected code"
      end) as ev2''.
    destruct ev2'' as [s2'' v2''].
    symmetry in Heqev2''.
    apply IHn1 in Heqev2''.
    rewrite Heqev2''. apply H.

    omega. destruct s2''. destruct l. inversion H. subst. apply H1.
    destruct v2''. inversion H. subst. congruence. congruence. congruence. congruence. congruence.
    inversion H. subst. congruence.
    omega.
    destruct v2'. destruct fuel. simpl in H. congruence. congruence. congruence. congruence. congruence. congruence.
    destruct fuel. simpl in H. inversion H. subst. congruence. simpl in H. inversion H. subst. congruence.

    apply H.
    omega.
    destruct v1. congruence. congruence. congruence. congruence. congruence.
    inversion H. subst. apply H1.

  - simpl in H. simpl. apply H.
  - simpl in H. simpl. apply H.
  - destruct IHn as [IHn1 IHn2].
    simpl in H. remember (S fuel) as Sfuel.
    simpl. rewrite HeqSfuel in *.

    remember (ev s fuel env e1) as ev1.
    destruct ev1 as [s0 v0].
    symmetry in Heqev1.
    apply IHn1 in Heqev1.
    rewrite Heqev1.

    destruct v0. apply H.

    remember (ev (fst s0, []) fuel env e2) as ev2.
    destruct ev2 as [s1 v1].
    symmetry in Heqev2.
    apply IHn1 in Heqev2.
    rewrite Heqev2.

    remember (ev (fst s0, []) fuel env e3) as ev3.
    destruct ev3 as [s2 v3].
    symmetry in Heqev3.
    apply IHn1 in Heqev3.
    rewrite Heqev3.

    destruct v1; destruct v3; apply H.

    omega. destruct v1; destruct v3; try congruence.
    omega. destruct v1; try congruence.

    destruct n1.

    remember (ev s0 fuel env e3) as ev2.
    destruct ev2 as [s1 v1].
    symmetry in Heqev2.
    apply IHn1 in Heqev2.
    rewrite Heqev2.
    apply H.
    omega. inversion H. subst. apply H1.

    remember (ev s0 fuel env e2) as ev2.
    destruct ev2 as [s1 v1].
    symmetry in Heqev2.
    apply IHn1 in Heqev2.
    rewrite Heqev2.
    apply H.
    omega. inversion H. subst. apply H1.

    inversion H. subst. reflexivity.
    inversion H. subst. reflexivity.
    inversion H. subst. reflexivity.

    omega. destruct v0; try congruence.

  - simpl in H.
    remember (S fuel) as Sfuel.
    simpl. rewrite HeqSfuel in *.
    destruct IHn as [IHn1 IHn2].
    remember (ev s fuel env e1) as ev1.
    destruct ev1 as [s1 v1].
    symmetry in Heqev1.
    apply IHn1 in Heqev1.
    rewrite Heqev1.
    remember (ev s1 fuel env e2) as ev2.
    destruct ev2 as [s2 v2].
    symmetry in Heqev2.
    apply IHn1 in Heqev2.
    rewrite Heqev2.
    apply H.
    omega. destruct v2; try congruence. destruct v1; try congruence.
    omega. destruct v1; try congruence.

  - simpl in H.
    remember (S fuel) as Sfuel.
    simpl. rewrite HeqSfuel in *.
    destruct IHn as [IHn1 IHn2].
    remember (ev s fuel env e) as ev1.
    destruct ev1 as [s1 v1].
    symmetry in Heqev1.
    apply IHn1 in Heqev1.
    rewrite Heqev1.
    apply H.
    omega. destruct v1; destruct op; try congruence.

  - simpl in H.
    remember (S fuel) as Sfuel.
    simpl. rewrite HeqSfuel in *.
    destruct IHn as [IHn1 IHn2].
    remember (ev s fuel env e1) as ev1.
    destruct ev1 as [s1 v1].
    symmetry in Heqev1.
    apply IHn1 in Heqev1.
    rewrite Heqev1.
    remember (ev s1 fuel env e2) as ev2.
    destruct ev2 as [s2 v2].
    symmetry in Heqev2.
    apply IHn1 in Heqev2.
    rewrite Heqev2.
    apply H.
    omega. destruct v2; destruct op; try congruence; destruct v1; inversion H; subst; congruence.
    omega. destruct v1; try congruence.
    remember (ev s1 fuel env e2) as ev2. destruct ev2 as [s2 v2].
    destruct op; inversion H; subst; congruence.

  - simpl in H. simpl. apply H.
  - remember (S fuel) as Sfuel.
    simpl. rewrite HeqSfuel in *.
    simpl in H.
    remember (fresh s) as fs.
    destruct fs as [s1 v1].
    remember (fresh s1) as fs1.
    destruct fs1 as [s2 v2].
    remember (ev (fst s2, []) fuel (VCode v2 :: VCode v1 :: env) e0) as ev0.
    destruct ev0 as [s0 v0].
    destruct IHn as [IHn1 IHn2].
    symmetry in Heqev0.
    apply IHn1 in Heqev0.
    rewrite Heqev0. apply H.
    omega.
    destruct v0; try congruence.
  - simpl in H. simpl. apply H.
  - simpl in H. simpl. apply H.
  - simpl in H. simpl. apply H.
  - simpl in H. simpl. apply H.
  - simpl. simpl in H. apply H.

Qed.

Lemma ev_fuel_mono: forall fuel s env e s' v,
        ev s fuel env e = (s', v) ->
        (forall msg, v <> VError msg) ->
        ev s (S fuel) env e = (s', v).
Proof.
  intros. eapply all_mono; eauto.
Qed.

Lemma ev_fuel_monotonic_delta: forall d fuel s env e s' v,
        ev s fuel env e = (s', v) ->
        (forall msg, v <> VError msg) ->
        ev s (fuel+d) env e = (s', v).
Proof.
  intros d. induction d; intros.
  - rewrite <- plus_n_O. assumption.
  - rewrite <- plus_n_Sm. eapply ev_fuel_mono; eauto.
Qed.

Lemma ev_fuel_monotonic: forall fuel fuel' s env e s' v,
        fuel' >= fuel ->
        ev s fuel env e = (s', v) ->
        (forall msg, v <> VError msg) ->
        ev s fuel' env e = (s', v).
Proof.
  intros.
  remember (fuel'-fuel) as d.
  assert (fuel'=fuel+d) as A. {
    subst. omega.
  }
  rewrite A. eapply ev_fuel_monotonic_delta; eauto.
Qed.

Lemma lift_fuel_monotonic_delta: forall d fuel s e s' v,
        lift s fuel v = (s', e) ->
        (forall msg, e <> EError msg) ->
        lift s (fuel+d) v = (s', e).
Proof.
  intros d. induction d; intros.
  - rewrite <- plus_n_O. assumption.
  - rewrite <- plus_n_Sm. eapply all_mono; eauto.
Qed.

Lemma lift_fuel_monotonic: forall fuel fuel' s e s' v,
        fuel' >= fuel ->
        lift s fuel v = (s', e) ->
        (forall msg, e <> EError msg) ->
        lift s fuel' v = (s', e).
Proof.
  intros.
  remember (fuel'-fuel) as d.
  assert (fuel'=fuel+d) as A. {
    subst. omega.
  }
  rewrite A. eapply lift_fuel_monotonic_delta; eauto.
Qed.

Lemma same_if_not_err: forall s env e fuel1 s1 v1 fuel2 s2 v2,
    ev s fuel1 env e = (s1, v1) ->
    ev s fuel2 env e = (s2, v2) ->
    (forall msg, v1 <> VError msg) ->
    (forall msg, v2 <> VError msg) ->
    s1=s2 /\ v1=v2.
Proof.
  intros s env e fuel1 s1 v1 fuel2 s2 v2 Hev1 Hev2 Herr1 Herr2.
  destruct (dec_lt fuel1 fuel2) as [Hlt | Hlt].
  apply ev_fuel_monotonic with (fuel':=fuel2) in Hev1. rewrite Hev1 in Hev2. inversion Hev2. subst. split; reflexivity.
  omega. assumption.
  apply ev_fuel_monotonic with (fuel':=fuel1) in Hev2. rewrite Hev1 in Hev2. inversion Hev2. subst. split; reflexivity.
  omega. assumption.
Qed.

Definition Vlift := VClo [] (ELift (EVar 1)).
Definition Vevl := VClo [Vlift;Vid] (ELam evl_body).


      Ltac simpl1g p0 Heqp0 :=
        match goal with
        | [ |- (let (s, v) := ?e in ?body1) = ?r ] =>
          remember (e) as p0;
          simpl in Heqp0;
          rewrite Heqp0;
          clear Heqp0; clear p0
        end.

      Ltac simpl2g p0 Heqp0 :=
        match goal with
        | [ |- (let (s, v) := let (s, v) := ?e in ?body1 in ?body2) = ?r ] =>
          remember (e) as p0;
          simpl in Heqp0;
          rewrite Heqp0;
          clear Heqp0; clear p0
        end.

Theorem opt_compilation: forall n, forall fuel, fuel < n -> forall p s names env' env2 s' v' Venv_self env0 venv,
    Venv_self = VClo [(src_to_val (to_src names env' p));Vevl;Vlift;Vid] evl_body ->
    env0 = [venv;Venv_self;(src_to_val (to_src names env' p));Vevl;Vlift;Vid] ->
    length env' = length env2 ->
    (forall i j xi xj, (index i (names ++ env') = Some xi /\ index j (names ++ env') = Some xj /\ i <> j) -> xi <> xj) ->
    (forall n x s, index n env' = Some x -> exists fuel v, ev s fuel env0 (EApp (EVar n_env) (EStr x)) = (s, v) /\ exists e, v = VCode e) ->
    (forall n x s e, (index n env' = Some x /\ exists fuel, ev s fuel env0 (EApp (EVar n_env) (EStr x)) = (s, VCode e)) -> index n env2 = Some e) ->
    ev s fuel env0 evl_body = (s', v') ->
    (exists msg, v' = VError msg) \/ (exists e', v' = VCode e' /\ (s', e') = (anf s env2 p)).
Proof.
  intros nMax. induction nMax; intros fuel Hfuel.
  inversion Hfuel. unfold n_ev in *. simpl in *.
  intros p s names env' env2 s' e' Venv_self env0 venv HeqVenv_self Heqenv0 L Hdistinct Henv1 Henv2 H.
  destruct fuel.
  simpl in H. inversion H. subst. left. repeat eexists.
  destruct p.
  - simpl in H.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    simpl1 H p0 Heqp0.
    simpl in Heqenv0.
    case_eq (index n0 env').
    intros s0 E. rewrite E in Heqenv0. simpl in Heqenv0.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite ev_var with (v:=VStr s0) in H.
    remember (S fuel) as fuel1.
    simpl in H.
    rewrite Heqfuel1 in H.
    simpl1 H p0 Heqp0.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite ev_var with (v:=VStr s0) in H.
    remember (S fuel) as fuel1'.
    simpl in H.
    rewrite Heqfuel1' in H.
    rewrite ev_var with (v:=venv) in H.
    specialize (Henv1 n0 s0 s E).
    destruct Henv1 as [fuel' [v' [Ha [e0 Hb]]]].
    rewrite Hb in Ha.
    destruct fuel'.
    simpl in Ha. inversion Ha.
    simpl in Ha.
    destruct fuel'.
    simpl in Ha. inversion Ha.
    rewrite ev_var with (v:=venv) in Ha.
    rewrite ev_str in Ha.
    remember (S fuel') as fuel1''.
    destruct venv; simpl in Ha; try congruence.
    rewrite ev_var with (v:=VStr s0) in H.
    subst.
    destruct (error_or_not e') as [[msg Herr] | Hmsg].
    subst. left. repeat eexists.
    eapply same_if_not_err with (s1:=s') (v1:=e') (s2:=s) (v2:=VCode e0) in Hmsg. destruct Hmsg. subst.
    right. exists e0. split. reflexivity. simpl.
    specialize (Henv2 n0 s0 s e0).
    assert (index n0 env' = Some s0 /\
          (exists fuel : nat,
             ev s fuel [VClo env e1; VClo [src_to_val (to_src names env' (EVar n0)); Vevl; Vlift; Vid] evl_body; VStr s0; Vevl; Vlift; Vid]
                (EApp (EVar n_env) (EStr s0)) = (s, VCode e0))) as A. {
      split. apply E.
      exists (S (S fuel')). remember (S fuel') as fuel1'. simpl. rewrite E. rewrite Heqfuel1' in *.
      rewrite ev_var with (v:= VClo env e1).
      rewrite ev_str. eapply Ha.
      unfold n_env. simpl. reflexivity.
    }
    specialize (Henv2 A). rewrite Henv2. reflexivity.
    eapply H. eapply Ha. congruence.
    unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
    unfold n_env. rewrite Heqenv0. simpl. reflexivity.
    unfold n_env. rewrite Heqenv0. simpl. reflexivity.
    unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
    unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
    intros E. rewrite E in Heqenv0. simpl in Heqenv0.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite ev_var with (v:=VError "unbound var") in H.
    inversion H. subst. left. repeat eexists.
    unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
  - admit.
  - simpl in H.
    destruct names as [| f names].
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    simpl1 H p0 Heqp0.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite ev_var with (v:=src_to_val (EError "name ran out")) in H.
    simpl in H. inversion H. subst. left. repeat eexists.
    unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
    destruct names as [| x names].
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    simpl1 H p0 Heqp0.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite ev_var with (v:=src_to_val (EError "name ran out")) in H.
    simpl in H. inversion H. subst. left. repeat eexists.
    unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    simpl1 H p0 Heqp0.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    simpl in Heqenv0.
    rewrite ev_var with (v:=VPair (VStr "lam") (VPair (VStr f) (VPair (VStr x) (VPair (src_to_val (to_src names (x :: f :: env') p)) (VStr "."))))) in H.
    Arguments string_dec: simpl never.
    simpl in H.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite ev_var with (v:=VPair (VStr "lam") (VPair (VStr f) (VPair (VStr x) (VPair (src_to_val (to_src names (x :: f :: env') p)) (VStr "."))))) in H.
    simpl1 H p0 Heqp0.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite ev_str with (t:="quote") in H.
    assert (forall fuel, ev s (S (S fuel)) env0 (EOp1 OCar (EVar n_exp)) = (s, VStr "lam")) as Hcar. {
      intros. simpl. unfold ev. unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
    }
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite (Hcar fuel) in H.
    remember (if string_dec "quote" "lam" then 1 else 0) as b.
    vm_compute in Heqb. rewrite Heqb in H.
    assert (forall fuel op, op <> "lam" ->
      ev s (S (S (S fuel))) env0 (EOp2 OEq (EStr op) (EOp1 OCar (EVar n_exp))) = (s, VNat 0)) as Hno. {
      intros fuel0 op Hnotop.
      remember (S (S fuel0)) as fuel02.
      simpl.
      rewrite Heqfuel02.
      remember (S fuel0) as fuel01.
      rewrite ev_str with (t:=op).
      rewrite Heqfuel01.
      rewrite (Hcar fuel0).
      remember (string_dec op "lam") as cmp.
      case_eq cmp.
      intros. congruence. intros ? Hcmp.
      auto.
    }
    assert (forall fuel op e1 e2, op <> "lam" ->
      ev s (S (S (S (S fuel)))) env0 (EIf (EOp2 OEq (EStr op) (EOp1 OCar (EVar n_exp))) e1 e2) = ev s (S (S (S fuel))) env0 e2) as Helse. {
      intros fuel0 op e1 e2  Hnotop.
      remember (S (S (S fuel0))) as fuel03.
      simpl.
      rewrite Heqfuel03.
      remember (S (S fuel0)) as fuel02.
      simpl.
      rewrite Heqfuel02.
      remember (S fuel0) as fuel01.
      rewrite ev_str with (t:=op).
      rewrite Heqfuel01.
      rewrite (Hcar fuel0).
      remember (string_dec op "lam") as cmp.
      case_eq cmp.
      intros. congruence. intros ? Hcmp.
      auto.
    }
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    remember (S (S (S fuel))) as fuel3.
    simpl in H.
    rewrite Heqfuel3 in H.
    remember (S (S fuel)) as fuel2.
    simpl1 H p0 Heqp0.
    rewrite Heqfuel2 in H.
    rewrite ev_str in H.
    rewrite Hcar in H.
    remember (if string_dec "lam" "lam" then 1 else 0) as c.
    vm_compute in Heqc. rewrite Heqc in H.
    remember (S (S fuel)) as fuel2'.
    simpl in H.
    rewrite Heqfuel2' in H.
    rewrite ev_var with (v:=Vlift) in H.
    unfold Vlift at 1 in H.
    simpl1 H p0 Heqp0.
    remember (S fuel) as fuel1.
    simpl in H.
    rewrite Heqfuel1 in H.
    rewrite ev_var with (v:=VClo env0
              (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))))
                 (ELam
                    (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar 6)
                       (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar 7) (EApp (EVar n_env) (EVar 9))))))) in H.
    simpl1 H p0 Heqp0.
    remember (fresh s) as fs. destruct fs as [s1 v1].
    remember (fresh s1) as fs1. destruct fs1 as [s2 v2].
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    simpl2 H p0 Heqp0.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    simpl3 H p0 Heqp0.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite ev_var with (v:=Vevl) in H.
    unfold Vevl in H.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    remember (ev (fst s2, []) (S (S (S (S fuel))))
                 (VCode v2 :: VCode v1 :: env0)
                 (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EOp1 OCdr (EVar n_exp)))))) as evb.
    rewrite Heqenv0 in Heqevb.
    simpl in Heqevb.
    rewrite Heqevb in H.
    destruct fuel.
    simpl in H. inversion H. subst. left. repeat eexists.
    rewrite ev_var with (v:=VPair (VStr "lam")
                           (VPair (VStr f)
                              (VPair (VStr x)
                                 (VPair
                                    (src_to_val
                                       (to_src names (x :: f :: env') p))
                                    (VStr "."))))) in H.
    remember (src_to_val (to_src names (x :: f :: env') p)) as src_val_p.
    destruct (error_or_not src_val_p) as [[msg Herr] | Hnoterr].
    rewrite Herr in H. inversion H. subst. left. repeat eexists.
    assert (forall {X} (a:string -> X) (b:X), match src_val_p with
             | VError msg => (a msg)
             | _ => b end = b) as A. {
      destruct src_val_p; simpl; congruence.
    }
    rewrite A in H.
    remember (S (S (S (S fuel)))) as fuel4.
    simpl3 H p0 Heqp0.
    rewrite Heqfuel4 in H.
    simpl3 H p0 Heqp0.
    remember (ev (fst s2, []) (S (S (S (S (S (S fuel))))))
             [VClo (VCode v2 :: VCode v1 :: env0)
                (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar 6)
                   (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar 7) (EApp (EVar n_env) (EVar 9))));
             VClo [src_val_p; VClo [Vlift; Vid] (ELam evl_body); Vlift; Vid] evl_body; src_val_p; VClo [Vlift; Vid] (ELam evl_body); Vlift; Vid] evl_body) as evi.
    destruct evi as [si' vi'].
    assert (S (S (S (S (S (S fuel))))) < nMax) as B by omega.
    assert (VClo [src_val_p; VClo [Vlift; Vid] (ELam evl_body); Vlift; Vid] evl_body = VClo [src_to_val (to_src names (x :: f :: env') p); Vevl; Vlift; Vid] evl_body) as C. {
      rewrite Heqsrc_val_p. simpl. reflexivity.
    }
    specialize (IHnMax (S (S (S (S (S (S fuel)))))) B p (fst s2, []) names (x :: f :: env') (v2 :: v1 :: env2) si' vi'
                       (VClo [src_val_p; VClo [Vlift; Vid] (ELam evl_body); Vlift; Vid] evl_body)
                       [(VClo (VCode v2 :: VCode v1 :: env0)
                (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar 6)
                     (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar 7) (EApp (EVar n_env) (EVar 9)))));
                        VClo [src_val_p; VClo [Vlift; Vid] (ELam evl_body); Vlift; Vid] evl_body;
                        (src_to_val (to_src names (x :: f :: env') p));Vevl;Vlift;Vid]
                       (VClo (VCode v2 :: VCode v1 :: env0)
                (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar 6)
                     (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar 7) (EApp (EVar n_env) (EVar 9)))))
               C).

    assert ([VClo (VCode v2 :: VCode v1 :: env0)
      (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar 6)
           (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar 7) (EApp (EVar n_env) (EVar 9))));
             VClo [src_val_p; VClo [Vlift; Vid] (ELam evl_body); Vlift; Vid] evl_body;
           src_to_val (to_src names (x :: f :: env') p); Vevl; Vlift; Vid] =
           [VClo (VCode v2 :: VCode v1 :: env0)
              (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar 6)
                 (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar 7) (EApp (EVar n_env) (EVar 9))));
            VClo [src_val_p; VClo [Vlift; Vid] (ELam evl_body); Vlift; Vid] evl_body; src_to_val (to_src names (x :: f :: env') p); Vevl; Vlift; Vid]) as D. {
      simpl. reflexivity.
    }

    specialize (IHnMax D).

    assert (forall (n : nat) (x0 : string) (s : state),
            index n (x :: f :: env') = Some x0 ->
            exists (fuel : nat) (v : val),
              ev s fuel
                [VClo (VCode v2 :: VCode v1 :: env0)
                   (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar 6)
                      (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar 7) (EApp (EVar n_env) (EVar 9))));
                VClo [src_val_p; VClo [Vlift; Vid] (ELam evl_body); Vlift; Vid] evl_body; src_to_val (to_src names (x :: f :: env') p); Vevl; Vlift; Vid]
                (EApp (EVar n_env) (EStr x0)) = (s, v) /\ (exists e : exp, v = VCode e)) as E. {
      intros.
      simpl in H0.
      case_eq ((n0 =? S (Datatypes.length env'))%nat); intros E.
      remember (string_dec x0 f) as b1;
      case_eq b1;
      remember (string_dec x0 x0) as b2;
      case_eq b2.

      rewrite E in H0. inversion H0. subst.
      exists 8. remember 7 as fuel07. exists (VCode v1). simpl.
      rewrite Heqfuel07. remember 6 as fuel06. simpl.
      rewrite Heqfuel06. remember 5 as fuel05. simpl.
      rewrite Heqfuel05.
      rewrite ev_var with (v:=VStr x0).
      split.
      simpl2g p0 Heqp0.
      rewrite H2.
      simpl. reflexivity. eexists. reflexivity.
      simpl. reflexivity.

      intros Ne. contradiction.

      intros.
      rewrite E in H0. inversion H0. subst.
      exists 8. remember 7 as fuel07. exists (VCode v2). simpl.
      rewrite Heqfuel07. remember 6 as fuel06. simpl.
      rewrite Heqfuel06. remember 5 as fuel05. simpl.
      rewrite Heqfuel05.
      rewrite ev_var with (v:=VStr x0).
      split.
      simpl2g p0 Heqp0.
      rewrite H2.
      simpl1g p0 Heqp0.
      rewrite H1.
      simpl. reflexivity. eexists. reflexivity.
      simpl. reflexivity.

      intros Neq. contradiction.

      rewrite E in H0.
      case_eq ((n0 =? Datatypes.length env')%nat); intros E2.

      remember (string_dec x0 x0) as b1;
      case_eq b1;
      remember (string_dec x0 x) as b2;
      case_eq b2.

      rewrite E2 in H0. inversion H0. subst.
      exists 8. remember 7 as fuel07. exists (VCode v1). simpl.
      rewrite Heqfuel07. remember 6 as fuel06. simpl.
      rewrite Heqfuel06. remember 5 as fuel05. simpl.
      rewrite Heqfuel05.
      rewrite ev_var with (v:=VStr x0).
      split.
      simpl2g p0 Heqp0.
      rewrite H2.
      simpl. reflexivity. eexists. reflexivity.
      simpl. reflexivity.

      intros.
      rewrite E2 in H0. inversion H0. subst.
      exists 8. remember 7 as fuel07. exists (VCode v1). simpl.
      rewrite Heqfuel07. remember 6 as fuel06. simpl.
      rewrite Heqfuel06. remember 5 as fuel05. simpl.
      rewrite Heqfuel05.
      rewrite ev_var with (v:=VStr x0).
      split.
      simpl2g p0 Heqp0.
      rewrite H2.
      simpl. reflexivity. eexists. reflexivity.
      simpl. reflexivity.

      intros. contradiction.
      intros. contradiction.

      rewrite E2 in H0.
      specialize (Henv1 n0 x0 s0 H0).
      destruct Henv1 as [fuel' [v' [Hev Hex]]].

      remember (string_dec x0 f) as b1;
      case_eq b1;
      remember (string_dec x0 x) as b2;
      case_eq b2.

      subst.
      exists 8. remember 7 as fuel07. exists (VCode v1). simpl.
      rewrite Heqfuel07. remember 6 as fuel06. simpl.
      rewrite Heqfuel06. remember 5 as fuel05. simpl.
      rewrite Heqfuel05.
      rewrite ev_var with (v:=VStr x0).
      split.
      simpl2g p0 Heqp0.
      rewrite H2.
      simpl. reflexivity. eexists. reflexivity.
      simpl. reflexivity.

      intros. subst.
      exists 8. remember 7 as fuel07. exists (VCode v1). simpl.
      rewrite Heqfuel07. remember 6 as fuel06. simpl.
      rewrite Heqfuel06. remember 5 as fuel05. simpl.
      rewrite Heqfuel05.
      rewrite ev_var with (v:=VStr f).
      split.
      simpl2g p0 Heqp0.
      rewrite H2.
      simpl. reflexivity. eexists. reflexivity.
      simpl. reflexivity.


      intros. subst.
      exists 8. remember 7 as fuel07. exists (VCode v2). simpl.
      rewrite Heqfuel07. remember 6 as fuel06. simpl.
      rewrite Heqfuel06. remember 5 as fuel05. simpl.
      rewrite Heqfuel05.
      rewrite ev_var with (v:=VStr x).
      split.
      simpl2g p0 Heqp0.
      rewrite H2.
      simpl1g p0 Heqp0.
      rewrite H1.
      simpl. reflexivity. eexists. reflexivity.
      simpl. reflexivity.

      intros.
      exists (S (S (S (S (S (S (S (S fuel')))))))).
      remember (S (S (S (S (S (S (S fuel'))))))) as fuel07.
      exists v'. simpl.
      rewrite Heqfuel07.
      remember (S (S (S (S (S (S fuel')))))) as fuel06. simpl.
      rewrite Heqfuel06.
      remember (S (S (S (S (S fuel'))))) as fuel05. simpl.
      rewrite Heqfuel05.
      rewrite ev_var with (v:=VStr x0).
      split.
      simpl2g p0 Heqp0.
      rewrite Heqenv0.
      Ltac simpl4g p0 Heqp0 :=
        match goal with
        | [ |- (let (s, v) := let (s, v) := let (s, v) := let (s, v) :=?e in ?body1 in ?body2 in ?body3 in ?body4) = ?r ] =>
          remember (e) as p0;
          simpl in Heqp0;
          rewrite Heqp0;
          clear Heqp0; clear p0
        end.
      simpl4g p0 Heqp0.
      subst. rewrite H2.
      simpl1g p0 Heqp0.
      subst. rewrite H1.
      remember (S (S (S (S fuel')))) as fuel14.
      simpl. rewrite Heqfuel14.
      rewrite ev_var with (v:=venv).
      rewrite ev_var with (v:=VStr x0).
      destruct Hex as [e'' Hex]. rewrite Hex in Hev.
      destruct fuel'.
      simpl in Hev. inversion Hev.
      simpl in Hev.
      destruct fuel'.
      simpl in Hev. inversion Hev.
      rewrite ev_var with (v:=venv) in Hev.
      rewrite ev_str in Hev.
      destruct venv; try solve [simpl in Hev; inversion Hev].
      eapply ev_fuel_monotonic. instantiate (1:=S fuel'). omega. rewrite Hex. eapply Hev.
      rewrite Hex. congruence.
      unfold n_env. simpl. reflexivity.
      simpl. reflexivity.
      unfold n_env. simpl. reflexivity.
      eapply Hex.
      simpl. rewrite Heqenv0. simpl. reflexivity.
    }
    assert (Datatypes.length (x :: f :: env') = Datatypes.length (v2 :: v1 :: env2)) as L1. {
      simpl. rewrite L. reflexivity.
    }
    specialize (IHnMax L1).
    assert ((forall (i j : nat) (xi xj : string),
                index i (names ++ x :: f :: env') = Some xi /\ index j (names ++ x :: f :: env') = Some xj /\ i <> j -> xi <> xj)) as Hd. {
      admit.
    }
    specialize (IHnMax Hd).
    specialize (IHnMax E).

    assert ((forall (n : nat) (x0 : string) (s : state) (e : exp),
            (index n (x :: f :: env') = Some x0 /\
            (exists fuel : nat,
               ev s fuel
                 [VClo (VCode v2 :: VCode v1 :: env0)
                    (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar 6)
                       (EIf (EOp2 OEq (EVar 9) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar 7) (EApp (EVar n_env) (EVar 9))));
                 VClo [src_val_p; VClo [Vlift; Vid] (ELam evl_body); Vlift; Vid] evl_body; src_to_val (to_src names (x :: f :: env') p); Vevl; Vlift; Vid]
                 (EApp (EVar n_env) (EStr x0)) = (s, VCode e))) -> index n (v2 :: v1 :: env2) = Some e)) as F. {
      intros.
      destruct H0 as [Hi [fuel' Hev]].
      simpl in Hi.
      simpl.
      case_eq ((n0 =? S (Datatypes.length env'))%nat); intros E0.
      rewrite E0 in Hi. inversion Hi. subst. rewrite <- L. rewrite E0.
      destruct fuel'.
      simpl in Hev. inversion Hev.
      simpl in Hev.
      destruct fuel'.
      simpl in Hev. inversion Hev.
      simpl in Hev.
      destruct fuel'.
      simpl in Hev. inversion Hev.
      simpl in Hev.
      destruct fuel'.
      simpl in Hev. inversion Hev.
      rewrite ev_var with (v:=VStr x0) in Hev.
      simpl in Hev.
      destruct fuel'.
      simpl in Hev. inversion Hev.
      simpl in Hev.
      destruct fuel'.
      simpl in Hev. inversion Hev.
      erewrite ev_var in Hev; try solve [unfold n_exp; simpl; reflexivity].
      simpl3 Hev p0 Heqp0.
      case_eq (string_dec x0 f). intros. subst. rewrite H0 in Hev.
      (specialize (Hd (length env') (S (length env')) f f)).
      simpl in Hd.
      (* something weird *)
      admit.
      admit.
      simpl. reflexivity.
      admit.
    }
    specialize (IHnMax F).
    rewrite Heqsrc_val_p in *.
    unfold Vevl in *.
    symmetry in Heqevi.
    specialize (IHnMax Heqevi).
    destruct IHnMax as [[msg Herr] | [e'' [Heq Hanf]]].
    simpl in H. rewrite Herr in H. inversion H. subst. left. repeat eexists.
    subst. simpl in H. inversion H. subst. right. eexists. split. reflexivity. simpl.
    rewrite <- Heqfs. rewrite <- Heqfs1. rewrite <- Hanf. reflexivity.
    unfold n_exp. simpl. reflexivity.
    unfold n_ev. rewrite Heqenv0. simpl. reflexivity.
    simpl. reflexivity.
    unfold n_l. rewrite Heqenv0. simpl. reflexivity.
    congruence. congruence. congruence. congruence. congruence.
    unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
    unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma correctness_of_interpretation_inner: forall n, forall fuel, fuel < n -> forall p s names env' r Venv_self,
     Venv_self = VClo [(src_to_val (to_src names env' p));Vev;Vid;Vid] evl_body ->
     ev s fuel [Vid;Venv_self;(src_to_val (to_src names env' p));Vev;Vid;Vid] evl_body = r ->
     (exists s' msg, r = (s', VError msg)) \/ r = ev s fuel (map VStr env') p.
Proof.
  intros nMax. induction nMax; intros fuel Hfuel.
  inversion Hfuel. unfold n_ev in *. simpl in *.
  intros p s names env' r Venv_self HeqVenv_self H.
  destruct fuel.
  simpl in H. left. subst. repeat eexists.
  simpl in H.
  destruct fuel.
  simpl in H. left. subst. repeat eexists.
  destruct fuel.
  simpl in H. left. subst. repeat eexists.
  destruct p.
  - simpl1 H p0 Heqp0.
    case_eq (index n0 env').
    intros s0 E. rewrite E in H.
    simpl in H. rewrite E in H.
    simpl in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    simpl2 H p0 Heqp0.
    simpl1 H p0 Heqp0.
    unfold Vid at 1 in H.
    simpl1 H p0 Heqp0.
    simpl in H.
    right. simpl. admit.
    intros E. rewrite E in H.
    simpl in H. inversion H. subst. left. repeat eexists.
  - admit.

  - remember (src_to_val (to_src names env' (ELam p))) as p_src_val.
    simpl in Heqp_src_val.
    remember [Vid; Venv_self; p_src_val; Vev; Vid; Vid] as env0.
    simpl1 H p0 Heqp0.
    assert (index n_exp env0 = Some p_src_val) as Hip. {
      unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
    }
    rewrite Hip in H. rewrite Heqp_src_val in H at 1.
    destruct names as [|f names].
    simpl in H. left. subst. repeat eexists.
    destruct names as [|x names].
    simpl in H. left. subst. repeat eexists.
    simpl in Heqp_src_val.
    simpl in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    simpl2 H p0 Heqp0.
    rewrite Hip in H. rewrite Heqp_src_val in H at 1.
    Arguments string_dec: simpl never.
    simpl1 H p0 Heqp0.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite ev_str with (t:="quote") in H.
    assert (forall fuel, ev s (S (S fuel)) env0 (EOp1 OCar (EVar n_exp)) = (s, VStr "lam")) as Hcar. {
      intros. simpl. rewrite Hip. rewrite Heqp_src_val. reflexivity.
    }
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite (Hcar fuel) in H.
    remember (if string_dec "quote" "lam" then 1 else 0) as b.
    vm_compute in Heqb. rewrite Heqb in H.
    assert (forall fuel op e1 e2, op <> "lam" ->
      ev s (S (S (S (S fuel)))) env0 (EIf (EOp2 OEq (EStr op) (EOp1 OCar (EVar n_exp))) e1 e2) = ev s (S (S (S fuel))) env0 e2) as Helse. {
      intros fuel0 op e1 e2  Hnotop.
      remember (S (S (S fuel0))) as fuel03.
      simpl.
      rewrite Heqfuel03.
      remember (S (S fuel0)) as fuel02.
      simpl.
      rewrite Heqfuel02.
      remember (S fuel0) as fuel01.
      rewrite ev_str with (t:=op).
      rewrite Heqfuel01.
      rewrite (Hcar fuel0).
      remember (string_dec op "lam") as cmp.
      case_eq cmp.
      intros. congruence. intros ? Hcmp.
      auto.
    }
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    remember (S (S fuel)) as fuel2.
    simpl in H.
    rewrite Heqfuel2 in H.
    rewrite ev_str in H.
    rewrite (Hcar fuel) in H.
    remember (if string_dec "lam" "lam" then 1 else 0) as yes.
    vm_compute in Heqyes. rewrite Heqyes in H.
    remember (S (S fuel)) as fuel2'.
    simpl in H.
    rewrite Heqfuel2' in H.
    rewrite ev_var with (v:=Vid) in H.
    unfold Vid in H at 1.
    simpl1 H p0 Heqp0.
    simpl in H.
    right. simpl.
    (* TODO: problem -- the closure has overhead *)
    admit.
    unfold n_l. rewrite Heqenv0. auto. congruence. congruence. congruence. congruence. congruence.

  - admit.
  - remember (src_to_val (to_src names env' (ELift p))) as p_src_val.
    simpl in Heqp_src_val.
    remember [Vid; Venv_self; p_src_val; Vev; Vid; Vid] as env0.
    simpl1 H p0 Heqp0.
    assert (index n_exp env0 = Some p_src_val) as Hip. {
      unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
    }
    rewrite Hip in H. rewrite Heqp_src_val in H at 1.
    simpl in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite ev_var with (n:=n_exp) (v:=p_src_val) in H.
    rewrite Heqp_src_val in H at 1.
    simpl1 H p0 Heqp0.
    Arguments string_dec: simpl never.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite ev_str with (t:="quote") in H.
    assert (forall fuel, ev s (S (S fuel)) env0 (EOp1 OCar (EVar n_exp)) = (s, VStr "lift")) as Hcar. {
      intros. simpl. rewrite Hip. rewrite Heqp_src_val. reflexivity.
    }
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite (Hcar fuel) in H.
    remember (if string_dec "quote" "lift" then 1 else 0) as b.
    vm_compute in Heqb. rewrite Heqb in H.
    assert (forall fuel op e1 e2, op <> "lift" ->
      ev s (S (S (S (S fuel)))) env0 (EIf (EOp2 OEq (EStr op) (EOp1 OCar (EVar n_exp))) e1 e2) = ev s (S (S (S fuel))) env0 e2) as Helse. {
      intros fuel0 op e1 e2  Hnotop.
      remember (S (S (S fuel0))) as fuel03.
      simpl.
      rewrite Heqfuel03.
      remember (S (S fuel0)) as fuel02.
      simpl.
      rewrite Heqfuel02.
      remember (S fuel0) as fuel01.
      rewrite ev_str with (t:=op).
      rewrite Heqfuel01.
      rewrite (Hcar fuel0).
      remember (string_dec op "lift") as cmp.
      case_eq cmp.
      intros. congruence. intros ? Hcmp.
      auto.
    }
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    remember (S (S fuel)) as fuel2.
    simpl in H.
    rewrite Heqfuel2 in H.
    remember (S fuel) as fuel1.
    simpl1 H p0 Heqp0.
    rewrite Heqfuel1 in H.
    rewrite ev_str in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite (Hcar fuel) in H.
    remember (if string_dec "lift" "lift" then 1 else 0) as yes.
    vm_compute in Heqyes. rewrite Heqyes in H.
    remember (S (S fuel)) as fuel2'.
    simpl in H.
    rewrite Heqfuel2' in H.
    remember (src_to_val (to_src names env' p)) as p1_src_val.
    assert (forall fuel, ev s (S (S (S fuel))) env0 (EOp1 OCar (EOp1 OCdr (EVar n_exp))) = (s, p1_src_val)) as A. {
      intros. simpl.
      rewrite Hip. rewrite Heqp_src_val at 1. reflexivity.
    }


    assert (forall fuel0,
               ev s (S (S (S (S (S fuel0))))) env0 (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)) =
               ev s (S (S (S (S fuel0)))) [Vid; VClo [p1_src_val; VClo [VClo [] (EVar 1); VClo [] (EVar 1)] (ELam evl_body); VClo [] (EVar 1); VClo [] (EVar 1)] evl_body; p1_src_val; Vev; Vid; Vid] evl_body) as HI. {

      Ltac simplh1 p0 Heqp0 :=
        match goal with
        | [ |- (let (s, v) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1) = ?r ] =>
          remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0;
          clear Heqp0; clear p0
        end.
      Ltac simplh2 p0 Heqp0 :=
        match goal with
        | [ |- (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = ?r ] =>
          remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0;
          clear Heqp0; clear p0
        end.
      Ltac simplh3 p0 Heqp0 :=
        match goal with
        | [ |- (let (s, v) := let (s2, v2) := let (s3,v3) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2 in ?body3) = ?r ] =>
          remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0;
          clear Heqp0; clear p0
        end.

      intros.
      remember (S (S (S (S fuel0)))) as fuel0'.
      simpl.
      rewrite Heqfuel0' in *. clear Heqfuel0'. clear fuel0'.

      remember (S (S (S fuel0))) as fuel0'.
      simplh1 p0 Heqp0.
      rewrite Heqfuel0' in *. clear Heqfuel0'. clear fuel0'.

      rewrite ev_var with (v:=Vev). unfold Vev.

      rewrite (A fuel0).

      destruct (error_or_not p1_src_val) as [[? Herr1] | Hnop1].
      rewrite Herr1. simpl. reflexivity.
      assert (forall b,
                 match p1_src_val with
                 | VError msg => (s, VError msg)
                 | _ => b
                 end = b) as B. {
        destruct p1_src_val; congruence.
      }
      rewrite B.

      remember (S (S fuel0)) as fuel0'.
      simplh1 p0 Heqp0.
      rewrite Heqfuel0' in *. clear Heqfuel0'. clear fuel0'.

      rewrite ev_var with (v:=Vid). unfold Vid.
      reflexivity.
      rewrite Heqenv0. unfold n_env. simpl. reflexivity.
      rewrite Heqenv0. unfold n_env. simpl. reflexivity.
    }

    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    destruct fuel.
    change 3 with (S 2) in H. remember 2 as fuele.
    simpl1 H p0 Heqp0.
    rewrite Heqfuele in *. clear Heqfuele. clear fuele.
    change 2 with (S 1) in H. remember 1 as fuele.
    simpl2 H p0 Heqp0.
    rewrite Heqfuele in *. clear Heqfuele. clear fuele.
    rewrite ev_var with (v:=Vev) in H. unfold Vev in H at 1.
    change 1 with (S 0) in H.
    simpl3 H p0 Heqp0. left. subst. repeat eexists.
    rewrite Heqenv0. unfold n_ev. simpl. reflexivity.
    destruct fuel.
    change 4 with (S 3) in H. remember 3 as fuele.
    simpl1 H p0 Heqp0.
    rewrite Heqfuele in *. clear Heqfuele. clear fuele.
    change 3 with (S 2) in H. remember 2 as fuele.
    simpl2 H p0 Heqp0.
    rewrite Heqfuele in *. clear Heqfuele. clear fuele.
    rewrite ev_var with (v:=Vev) in H. unfold Vev in H at 1.
    change 1 with (S 0) in H.
    simpl3 H p0 Heqp0. left. subst. repeat eexists.
    rewrite Heqenv0. unfold n_ev. simpl. reflexivity.

    rewrite HI in H.
    remember (ev s (S (S (S (S fuel))))
           [Vid; VClo [p1_src_val; VClo [VClo [] (EVar 1); VClo [] (EVar 1)] (ELam evl_body); VClo [] (EVar 1); VClo [] (EVar 1)] evl_body; p1_src_val;
            Vev; Vid; Vid] evl_body) as r1.
    remember (S (S (S (S (S (S (S (S (S (S fuel2)))))))))) as fuelS.
    simpl.
    symmetry in Heqr1.
    edestruct IHnMax with (fuel:=S (S (S (S fuel)))) (p:=p). omega. reflexivity. repeat rewrite Heqp1_src_val in Heqr1. unfold Vev in Heqr1. unfold Vev.
    unfold Vid in *. apply Heqr1.
    destruct H0 as [? [? Herr]].
    rewrite Herr in H. simpl in H. left. subst. repeat eexists.
    rewrite HeqfuelS. rewrite Heqfuel2. rewrite Heqfuel1. rewrite Heqfuel2'.
    destruct r1 as [s1 v1].
    rewrite ev_fuel_monotonic with (v:=v1) (s':=s1) (fuel:=(S (S (S (S fuel))))).
    destruct (error_or_not v1) as [[? Herr1] | Hnop1].
    left. subst. repeat eexists.
    assert (forall b (s: state),
               match v1 with
               | VError msg => (s, VError msg)
               | _ => b
               end = b) as B. {
      destruct v1; congruence.
    }
    rewrite B. rewrite B in H.
    remember (lift s1 (S (S (S (S (S fuel))))) v1) as r2.
    destruct r2 as [s2 e2].
    rewrite lift_fuel_monotonic with (e:=e2) (s':=s2) (fuel:=(S (S (S (S (S fuel)))))).
    destruct e2; try auto.
    omega. auto. admit. omega. auto. admit.
    congruence. congruence. congruence. congruence. congruence. congruence. congruence. congruence.
  - remember (src_to_val (to_src names env' (ERun p1 p2))) as p_src_val.
    simpl in Heqp_src_val.
    simpl1 H p0 Heqp0.
    remember [Vid; Venv_self; p_src_val; Vev; Vid; Vid] as env0.
    assert (index n_exp env0 = Some p_src_val) as Hip. {
      unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
    }
    rewrite Heqp_src_val in H at 1.
    simpl in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite ev_var with (n:=n_exp) (v:=p_src_val) in H.
    rewrite Heqp_src_val in H at 1.
    simpl1 H p0 Heqp0.
    Arguments string_dec: simpl never.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite ev_str with (t:="quote") in H.
    assert (forall fuel, ev s (S (S fuel)) env0 (EOp1 OCar (EVar n_exp)) = (s, VStr "run")) as Hcar. {
      intros. simpl. rewrite Hip. rewrite Heqp_src_val. reflexivity.
    }
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite (Hcar fuel) in H.
    remember (if string_dec "quote" "run" then 1 else 0) as b.
    vm_compute in Heqb. rewrite Heqb in H.
    assert (forall fuel op e1 e2, op <> "run" ->
      ev s (S (S (S (S fuel)))) env0 (EIf (EOp2 OEq (EStr op) (EOp1 OCar (EVar n_exp))) e1 e2) = ev s (S (S (S fuel))) env0 e2) as Helse. {
      intros fuel0 op e1 e2  Hnotop.
      remember (S (S (S fuel0))) as fuel03.
      simpl.
      rewrite Heqfuel03.
      remember (S (S fuel0)) as fuel02.
      simpl.
      rewrite Heqfuel02.
      remember (S fuel0) as fuel01.
      rewrite ev_str with (t:=op).
      rewrite Heqfuel01.
      rewrite (Hcar fuel0).
      remember (string_dec op "run") as cmp.
      case_eq cmp.
      intros. congruence. intros ? Hcmp.
      auto.
    }
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite Helse in H.
    simpl in H. left. subst. repeat eexists.
    congruence. congruence. congruence. congruence. congruence. congruence. congruence. congruence. congruence. congruence. congruence. congruence.
    congruence. congruence. congruence.
  - simpl in H. subst. right. simpl. reflexivity.
  - cbv [to_src] in H. cbv [src_to_val] in H.
    simpl in H.
    destruct fuel as [|fuel].
    simpl in H. left. subst. repeat eexists.
    rewrite ev_var with (n:=n_exp) (v:=VPair (VStr "quote") (VPair (VStr t) (VStr "."))) in H.
    simpl1 H p0 Heqp0.
    simpl in H.
    destruct fuel as [|fuel].
    simpl in H. left. subst. repeat eexists.
    Arguments string_dec: simpl never.
    rewrite ev_str with (t:="quote") in H.
    destruct fuel as [|fuel].
    simpl in H. left. subst. repeat eexists.
    rewrite exp_apart_car in H.
    remember (if string_dec "quote" "quote" then 1 else 0) as b.
    vm_compute in Heqb. rewrite Heqb in H.
    simpl1 H p0 Heqp0.
    unfold Vid in H.
    simpl. simpl in H.
    destruct fuel as [|fuel].
    simpl in H. left. subst. repeat eexists.
    simpl in H. subst. right. reflexivity.
    simpl. reflexivity.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
