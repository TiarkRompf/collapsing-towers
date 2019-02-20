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
  case_eq (n =? Datatypes.length env1); intros E.
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
  case_eq (n =? Datatypes.length env1); intros E.
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

Lemma ev_to_src: forall n, forall fuel, fuel < n -> forall p s env names env' r,
    ev s fuel env (to_src names env' p) = r ->
    (exists msg, (s, VError msg) = r) \/ ((s, src_to_val (to_src names env' p)) = r).
Proof.
  intros nMax. induction nMax; intros fuel Hfuel.
  inversion Hfuel.
  destruct fuel as [| fuel].
  simpl. intros. left. subst. repeat eexists.
  intros.
  destruct p.
  - simpl. subst. simpl.
    case_eq (index n0 env').
    intros t E. simpl. right. reflexivity.
    intros E. simpl. left. repeat eexists.
  - simpl.
    cbv [to_src] in H. fold to_src in H.
    simpl in H.
    destruct fuel as [| fuel].
    simpl in H. left. repeat eexists. eapply H.
    edestruct IHnMax with (fuel:=fuel) (p:=p1) (s:=s) (env:=env) (names:=names) (env':=env'). omega. auto.
    destruct H0 as [? Herr1]. symmetry in Herr1.
    eapply econs_ind1err in Herr1.
    remember (ev s (S fuel) env (EStr "app")) as rapp.
    simpl in Heqrapp. rewrite Heqrapp in H.
    rewrite Herr1 in H.
    left. eexists. eapply H.
    simpl in H.
    destruct fuel as [| fuel].
    simpl in H. left. eexists. eapply H.
    edestruct IHnMax with (fuel:=fuel) (p:=p2) (s:=s) (env:=env) (names:=names) (env':=env'). omega. auto.
    destruct H1 as [? Herr2]. symmetry in Herr2.
    eapply econs_ind1err in Herr2.
    rewrite <- H0 in H.
    rewrite Herr2 in H.
    remember (src_to_val (to_src names env' p1)) as v1.
    destruct v1; try solve [left; eexists; eapply H].
    rewrite <- H0 in H. simpl in H.
    rewrite <- H1 in H. simpl in H.
    remember (src_to_val (to_src names env' p1)) as v1.
    remember (src_to_val (to_src names env' p2)) as v2.
    destruct fuel as [| fuel].
    simpl in H.
    destruct v1; try solve [left; eexists; eapply H];
      destruct v2; try solve [left; eexists; eapply H].
    simpl in H.
    destruct v1; try solve [left; eexists; eapply H];
      destruct v2; try solve [left; eexists; eapply H];
        try solve [right; subst; reflexivity].
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
  - admit.
Admitted.

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
Definition Vev := VClo [Vid;Vid] (ELam evl_body).

Eval vm_compute in ev (0,[]) 100 [Vid;Vid;(src_to_val (to_src0 (EOp2 OPlus (ENat 1) (ENat 1))));Vev;Vid;Vid] evl_body.

Ltac simpl1 H r p0 Heqp0 :=
  match goal with
  | [ H : (let (s, v) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1) = r |- _ ] =>
    remember (ev s1 (S fuel1) env1 e1) as p0;
    simpl in Heqp0;
    rewrite Heqp0 in H;
    clear Heqp0; clear p0
  end.
Ltac simpl2 H r p0 Heqp0 :=
  match goal with
  | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
    remember (ev s1 (S fuel1) env1 e1) as p0;
    simpl in Heqp0;
    rewrite Heqp0 in H;
    clear Heqp0; clear p0
  end.
Ltac simpl3 H r p0 Heqp0 :=
  match goal with
  | [ H : (let (s, v) := let (s2, v2) := let (s3,v3) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2 in ?body3) = r |- _ ] =>
    remember (ev s1 (S fuel1) env1 e1) as p0;
    simpl in Heqp0;
    rewrite Heqp0 in H;
    clear Heqp0; clear p0
  end.

Lemma exp_apart_car: forall s fuel a d,
    ev s (S (S fuel)) [Vid; Vid; VPair a d; Vev; Vid; Vid] (EOp1 OCar (EVar n_exp)) = (s, a).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma exp_apart_cdr: forall s fuel a d,
    ev s (S (S fuel)) [Vid; Vid; VPair a d; Vev; Vid; Vid] (EOp1 OCdr (EVar n_exp)) = (s, d).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma ev_fuel_mono: forall fuel s env e s' v,
        ev s fuel env e = (s', v) ->
        (forall msg, v <> VError msg) ->
        ev s (S fuel) env e = (s', v).
Proof.
  intros fuel. induction fuel; intros s env e s' v Hev Hnoerr.
  simpl in Hev. congruence.
  destruct e.
  - simpl in Hev.
    case_eq (index n0 env).
    intros v0 E. simpl. rewrite E in *. inversion Hev. subst. reflexivity.
    intros E. simpl. rewrite E in *. inversion Hev. congruence.
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
  - admit.
  - admit.
Admitted.

Lemma ev_fuel_monotonic: forall fuel fuel' s env e s' v,
        fuel' > fuel ->
        ev s fuel env e = (s', v) ->
        (forall msg, v <> VError msg) ->
        ev s fuel' env e = (s', v).
Proof.
  admit.
Admitted.

Lemma lift_monotonic: forall fuel fuel' s e s' v,
        fuel' > fuel ->
        lift s fuel v = (s', e) ->
        (forall msg, v <> VError msg) ->
        lift s fuel' v = (s', e).
Proof.
  admit.
Admitted.

Lemma correctness_of_interpretation_inner: forall n, forall fuel, fuel < n -> forall p s names r Venv_self,
     Venv_self = VClo [(src_to_val (to_src names [] p));Vev;Vid;Vid] evl_body ->
     ev s fuel [Vid;Venv_self;(src_to_val (to_src names [] p));Vev;Vid;Vid] evl_body = r ->
     (exists s' msg, r = (s', VError msg)) \/ r = ev s fuel [] p.
Proof.
  intros nMax. induction nMax; intros fuel Hfuel.
  inversion Hfuel. unfold n_ev in *. simpl in *.
  intros p s names r Venv_self HeqVenv_self H.
  destruct fuel.
  simpl in H. left. subst. repeat eexists.
  simpl in H.
  destruct fuel.
  simpl in H. left. subst. repeat eexists.
  destruct fuel.
  simpl in H. left. subst. repeat eexists.
  destruct p.
  - simpl in H. left. subst. repeat eexists.
  - admit.
  - admit.
  - admit.
  - remember (src_to_val (to_src names [] (ELift p))) as p_src_val.
    simpl in Heqp_src_val.
    remember [Vid; Venv_self; p_src_val; Vev; Vid; Vid] as env0.
    simpl1 H r p0 Heqp0.
    assert (index n_exp env0 = Some p_src_val) as Hip. {
      unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
    }
    rewrite Hip in H. rewrite Heqp_src_val in H at 1.
    simpl in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite ev_var with (n:=n_exp) (v:=p_src_val) in H.
    rewrite Heqp_src_val in H at 1.
    simpl1 H r p0 Heqp0.
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
    simpl1 H r p0 Heqp0.
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
    remember (src_to_val (to_src names [] p)) as p1_src_val.
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
    admit.
    destruct fuel.
    admit.

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
    rewrite lift_monotonic with (e:=e2) (s':=s2) (fuel:=(S (S (S (S (S fuel)))))).
    destruct e2; try auto.
    omega. auto. auto. omega. auto. admit.
    congruence. congruence. congruence. congruence. congruence. congruence. congruence. congruence.
  - remember (src_to_val (to_src names [] (ERun p1 p2))) as p_src_val.
    simpl in Heqp_src_val.
    remember [Vid; Vid; p_src_val; Vev; Vid; Vid] as env0.
    simpl1 H r p0 Heqp0.
    assert (index n_exp env0 = Some p_src_val) as Hip. {
      unfold n_exp. rewrite Heqenv0. simpl. reflexivity.
    }
    rewrite Hip in H. rewrite Heqp_src_val in H at 1.
    simpl in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    rewrite ev_var with (n:=n_exp) (v:=p_src_val) in H.
    rewrite Heqp_src_val in H at 1.
    simpl1 H r p0 Heqp0.
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
    simpl1 H r p0 Heqp0.
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
    simpl1 H r p0 Heqp0.
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

(*    
Lemma correctness_of_interpretation_inner: forall n, forall fuel, fuel < n ->
   forall p s names r,
     ev s fuel [(src_to_val (to_src names [] p));Vev;Vid;Vid] (EApp (EApp (EVar n_ev) (EVar (n_ev+1))) (ELam (EVar 1))) = r ->
     (exists s' msg, r = (s', VError msg)) \/ r = ev s fuel [] p.
Proof.
  intros nMax. induction nMax; intros fuel Hfuel.
  inversion Hfuel. unfold n_ev in *. simpl in *.
  intros.
  destruct fuel.
  simpl in H. left. subst. repeat eexists.
  simpl in H.
  destruct fuel.
  simpl in H. left. subst. repeat eexists.
  destruct p.
  - simpl in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    simpl in H. left. subst. repeat eexists.
  - simpl in H.
    admit.
  - simpl in H.
    admit.
  - simpl in H.
    admit.
  - simpl in H.
    admit.
  - simpl in H.
    admit.
  - simpl in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    simpl in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    simpl in H. right. simpl. subst. reflexivity.
  - admit.
  - admit.
  - admit.
  - (*
    simpl in H.
    destruct fuel as [|fuel].
    simpl in H. left. subst. repeat eexists.
    rewrite ev_var with (n:=2) (v:=Vev) in H.
    unfold Vev in H. fold Vev in H.
    rewrite ev_var with (n:=3) (v:=src_to_val (to_src names [] (EOp1 op p))) in H.
    cbv [to_src] in H. fold to_src in H. cbv [src_to_val] in H.
    match goal with
      | [ H : (let (s, v) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    unfold evl_body in H.
    match goal with
      | [ H : (let (s, v) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel as [|fuel].
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    fold evl_body in H.
    simpl in H.
    destruct fuel as [|fuel].
    simpl in H. left. subst. repeat eexists.
    Arguments string_dec: simpl never.
    unfold n_exp in H.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    match goal with
      | [ H : (let (s, v) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := let (s3,v3) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2 in ?body3) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct op.
    remember (if string_dec "quote" "car" then 1 else 0) as bquote.
    vm_compute in Heqbquote. rewrite Heqbquote in H.
    remember (S (S fuel)) as fuel2.
    simpl in H.
    rewrite Heqfuel2 in H. remember (S fuel) as fuel1.
    simpl in H. rewrite Heqfuel1 in H.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := let (s3,v3) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2 in ?body3) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    remember (if string_dec "plus" "car" then 1 else 0) as bplus.
    vm_compute in Heqbplus. rewrite Heqbplus in H.
    match goal with
      | [ H : (let (s, v) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := let (s3,v3) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2 in ?body3) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    remember (if string_dec "minus" "car" then 1 else 0) as b0.
    vm_compute in Heqb0. rewrite Heqb0 in H.
    remember (S (S fuel)) as fuel2'.
    simpl in H. rewrite Heqfuel2' in H. remember (S fuel) as fuel1'.
    match goal with
      | [ H : (let (s, v) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    rewrite Heqfuel1' in H.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := let (s3,v3) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2 in ?body3) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    simpl. reflexivity.
     *)
    admit.
  - simpl in H.
    destruct fuel as [|fuel].
    simpl in H. left. subst. repeat eexists.
    rewrite ev_var with (n:=2) (v:=Vev) in H.
    unfold Vev in H. fold Vev in H.
    rewrite ev_var with (n:=3) (v:=src_to_val (to_src names [] (EOp2 op p1 p2))) in H.
    cbv [to_src] in H. fold to_src in H. cbv [src_to_val] in H.
    match goal with
      | [ H : (let (s, v) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    unfold evl_body in H.
    match goal with
      | [ H : (let (s, v) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel as [|fuel].
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    fold evl_body in H.
    simpl in H.
    destruct fuel as [|fuel].
    simpl in H. left. subst. repeat eexists.
    Arguments string_dec: simpl never.
    unfold n_exp in H.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    match goal with
      | [ H : (let (s, v) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := let (s3,v3) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2 in ?body3) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct op.
    admit.
    remember (if string_dec "quote" "plus" then 1 else 0) as bquote.
    vm_compute in Heqbquote. rewrite Heqbquote in H.
    remember (S (S fuel)) as fuel2.
    simpl in H.
    rewrite Heqfuel2 in H. remember (S fuel) as fuel1.
    simpl in H. rewrite Heqfuel1 in H.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := let (s3,v3) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2 in ?body3) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    remember (if string_dec "plus" "plus" then 1 else 0) as bplus.
    vm_compute in Heqbplus. rewrite Heqbplus in H.
    remember (S fuel) as fuel1'.
    match goal with
      | [ H : (let (s, v) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    rewrite Heqfuel1' in H.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := let (s3,v3) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2 in ?body3) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    unfold Vev in H.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := let (s3,v3) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2 in ?body3) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := let (s3,v3) := let (s4,v4) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2 in ?body3 in ?body4) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    match goal with
      | [ H : (let (s, v) := let (s2, v2) := let (s3,v3) := let (s4,v4) := let (s5,v5) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1 in ?body2 in ?body3 in ?body4 in ?body5) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.
    fold src_to_val in H.
    remember (src_to_val (to_src names [] p1)) as p1_src_val.
    edestruct (error_or_not p1_src_val) as [[? Herr] | Hno].
    rewrite Herr in H.
    match goal with
      | [ H : (let (s, v) := ev ?s1 (S ?fuel1) ?env1 ?e1 in ?body1) = r |- _ ] =>
        remember (ev s1 (S fuel1) env1 e1) as p0;
          simpl in Heqp0;
          rewrite Heqp0 in H;
          clear Heqp0; clear p0
    end.

    remember (S (S fuel)) as fuelx.

    simpl in H. left. repeat eexists. symmetry. eapply H.
    
  - simpl. simpl in H.
    destruct fuel.
    simpl in H. left. subst. repeat eexists.
    simpl in H. left. subst. repeat eexists.
Admitted.

(*
 Lemma correctness_of_interpretation_loop: forall n, forall fuel, fuel < n ->
   forall p s names r,
     ev s fuel [VClo [VClo [] (EVar 1);VNat 0] (ELam (ELam evl_body));VClo [] (EVar 1);VNat 0] (EApp (EVar n_ev) (to_src names [] p)) = r ->
     (exists s' msg, r = (s', VError msg)) \/ r = ev s fuel [] p.
Proof.
  intros nMax. induction nMax; intros fuel Hfuel.
  inversion Hfuel.
  intros.
  destruct fuel.
  simpl. left. simpl in H; subst. repeat eexists.
  destruct p.
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
  - cbv [to_src] in H. fold to_src in H. cbv [ev] in H. fold ev in H.
    destruct fuel as [|fuel].
    simpl in H. left. repeat eexists. subst. reflexivity.
    simpl in H.
    destruct fuel as [| fuel].
    simpl in H. left. repeat eexists. subst. reflexivity.
    simpl in H.
    edestruct ev_to_src with (p:=p) (fuel:=fuel) (n:=S fuel). omega. auto.
    destruct H0 as [? Herr1].
    rewrite <- Herr1 in H. left. repeat eexists. subst. reflexivity.
    rewrite <- H0 in H.
    remember (src_to_val (to_src names [] p)) as v1.
    destruct fuel as [| fuel].
    simpl in H. destruct v1;
                  try solve [left; repeat eexists; subst; reflexivity].
    simpl in H.
    remember (S (S (S fuel))) as fuel3. simpl.
    edestruct IHnMax with (p:=p) (fuel:=fuel3). omega. auto.
    destruct H1 as [? [? Herr]].
    simpl in H.
    rewrite Herr in H0.
    simpl in H.
    destruct v1;
      try solve [left; repeat eexists; subst; reflexivity].
    destruct op.

    
    
    edestruct ev_to_src with (p:=p2) (fuel:=fuel) (n:=S fuel). omega. auto.
    remember (ev s (S fuel) [VClo [VClo [] (EVar 1); VNat 0] (ELam (ELam evl_body)); VClo [] (EVar 1); VNat 0] (EVar n_ev)) as A.
    simpl in HeqA. rewrite HeqA in H.
    remember (ev s (S fuel) [VClo [VClo [] (EVar 1); VNat 0] (ELam (ELam evl_body)); VClo [] (EVar 1); VNat 0] (ECons (op1_to_src op) (ECons (to_src names [] p) (EStr ".")))) as B.
    simpl in HeqB.
    destruct fuel as [|fuel].
    admit.
    simpl in HeqB.
    destruct fuel as [|fuel].
    admit.
    simpl in HeqB. fold ev in HeqB.
Lemma correctness_of_interpretation_rec: forall n, forall fuel, fuel < n ->
   forall p s names r,
     ev s fuel [] (EApp (EApp (EApp evl (ELam (EVar 1))) (to_src names [] p)) (ELam (EVar 1))) = r ->
     (exists s' msg, r = (s', VError msg)) \/ r = ev s fuel [] p.
Proof.
  intros nMax. induction nMax; intros fuel Hfuel.
  inversion Hfuel.
  intros.
  destruct fuel.
  simpl. left. simpl in H; subst. repeat eexists.
  destruct p.
  - admit. (*
    simpl. simpl in H.
    case_eq (index n0 env_to); [intros ri Hi|].
    case_eq (index n0 env); [intros vi Hiv|].
    right.
    rewrite Hi.
    admit. *)
  - eapply inv_app in H.
    destruct H as [Herr | [Hev | Hec]].
    left. apply Herr.
    destruct Hev as [? [? [? [? [? [Hev1 [Hev2 Hev3]]]]]]].
    simpl in Hev1. destruct fuel as [| fuel].
    simpl in Hev1. inversion Hev1.
    eapply inv_app in Hev1.
    destruct Hev1 as [Herr | [Hev1 | Hec1]].
    destruct Herr as [? [? Herr]]. inversion Herr.
    destruct Hev1 as [? [? [? [? [? [Hev1 [Hev12 Hev13]]]]]]].
    admit.
    admit.
    admit.
  - simpl. admit.
  - simpl. admit.
  - simpl. admit.
  - simpl. admit.
  - simpl.
    eapply inv_app in H.
    destruct H as [Herr | [Hev | Hec]].
    left. apply Herr.
    destruct Hev as [? [? [? [? [? [Hev1 [Hev2 Hev3]]]]]]].
    destruct fuel as [|fuel].
    simpl in Hev1. inversion Hev1.
    simpl in Hev1.
    remember (ev s fuel [] (EApp evl (ELam (EVar 1)))) as rx1.
    destruct fuel as [|fuel].
    simpl in Heqrx1. rewrite Heqrx1 in Hev1. inversion Hev1.
    symmetry in Heqrx1. unfold evl in Heqrx1. eapply inv_app_lam in Heqrx1.
    destruct Heqrx1 as [[? [? Heqrx1]] | [? [? [? [Heqrx1b Heqrx1]]]]].
    rewrite Heqrx1 in Hev1. inversion Hev1.
    rewrite <- Heqrx1 in Hev1. destruct fuel as [| fuel].
    simpl in Hev1. inversion Hev1. simpl in Hev1.
    inversion Hev1. rewrite <- H2 in Hev3.
    eapply inv_if_true in Hev3.
    simpl in Heqrx1b. inversion Heqrx1b. subst. simpl.
    simpl in Hev3. right. repeat eexists.
    simpl in Hev2. inversion Hev2. subst. simpl in Hev3.
    simpl in Hev1. inversion Hev1. subst. rewrite <- Hev3. reflexivity.
    simpl. subst. simpl. simpl in Hev2. inversion Hev2. subst. simpl in Heqrx1b. inversion Heqrx1b. reflexivity.
    destruct Hec as [? [? [? [? [Hc1 [Hcl Hc2]]]]]].
    destruct fuel as [| fuel].
    simpl in Hcl. inversion Hcl.
    simpl in Hcl. inversion Hcl.
  - simpl. admit.
  - simpl. admit.
  - cbv [to_src] in H. fold to_src in H. eapply inv_app in H.
    destruct H as [Herr | [Hev | Hec]].
    left. apply Herr.
    destruct Hev as [? [? [? [? [? [Hev1 [Hev2 Hev3]]]]]]].
    destruct fuel as [| fuel].
    simpl in Hev1. inversion Hev1.
    eapply inv_app in Hev1.
    destruct Hev1 as [Herr | [Hev1 | Hec1]].
    destruct Herr as [? [? Herr]]. inversion Herr.
    destruct Hev1 as [? [? [? [? [? [Hev1 [Hev12 Hev13]]]]]]].
    simpl in Hev12.
    destruct fuel as [| fuel].
    simpl in Hev1. inversion Hev1.
    eapply inv_app_lam in Hev1. simpl in Hev1. destruct Hev1 as [Herr | Hev1].
    destruct Herr as [? [? Herr]]. inversion Herr.
    destruct Hev1 as [v2 [s2 [v1 [Hevv2 Hev1]]]].
    simpl in Hev12.
    remember (ev x4 fuel [] (op1_to_src op)) as rop.
    destruct fuel as [| fuel].
    simpl in Hev1. inversion Hev1. subst.
    simpl in Hev1. inversion Hev1. subst.
    simpl in Hev13. inversion Hev13. subst.
    clear Hev1. clear Hev13.
    simpl in Hevv2. inversion Hevv2. subst. clear Hevv2.
    simpl in Hev12.
    remember (ev x4 fuel [] (to_src names [] p)) as rp.
    edestruct IHnMax with (fuel:=fuel) (p:=p). omega.
    simpl in Hev2. inversion Hev2. subst.
    simpl in Heqrop. rewrite Heqrop in Hev12.
    remember (ev x4 (S fuel) [] (ECons (to_src names [] p) (EStr "."))) as rcp.
    simpl in Heqrcp.
    destruct fuel as [| fuel].


  - simpl. admit.
  - admit. (*simpl. right. reflexivity.*)
Admitted.
*)
*)