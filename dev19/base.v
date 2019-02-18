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
| OCons
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
      | (VCode e1, VCode e2) => reflect s (EOp2 OCons e1 e2)
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
          | (OCons, v1, v2) => (s, VPair v1 v2)
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

Definition evl :=
(ELam (ELam (ELam
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
   (EIf (EOp2 OEq (EStr "cons")  (EOp1 OCar (EVar n_exp))) (EApp (EVar n_l) (EOp2 OCons  (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar n_env))))
   (EIf (EOp2 OEq (EStr "car")   (EOp1 OCar (EVar n_exp))) (EOp1 OCar (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)))
   (EIf (EOp2 OEq (EStr "cdr")   (EOp1 OCar (EVar n_exp))) (EOp1 OCdr (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)))
   (EIf (EOp2 OEq (EStr "app")   (EOp1 OCar (EVar n_exp))) (EApp (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EVar n_exp)))) (EVar n_env)) (EApp (EApp (EVar n_ev) (EOp1 OCar (EOp1 OCdr (EOp1 OCdr (EVar n_exp))))) (EVar n_env)))
   (EStr "error")
)))))))))))))))))))).

Eval vm_compute in (ev0 (EApp (EApp (EApp evl (ELam (EVar 1))) (ENat 5)) (ELam (EError "unbound")))).
Eval vm_compute in (ev0 (EApp (EApp (EApp evl (ELam (EVar 1))) (EOp2 OCons (EStr "cons") (EOp2 OCons (ENat 5) (EOp2 OCons (ENat 6) (EStr "."))))) (ELam (EError "unbound")))).
Eval vm_compute in (ev0 (EApp (EApp (EApp evl (ELam (EVar 1))) (EOp2 OCons (EStr "app") (EOp2 OCons (EOp2 OCons (EStr "lam") (EOp2 OCons (EStr "_") (EOp2 OCons (EStr "x") (EOp2 OCons (EOp2 OCons (EStr "plus") (EOp2 OCons (EStr "x") (EOp2 OCons (ENat 1) (EStr ".")))) (EStr "."))))) (EOp2 OCons (ENat 2) (EStr (".")))))) (ELam (EError "unbound")))).

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
  | OCons => "cons"
  | OEq => "eq"
  | OPlus => "plus"
  | OMinus => "minus"
  | OTimes => "times"
  end).

Definition ECons a b := EOp2 OCons a b.

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

Lemma correctness_of_interpretation_rec: forall n, forall fuel, fuel < n ->
   forall p s env names env_to,
     (exists s' msg, ev s fuel env (to_src names env_to p) = (s', VError msg)) \/
     ev s fuel env (to_src names env_to p) = ev s fuel env p.                Proof.
  intros nMax. induction nMax; intros fuel Hfuel.
  inversion Hfuel.
  intros.
  destruct fuel.
  simpl. left. repeat eexists.
  destruct p.
  - simpl. admit.
  - simpl. admit.
  - simpl. admit.
  - simpl. admit.
  - simpl. admit.
  - simpl. admit.
  - simpl. right. reflexivity.
  - simpl. admit.
  - simpl. admit.
  - simpl. admit.
  - simpl. admit.
  - simpl. right. reflexivity.
Admitted.

Theorem correctness_of_interpretation: forall p,
    (* conditions *)
    (exists s' msg, ev0 (to_src0 p) = (s', VError msg)) \/ ev0 (to_src0 p) = ev0 p.
Proof.
  unfold ev0. unfold to_src0. intros p.
  edestruct correctness_of_interpretation_rec with (n:=101) (fuel:=100) (p:=p). omega.
  left. eapply H.
  right. eapply H.
Qed.