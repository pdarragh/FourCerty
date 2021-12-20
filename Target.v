From FourCerty Require Import Utility NEVector.

Import Utility NEVector NEVectorNotations.

Module TargetLang.

(* There are 16 distinct 64-bit registers, plus [eax] that refers to the lower
   32 bits of [rax]. *)
Inductive register : Set :=
  | rax | rbx | rcx | rdx
  | rbp | rsp | rsi | rdi
  | r8  | r9  | r10 | r11
  | r12 | r13 | r14 | r15
  | eax.

(* Labels are just strings. *)
Definition label : Type := string.

(* Offsets are pairs of registers with an integer offset value. *)
Inductive offset : Type :=
  | Offset (reg : register) (z : Z).

(* [Mov] instructions only permit one of the two arguments to be an [Offset]. *)
Inductive mov_desc : Type :=
  | off_reg (off : offset) (reg : register)
  | off_int (off : offset) (int : Z)
  | reg_off (reg : register) (off : offset)
  | reg_int (reg : register) (int : Z).

Inductive tgt_ins : Type :=
  | TgtErr
  | Call (l : label)
  | Ret
  | Mov (desc: mov_desc)
  | Add (dst : register) (src : register + offset + Z)
  | Sub (dst : register) (src : register + offset + Z)
  | Cmp (a1 : register + offset) (a2 : register + offset + Z)
  | Jmp (x : label + register)
  | Je (x : label + register)
  | Jne (x : label + register)
  | Jl (x : label + register)
  | Jg (x : label + register)
  | And (dst : register + offset) (src : register + offset + Z)
  | Or (dst : register + offset) (src : register + offset + Z)
  | Xor (dst : register + offset) (src : register + offset + Z)
  | Sal (dst : register) (i : Z)
  | Sar (dst : register) (i : Z)
  | Push (a1 : Z + register)
  | Pop (a1 : register)
  | Lea (dst : register + offset) (x : label).

Definition registers := nevector nat 16.

Definition reg_id (reg : register) : nat :=
  match reg with
  | rax => 0
  | rbx => 1
  | rcx => 2
  | rdx => 3
  | rbp => 4
  | rsp => 5
  | rsi => 6
  | rdi => 7
  | r8  => 8
  | r9  => 9
  | r10 => 10
  | r11 => 11
  | r12 => 12
  | r13 => 13
  | r14 => 14
  | r15 => 15
  | eax => 0
  end.

Definition register_lookup (regs : registers) (reg : register) : nat :=
  regs[@ (reg_id reg)].

Inductive tgt_machine : Type :=
  | Machine (funs : partial_map nat)
            (inss : list tgt_ins)
            (regs : registers)
            (stack : list nat).

Definition machine_register_lookup (mchn : tgt_machine) (reg : register) : nat :=
  match mchn with
  | Machine _ _ regs _ => register_lookup regs reg
  end.

Definition push (mchn : tgt_machine) (val : nat) : tgt_machine :=
  match mchn with
  | Machine funs inss regs stack => Machine funs inss regs (val :: stack)
  end.

Definition pop (mchn : tgt_machine) : result (nat * tgt_machine) :=
  match mchn with
  | Machine funs inss regs [] => Err Error
  | Machine funs inss regs (v :: stack) => Ok (v, Machine funs inss regs stack)
  end.

Declare Scope tgt_scope.
Delimit Scope tgt_scope with tgt.

Notation "r [ z ]" := (Offset r z) (at level 80) : tgt_scope.
Notation "m <| r |>" := (machine_register_lookup m r) (at level 80) : tgt_scope.
Notation "m >> v ;; c" := (bind (pop m) (fun '(m, v) => c)) (at level 80) : tgt_scope.
Notation "m << v ;; c" := (let m := (push m v) in c) (at level 80) : tgt_scope.

Open Scope tgt_scope.

End TargetLang.
