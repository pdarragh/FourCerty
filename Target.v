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

Definition register_vector := nevector nat 16.
Definition empty_registers : register_vector := replicate1 0 15.

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

Inductive tgt_machine : Type :=
  | Machine
      (* Functions are names correlated to addresses on the stack. *)
      (funs : partial_map nat)
      (inss : list tgt_ins)
      (regs : register_vector)
      (stack : list nat).

Definition register_lookup (mchn : tgt_machine) (reg : register) : nat :=
  match mchn with
  | Machine _ _ regs _ => regs[@ (reg_id reg)]
  end.

Definition offset_to_addr (mchn : tgt_machine) (off : offset) : nat :=
  match off with
  | Offset reg o => (register_lookup mchn reg) + (Z.to_nat o)
  end.

Definition offset_lookup (mchn : tgt_machine) (off : offset) : result nat :=
  match off with
  | Offset reg o =>
      match mchn with
      | Machine _ _ _ stack =>
          let addr := register_lookup mchn reg in
          match List.nth_error stack (addr + (Z.to_nat o)) with
          | None => Err (ErrorMsg "Out-of-bounds memory access.")
          | Some v => Ok v
          end
      end
  end.

Definition read_memory := offset_lookup.

Definition write_memory (mchn : tgt_machine) (off : offset) (val : nat) : result tgt_machine :=
  match mchn with
  | Machine funs inss regs stack =>
      stack' <- update_nth stack (offset_to_addr mchn off) val;;
      ret (Machine funs inss regs stack')
  end.

Definition push (val : nat) (mchn : tgt_machine) : tgt_machine :=
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

Notation "r {{ z }}" := (Offset r z) (at level 80) : tgt_scope.
Notation "m <| r |>" := (register_lookup m r) (at level 10) : tgt_scope.
Notation "m <|| o ||>" := (offset_lookup m o) (at level 10) : tgt_scope.
Infix ">>" := push (at level 80) : tgt_scope.

(* I cannot for the life of me get this notation to work correctly. *)
(* Notation "v <<- m ; c" := (bind (pop m) (fun '(v, x) => c)) (at level 61, m at next level, m binder, right associativity) : tgt_scope. *)

Open Scope tgt_scope.

End TargetLang.
