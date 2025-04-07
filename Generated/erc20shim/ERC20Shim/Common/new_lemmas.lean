import Clear.ReasoningPrinciple

namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

lemma lookupAcc_preserves_eq {evm evm' : EVMState} {varstore varstore' : VarStore} :
  preservesEvm (Ok evm varstore) (Ok evm' varstore') →
  evm.lookupAccount evm.execution_env.code_owner = evm'.lookupAccount evm'.execution_env.code_owner := by
  unfold lookupAccount
  intro preserves
  unfold preservesEvm at preserves
  simp [Preserved_def] at preserves
  have h1 : evm.execution_env.code_owner = evm'.execution_env.code_owner := by
    simp [preserves.2.2.1]
  have h2 : evm.account_map = evm'.account_map := by
    simp [preserves]
  rw[h1,h2]

lemma updateAcc_preserved_eq {evm evm' : EVMState} {varstore varstore' : VarStore} {slot value : UInt256} {act : Account}:
  preservesEvm (Ok evm varstore) (Ok evm' varstore') ∧
   evm.lookupAccount evm.execution_env.code_owner = act
  →
  Preserved (evm.updateAccount evm.execution_env.code_owner (act.updateStorage slot value))
            (evm'.updateAccount evm'.execution_env.code_owner (act.updateStorage slot value)) := by
  intro h
  obtain ⟨preserves, lookup⟩ := h

  have : evm.lookupAccount evm.execution_env.code_owner = evm'.lookupAccount evm'.execution_env.code_owner := by
    apply lookupAcc_preserves_eq preserves
  have : evm'.lookupAccount evm'.execution_env.code_owner = act := by
    rw[←this]
    exact lookup

  unfold preservesEvm at preserves
  simp [Preserved_def] at preserves
  have h1 : evm.execution_env.code_owner = evm'.execution_env.code_owner := by
    simp [preserves.2.2.1]
  rw[h1]
  simp[Preserved_def]
  unfold updateAccount
  simp
  obtain ⟨account, hash, exec, keccak⟩ := preserves
  aesop

lemma sstore_preserved_eq {evm evm' : EVMState} {varstore varstore' : VarStore} {slot value : UInt256} :
  preservesEvm (Ok evm varstore) (Ok evm' varstore') →
  preservesEvm (Ok (sstore evm slot value) varstore)
                (Ok (sstore evm' slot value) varstore') := by
  intro preserves
  unfold preservesEvm
  simp [Preserved_def]
  have : evm.lookupAccount evm.execution_env.code_owner =
          evm'.lookupAccount evm'.execution_env.code_owner := by
          apply lookupAcc_preserves_eq preserves
  have preserves_ : preservesEvm (Ok evm varstore) (Ok evm' varstore') :=
    by exact preserves
  unfold preservesEvm at preserves
  simp [Preserved_def] at preserves
  obtain ⟨account, hash, exec, keccak⟩ := preserves
  unfold sstore
  simp[this]

  cases  h: evm'.lookupAccount evm'.execution_env.code_owner with
  | none =>
    simp [account, hash, exec, keccak]
  | some act =>
    simp[h]
    have : Preserved (evm.updateAccount evm.execution_env.code_owner (act.updateStorage slot value))
              (evm'.updateAccount evm'.execution_env.code_owner (act.updateStorage slot value)) := by
              apply updateAcc_preserved_eq
              rw[←this] at h
              exact ⟨preserves_, h⟩
    simp[Preserved_def] at this
    exact this

lemma decide_UInt256_true {p :Prop} [h : Decidable p] :
  (decide p).toUInt256 ≠ 0  → p := by
  unfold Bool.toUInt256
  simp

lemma decide_UInt256_false {p :Prop} [h : Decidable p] :
  (decide p).toUInt256 ≠ 1 → ¬p := by
  unfold Bool.toUInt256
  simp

lemma preserves_evm_eq {evm : EVMState} {store store' : VarStore} :
  preservesEvm (Ok evm store) (Ok evm store') := by
  unfold preservesEvm
  simp

@[simp]
 lemma store_eq_store {evm' : EVMState} {varstore' : VarStore} :
   (Ok evm' varstore').store = varstore' :=
   by simp [State.store]
 
 @[aesop norm simp]
 lemma store_eq_store' {s' : State} {evm' : EVMState} {varstore' : VarStore} (h : s' = Ok evm' varstore') :
   s'.store = varstore' := by
   rw[h]
   simp [State.store]
 
 @[simp]
 lemma evm_eq_evm {evm' : EVMState} {varstore' : VarStore} :
   (Ok evm' varstore').evm = evm' :=
   by simp [State.evm]
 
 @[aesop norm simp]
 lemma evm_eq_evm' {s' : State} {evm' : EVMState} {varstore' : VarStore} (h : s' = Ok evm' varstore') :
   s'.evm = evm' := by
   rw[h]
   simp [State.evm]