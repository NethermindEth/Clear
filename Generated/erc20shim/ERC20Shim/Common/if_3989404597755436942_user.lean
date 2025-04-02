import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256

import Generated.erc20shim.ERC20Shim.Common.if_3989404597755436942_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_if_3989404597755436942 (s₀ s₉ : State) : Prop :=
  s₉.isOk ∧

  (--Case 1: No initial collision
    s₀.evm.hash_collision = false →
  (
    ( -- Case 1.1 : Reversion
      preservesEvm s₀ s₉ ∧
      s₉.evm.reverted = true  ∧
      s₀["_7"]!! ≠ 0
    )
    ∨
    ( -- Case 1.2 : No Reversion
      preservesEvm s₀ s₉ ∧
      s₀["_7"]!! = 0
    )
    ∨
      -- Case 1.3 : Collision in function
      s₉.evm.hash_collision = true
  )
  )
  ∧
  (-- Case 2: existing initial collision
     s₀.evm.hash_collision = true →
    s₉.evm.hash_collision = true
  )

lemma if_3989404597755436942_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3989404597755436942_concrete_of_code s₀ s₉ →
  Spec A_if_3989404597755436942 s₀ s₉ := by
  unfold if_3989404597755436942_concrete_of_code A_if_3989404597755436942

  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  rintro hasFuel ⟨s, call_encode, code⟩

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *

  unfold A_abi_encode_address_uint256_uint256 at call_encode

  rw [←s0_all] at call_encode
  rw [insert_of_ok] at call_encode
  rw [insert_of_ok] at call_encode
  rw [insert_of_ok] at call_encode
  simp at call_encode
  unfold setEvm at call_encode
  unfold multifill at call_encode
  simp at call_encode
  rw [insert_of_ok] at call_encode
  rw [insert_of_ok] at call_encode
  unfold lookup! at call_encode
  unfold State.insert at call_encode
  simp at call_encode

  generalize general_1 : (Finmap.lookup "_9"
                                (Finmap.insert "_11" 4
                                  (Finmap.insert "_10" (Fin.shiftLeft 957625571 226)
                                    (Finmap.insert "_9" (EVMState.mload evm₀ 64)
                                      (Finmap.insert "_8" 64
                                        (Finmap.insert "expr_3"
                                          (Finmap.lookup "var_value"
                                              (Finmap.insert "expr_2"
                                                (Finmap.lookup "_6"
                                                    (Finmap.insert "expr_1" (Finmap.lookup "var_from" varstore₀).get!
                                                      varstore₀)).get!
                                                (Finmap.insert "expr_1" (Finmap.lookup "var_from" varstore₀).get!
                                                  varstore₀))).get!
                                          (Finmap.insert "expr_2"
                                            (Finmap.lookup "_6"
                                                (Finmap.insert "expr_1" (Finmap.lookup "var_from" varstore₀).get!
                                                  varstore₀)).get!
                                            (Finmap.insert "expr_1" (Finmap.lookup "var_from" varstore₀).get!
                                              varstore₀)))))))).get! = gen_1 at *
  generalize general_2 : (Finmap.insert "_12" (gen_1 + 4)
                            (Finmap.insert "_11" 4
                              (Finmap.insert "_10" (Fin.shiftLeft 957625571 226)
                                (Finmap.insert "_9" (EVMState.mload evm₀ 64)
                                  (Finmap.insert "_8" 64
                                    (Finmap.insert "expr_3"
                                      (Finmap.lookup "var_value"
                                          (Finmap.insert "expr_2"
                                            (Finmap.lookup "_6"
                                                (Finmap.insert "expr_1" (Finmap.lookup "var_from" varstore₀).get!
                                                  varstore₀)).get!
                                            (Finmap.insert "expr_1" (Finmap.lookup "var_from" varstore₀).get!
                                              varstore₀))).get!
                                      (Finmap.insert "expr_2"
                                        (Finmap.lookup "_6"
                                            (Finmap.insert "expr_1" (Finmap.lookup "var_from" varstore₀).get!
                                              varstore₀)).get!
                                        (Finmap.insert "expr_1" (Finmap.lookup "var_from" varstore₀).get!
                                          varstore₀)))))))) = gen_2 at *
  generalize general_evm : (mstore evm₀
            (Finmap.lookup "_9"
                (Finmap.insert "_10" (Fin.shiftLeft 957625571 226)
                  (Finmap.insert "_9" (EVMState.mload evm₀ 64)
                    (Finmap.insert "_8" 64
                      (Finmap.insert "expr_3"
                        (Finmap.lookup "var_value"
                            (Finmap.insert "expr_2"
                              (Finmap.lookup "_6"
                                  (Finmap.insert "expr_1" (Finmap.lookup "var_from" varstore₀).get! varstore₀)).get!
                              (Finmap.insert "expr_1" (Finmap.lookup "var_from" varstore₀).get! varstore₀))).get!
                        (Finmap.insert "expr_2"
                          (Finmap.lookup "_6"
                              (Finmap.insert "expr_1" (Finmap.lookup "var_from" varstore₀).get! varstore₀)).get!
                          (Finmap.insert "expr_1" (Finmap.lookup "var_from" varstore₀).get! varstore₀))))))).get!
            (Fin.shiftLeft 957625571 226)) = gen_evm at *

  have s0__ok : (Ok gen_evm gen_2).isOk := by aesop
  by_cases _3_var : s₀["_7"]!! ≠ 0

  · clr_spec at call_encode

    simp [_3_var] at code
    obtain ⟨s_ok, ⟨s_preservesEvm, encode, s_no_collision⟩ | s_collision ⟩ := call_encode
    · obtain ⟨s_evm, ⟨s_varstore, s_all⟩⟩ := State_of_isOk s_ok

      have : Preserved evm₀ gen_evm := by
        rw[←general_evm]
        apply mstore_preserved

      have s0_s_preservesEvm : preservesEvm s₀ s := by
                apply preservesEvm_trans s0__ok
                aesop
                aesop

      have s_s9_preservesEvm : preservesEvm s s₉ := by
        have : Preserved s.evm s₉.evm := by
          have : (s.evm.account_map    = s₉.evm.account_map ∧
                          s.evm.hash_collision = s₉.evm.hash_collision ∧
                          s.evm.execution_env  = s₉.evm.execution_env ∧
                          s.evm.keccak_map     ≤ s₉.evm.keccak_map) := by
                          rw[←code]
                          unfold setEvm
                          simp [s_all]
                          rw [insert_of_ok]
                          unfold evm_revert
                          unfold evm_return
                          simp

          simp [Preserved_def]
          aesop
        aesop

      unfold setEvm at code
      simp [s_all] at code
      split_ands
      · aesop
      · intro s0_no_collision
        left
        split_ands
        · apply preservesEvm_trans s_ok
          all_goals aesop
        · aesop
        · aesop
      · rw[←code]
        unfold lookup! State.insert evm_revert evm_return
        simp
        unfold preservesEvm at s0_s_preservesEvm
        simp[←s0_all, s_all, Preserved_def] at s0_s_preservesEvm
        aesop
    · aesop
  · aesop

end

end ERC20Shim.Common
