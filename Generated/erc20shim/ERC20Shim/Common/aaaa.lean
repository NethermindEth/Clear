import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_address
import Generated.erc20shim.ERC20Shim.abi_encode_uint256_to_uint256

import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256_gen

namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

set_option maxHeartbeats 2500000
set_option maxRecDepth 1000

theorem Generated.erc20shim.ERC20Shim.extracted_1 {s₉ : State} {value pos : Literal} (evm₀ : EVM) (varstore₀ : VarStore)
  (hasFuel : ¬❓ s₉) (s_inhabited : State)
  (s_inhabited_all : Ok evm₀ Inhabited.default⟦"pos"↦pos⟧⟦"value"↦value⟧ = s_inhabited) (s₀ : State)
  (s0_all : Ok evm₀ varstore₀ = s₀) (code : Ok (mstore evm₀ pos value) varstore₀ = s₉) :
  s₉.isOk ∧
    (s₀.evm.hash_collision = false →
        preservesEvm s₀ s₉ ∧ Ok (mstore s₀.evm pos value) s₀.store = s₉ ∧ s₉.evm.hash_collision = false ∨
          s₉.evm.hash_collision = true) ∧
      (s₀.evm.hash_collision = true → s₉.evm.hash_collision = true) := sorry

















end

end ERC20Shim.Common
