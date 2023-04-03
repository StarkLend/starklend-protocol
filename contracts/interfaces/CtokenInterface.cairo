// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts for Cairo v0.2.1 (token/erc20/interfaces/IERC20.cairo)

%lang starknet

from starkware.cairo.common.uint256 import Uint256

@contract_interface
namespace ICToken {
    func name() -> (name: felt) {
    }

    func symbol() -> (symbol: felt) {
    }

    func decimals() -> (decimals: felt) {
    }

    func totalSupply() -> (totalSupply: Uint256) {
    }

    func balanceOf(account: felt) -> (balance: Uint256) {
    }

    func allowance(owner: felt, spender: felt) -> (remaining: Uint256) {
    }

    func transfer(recipient: felt, amount: Uint256) -> (success: felt) {
    }

    func transferFrom(sender: felt, recipient: felt, amount: Uint256) -> (success: felt) {
    }

    func borrow_balance_stored(account: felt) -> (balance: Uint256) {
    }

    func exchange_rate_stored(account: felt) -> (balance: Uint256) {
    }

    func get_oracle_price() -> (oracle_price: felt) {
    }

    func get_accrual_block_number() -> (block_number: felt) {
    }

    func approve(spender: felt, amount: Uint256) -> (success: felt) {
    }
}
