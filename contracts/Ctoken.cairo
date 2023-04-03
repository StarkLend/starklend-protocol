%lang starknet

from starkware.starknet.common.syscalls import (
    get_caller_address,
    get_contract_address,
    get_block_number,
)
from starkware.cairo.common.cairo_builtins import HashBuiltin
from starkware.cairo.common.math import assert_not_zero, assert_lt, assert_nn, assert_not_equal
from starkware.cairo.common.math_cmp import is_nn
from starkware.cairo.common.bool import FALSE
from starkware.cairo.common.uint256 import Uint256, uint256_check, uint256_eq, uint256_not
from openzeppelin.security.safemath.library import SafeUint256
from openzeppelin.security.reentrancyguard.library import ReentrancyGuard
from openzeppelin.utils.constants.library import UINT8_MAX
from openzeppelin.token.erc20.IERC20 import IERC20

from comptroller import (
    mint_allowed,
    redeem_allowed,
    borrow_allowed,
    liquidate_borrow_allowed,
    repay_borrow_allowed,
    liquidate_calculate_seize_tokens,
    seize_allowed,
)

from interfaces.CtokenInterface import ICToken

// from starlink.ocr2.interfaces.IAggregator import IAggregator

//
// Events
//

@event
func Transfer(from_: felt, to: felt, value: Uint256) {
}

@event
func Mint(minter: felt, amount: Uint256, mint_tokens: Uint256) {
}

@event
func Redeem(redeemer: felt, amount: Uint256, redeem_tokens: Uint256) {
}

@event
func Borrow(borrower: felt, amount: Uint256, account_borrows: Uint256, total_borrows: Uint256) {
}

@event
func Approval(owner: felt, spender: felt, value: Uint256) {
}

//
// Storage
//

@storage_var
func ERC20_name() -> (name: felt) {
}

@storage_var
func ERC20_symbol() -> (symbol: felt) {
}

@storage_var
func underlying_storage() -> (address: felt) {
}

@storage_var
func oracle_storage() -> (address: felt) {
}

@storage_var
func ERC20_decimals() -> (decimals: felt) {
}

@storage_var
func ERC20_total_supply() -> (total_supply: Uint256) {
}

@storage_var
func ERC20_balances(account: felt) -> (balance: Uint256) {
}

@storage_var
func ERC20_allowances(owner: felt, spender: felt) -> (allowance: Uint256) {
}

@storage_var
func total_cash(address: felt) -> (cash: felt) {
}

@storage_var
func total_borrows() -> (borrow: felt) {
}

@storage_var
func total_reserves() -> (reserves: felt) {
}

@storage_var
func borrow_principal(address: felt) -> (principal: felt) {
}

@storage_var
func accrual_block_number() -> (b_n: felt) {
}

@storage_var
func borrow_interest(address: felt) -> (interest_index: felt) {
}

@storage_var
func initial_exchange_rate_mantissa(token: felt) -> (exchange_rate: felt) {
}

@storage_var
func protocol_seize_share() -> (protocol_seize: felt) {
}

namespace Ctoken {
    //
    // Initializer
    //

    func initializer{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        name: felt, symbol: felt, decimals: felt, underlying: felt, oracle_address: felt
    ) {
        ERC20_name.write(name);
        ERC20_symbol.write(symbol);
        underlying_storage.write(underlying);
        oracle_storage.write(oracle_address);

        let (block_number) = get_block_number();

        accrual_block_number.write(block_number);
        with_attr error_message("ERC20: decimals exceed 2^8") {
            assert_lt(decimals, UINT8_MAX);
        }
        ERC20_decimals.write(decimals);
        return ();
    }

    //
    // Public functions
    //

    func name{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}() -> (name: felt) {
        let (name) = ERC20_name.read();
        return (name,);
    }

    func symbol{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}() -> (
        symbol: felt
    ) {
        let (symbol) = ERC20_symbol.read();
        return (symbol,);
    }

    func total_supply{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}() -> (
        total_supply: Uint256
    ) {
        let (total_supply: Uint256) = ERC20_total_supply.read();
        return (total_supply,);
    }

    func decimals{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}() -> (
        decimals: felt
    ) {
        let (decimals) = ERC20_decimals.read();
        return (decimals,);
    }

    func balance_of{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        account: felt
    ) -> (balance: Uint256) {
        let (balance: Uint256) = ERC20_balances.read(account);
        return (balance,);
    }

    func allowance{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        owner: felt, spender: felt
    ) -> (remaining: Uint256) {
        let (remaining: Uint256) = ERC20_allowances.read(owner, spender);
        return (remaining,);
    }

    func transfer{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        recipient: felt, amount: Uint256
    ) {
        let (sender) = get_caller_address();
        _transfer(sender, recipient, amount);
        return ();
    }

    func transfer_from{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        sender: felt, recipient: felt, amount: Uint256
    ) -> () {
        let (caller) = get_caller_address();
        // subtract allowance
        _spend_allowance(sender, caller, amount);
        // execute transfer
        _transfer(sender, recipient, amount);
        return ();
    }

    func approve{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        spender: felt, amount: Uint256
    ) {
        with_attr error_message("ERC20: amount is not a valid Uint256") {
            uint256_check(amount);
        }

        let (caller) = get_caller_address();
        _approve(caller, spender, amount);
        return ();
    }

    func increase_allowance{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        spender: felt, added_value: Uint256
    ) -> () {
        with_attr error("ERC20: added_value is not a valid Uint256") {
            uint256_check(added_value);
        }

        let (caller) = get_caller_address();
        let (current_allowance: Uint256) = ERC20_allowances.read(caller, spender);

        // add allowance
        with_attr error_message("ERC20: allowance overflow") {
            let (new_allowance: Uint256) = SafeUint256.add(current_allowance, added_value);
        }

        _approve(caller, spender, new_allowance);
        return ();
    }

    func decrease_allowance{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        spender: felt, subtracted_value: Uint256
    ) -> () {
        alloc_locals;
        with_attr error_message("ERC20: subtracted_value is not a valid Uint256") {
            uint256_check(subtracted_value);
        }

        let (caller) = get_caller_address();
        let (current_allowance: Uint256) = ERC20_allowances.read(owner=caller, spender=spender);

        with_attr error_message("ERC20: allowance below zero") {
            let (new_allowance: Uint256) = SafeUint256.sub_le(current_allowance, subtracted_value);
        }

        _approve(caller, spender, new_allowance);
        return ();
    }

    func borrow_balance_stored{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        account: felt, token: felt
    ) -> (balance: Uint256) {
        alloc_locals;

        let (borrow_balance) = _borrow_balance_stored_internal(account, token);

        return (borrow_balance,);
    }

    func exchange_rate_stored{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        account: felt, token: felt
    ) -> (balance: Uint256) {
        alloc_locals;

        let (exchange_rate) = _exchange_rate_stored_internal(account, token);

        return (exchange_rate,);
    }

    func get_oracle_price{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}() -> (
        balance: felt
    ) {
        alloc_locals;

        let (oracle_add) = oracle_storage.read();

        // let (round) = IAggregator.latest_round_data();

        return (1,);
    }

    func get_accrual_block_number{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        ) -> (block_numbher: felt) {
        alloc_locals;

        let (b_n) = accrual_block_number.read();

        return (b_n,);
    }

    //
    // Internal
    //

    func uint256_to_address_felt(x: Uint256) -> (address: felt) {
        return (x.low + x.high * 2 ** 128,);
    }

    func _exchange_rate_stored_internal{
        syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr
    }(account: felt, token: felt) -> (exchange_rate: felt) {
        alloc_locals;

        let (tot_cash) = total_cash.read(account);
        let (tot_borrow) = total_borrows.read();
        let (total_supply) = IERC20.totalSupply(token);
        let (total_supply_felt) = uint256_to_address_felt(total_supply);
        // let (cmp) = uint256_signed_le(total_supply, Uint256(low=0, high=0))

        if (total_supply_felt == 0) {
            let (initial_rate) = initial_exchange_rate_mantissa.read(token);
            return (initial_rate,);
        }

        let cash_plus_borrow = tot_cash + tot_borrow;
        let exchnage_rate = cash_plus_borrow / total_supply_felt;
        let Uint256_exchange_rate = Uint256(exchnage_rate, 0);

        return (Uint256_exchange_rate,);
    }

    func _borrow_balance_stored_internal{
        syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr
    }(account: felt) -> (balance: Uint256) {
        alloc_locals;

        let (principal) = borrow_principal.read(account);

        // let tokenA_Uint256 = Uint256(low=tokenA, high=0)
        // let tokenB_Uint256 = Uint256(low=tokenB, high=0)
        // let (v) = uint256_signed_le(tokenA_Uint256, tokenB_Uint256)

        if (principal == 0) {
            return (0,);
        }

        let (borrow_index) = borrow_interest.read(account);

        // borrow index
        let principalTimesIndex = principal * 1;
        let borrow_balance = principalTimesIndex / borrow_index;

        return (Uint256(borrow_balance),);
    }

    func _mint{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        recipient: felt, amount: Uint256
    ) {
        with_attr error_message("ERC20: amount is not a valid Uint256") {
            uint256_check(amount);
        }

        with_attr error_message("ERC20: cannot mint to the zero address") {
            assert_not_zero(recipient);
        }

        let (token_address) = get_contract_address();

        let (m_allowed) = mint_allowed(token_address, recipient, amount);

        with_attr error_message("ERC20: mint not allowed") {
            assert_nn(m_allowed);
        }

        // @todo add check for Verify market's block number equals current block number */

        let (accrual_b_n) = accrual_block_number.read();
        let (curr_b_n) = get_block_number();
        with_attr error_message("ERC20: mint not allowed") {
            assert_not_equal(accrual_b_n, curr_b_n);
        }

        let (underlying_contract) = underlying_storage.read();
        let (user) = get_caller_address();

        ReentrancyGuard._start();
        IERC20.transferFrom(underlying_contract, user, token_address, amount);

        let (exchange_rate) = _exchange_rate_stored_internal(recipient, token_address);

        let (mint_token, rem) = SafeUint256.div_rem(amount, exchange_rate);

        let (supply: Uint256) = ERC20_total_supply.read();
        with_attr error_message("ERC20: mint overflow") {
            let (new_supply: Uint256) = SafeUint256.add(supply, mint_token);
        }

        ERC20_total_supply.write(new_supply);

        let (balance: Uint256) = ERC20_balances.read(account=recipient);
        // overflow is not possible because sum is guaranteed to be less than total supply
        // which we check for overflow below
        let (new_balance: Uint256) = SafeUint256.add(balance, mint_token);
        ERC20_balances.write(recipient, new_balance);

        Mint.emit(recipient, amount, mint_token);
        Transfer.emit(token_address, recipient, mint_token);

        ReentrancyGuard._end();
        return ();
    }

    func _redeem{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        redeemer: felt, redeem_token_in: Uint256, redeem_amount: Uint256
    ) {
        with_attr error_message("ERC20: amount is not a valid Uint256") {
            uint256_check(redeem_amount);
        }

        with_attr error_message("ERC20: cannot mint to the zero address") {
            assert_not_zero(redeemer);
        }

        let (token_address) = get_contract_address();
        let (exchange_r) = _exchange_rate_stored_internal(redeemer, token_address);
        let cmp = is_nn(redeem_token_in);

        local redeem_token;
        local redeem_amount;

        if (cmp == 0) {
            redeem_token = redeem_token_in;
            let (mul) = SafeUint256.mul(exchange_r, redeem_token_in);
            redeem_amount = mul;
        } else {
            let (div, rem) = SafeUint256.div_rem(redeem_token_in, exchange_r);

            redeem_token = div;
            redeem_amount = redeem_amount;
        }

        let (m_allowed) = redeem_allowed(token_address, redeemer, redeem_token);

        with_attr error_message("ERC20: redeem not allowed") {
            assert_nn(m_allowed);
        }

        // @todo add check for Verify market's block number equals current block number */

        let (accrual_b_n) = accrual_block_number.read();
        let (curr_b_n) = get_block_number();
        with_attr error_message("ERC20: redeem not allowed") {
            assert_not_equal(accrual_b_n, curr_b_n);
        }

        let (tot_cash) = total_cash.read(redeemer);
        let total_cash_uint = Uint256(tot_cash);

        let (diff) = SafeUint256.sub_le(tot_cash, redeem_amount);

        let cmp1 = is_nn(diff);

        with_attr error_message("ERC20: redeem not allowed total cash is less") {
            assert_nn(cmp1);
        }

        let (supply: Uint256) = ERC20_total_supply.read();
        with_attr error_message("ERC20: mint overflow") {
            let (new_supply: Uint256) = SafeUint256.sub_le(supply, redeem_token);
        }

        ReentrancyGuard._start();

        ERC20_total_supply.write(new_supply);

        let (balance: Uint256) = ERC20_balances.read(account=redeemer);
        // overflow is not possible because sum is guaranteed to be less than total supply
        // which we check for overflow below
        let (new_balance: Uint256) = SafeUint256.sub_le(balance, redeem_token);
        ERC20_balances.write(redeemer, new_balance);

        // do transfer out
        let (underlying_contract) = underlying_storage.read();
        IERC20.transferFrom(underlying_contract, token_address, redeemer, redeem_amount);

        Transfer.emit(redeemer, token_address, redeem_token);
        Redeem.emit(redeemer, redeem_amount, redeem_token);

        ReentrancyGuard._end();
        return ();
    }

    func _borrow{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        borrower: felt, amount: Uint256
    ) {
        with_attr error_message("ERC20: amount is not a valid Uint256") {
            uint256_check(amount);
        }

        with_attr error_message("ERC20: cannot mint to the zero address") {
            assert_not_zero(borrower);
        }

        let (token_address) = get_contract_address();

        let (m_allowed) = borrow_allowed(token_address, borrower, amount);

        with_attr error_message("ERC20: mint not allowed") {
            assert_nn(m_allowed);
        }

        // @todo add check for Verify market's block number equals current block number */
        let (accrual_b_n) = accrual_block_number.read();
        let (curr_b_n) = get_block_number();
        with_attr error_message("ERC20: borrow not allowed") {
            assert_not_equal(accrual_b_n, curr_b_n);
        }

        let (tot_cash) = total_cash.read(borrower);
        let total_cash_uint = Uint256(tot_cash);

        let (diff) = SafeUint256.sub_le(tot_cash, amount);

        let cmp1 = is_nn(diff);

        with_attr error_message("ERC20: borrow not allowed total cash is less") {
            assert_nn(cmp1);
        }

        ReentrancyGuard._start();
        let (account_borrow_prev) = _borrow_balance_stored_internal(borrower);

        let (new_account_borrow) = SafeUint256.add(account_borrow_prev, amount);
        let (total_borr) = total_borrows.read();
        let (total_borrow_amount) = SafeUint256.add(total_borr, amount);

        borrow_principal.write(borrower, new_account_borrow);

        // @todo How is borrow interest even coming here Ask ssj
        // borrow_interest.write(borrower, )

        total_borrows.write(total_borrow_amount);

        let (underlying_contract) = underlying_storage.read();
        IERC20.transferFrom(underlying_contract, token_address, borrower, amount);

        Borrow.emit(borrower, amount, new_account_borrow, total_borrow_amount);
        ReentrancyGuard._end();
        return ();
    }

    func _repay_borrow{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        payer: felt, borrower: felt, amount: Uint256
    ) -> (repay_amount: Uint256) {
        with_attr error_message("ERC20: amount is not a valid Uint256") {
            uint256_check(amount);
        }

        with_attr error_message("ERC20: cannot mint to the zero address") {
            assert_not_zero(borrower);
        }

        let (token_address) = get_contract_address();

        let (m_allowed) = repay_borrow_allowed(token_address, payer, borrower, amount);

        with_attr error_message("ERC20: mint not allowed") {
            assert_nn(m_allowed);
        }

        // @todo add check for Verify market's block number equals current block number */
        let (accrual_b_n) = accrual_block_number.read();
        let (curr_b_n) = get_block_number();
        with_attr error_message("ERC20: mint not allowed") {
            assert_not_equal(accrual_b_n, curr_b_n);
        }

        let (account_borrow_prev) = _borrow_balance_stored_internal(borrower);

        let MAX_UINT = Uint256(-1);

        local repay_amount_final;

        if (repay_amount == MAX_UINT) {
            repay_amount_final = account_borrow_prev;
        } else {
            repay_amount_final = amount;
        }

        ReentrancyGuard._start();

        let (underlying_contract) = underlying_storage.read();
        IERC20.transferFrom(underlying_contract, payer, token_address, repay_amount_final);

        let (new_account_borrow) = SafeUint256.sub_le(account_borrow_prev, repay_amount_final);
        let (total_borr) = total_borrows.read();
        let (total_borrow_amount) = SafeUint256.sub_le(total_borr, repay_amount_final);

        borrow_principal.write(borrower, new_account_borrow);

        // @todo How is borrow interest even coming here Ask ssj
        // borrow_interest.write(borrower, )

        total_borrows.write(total_borrow_amount);

        Borrow.emit(borrower, amount, new_account_borrow, total_borrow_amount);

        ReentrancyGuard._end();
        return (repay_amount_final,);
    }

    func _seize_internal{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        seizer_token: felt, liquidator: felt, borrower: felt, seize_tokens: felt
    ) {
        let (token_address) = get_contract_address();

        let (s_allowed) = seize_allowed(
            token_address, seizer_token, liquidator, borrower, seize_tokens
        );

        with_attr error_message("ERC20: mint not allowed") {
            assert_nn(s_allowed);
        }

        // liquidator should not be borrower
        with_attr error_message("ERC20: seize not allowed") {
            assert_not_equal(liquidator, borrower);
        }

        let (protocol_seize_s) = protocol_seize_share.read();

        let (protocol_seize_tokens) = SafeUint256.mul(seize_tokens, protocol_seize_s);
        let (liquidator_seize_tokens) = SafeUint256.sub_le(seize_tokens, protocol_seize_tokens);

        let (exchange_rate) = _exchange_rate_stored_internal(borrower, seizer_token);

        ReentrancyGuard._start();
        let (protocol_seize_amt) = SafeUint256.mul(exchange_rate, protocol_seize_tokens);
        let (total_r) = total_reserves.read();

        let (total_r_new) = SafeUint256.add(total_r, protocol_seize_amt);

        total_reserves.write(total_r_new);

        let (total_sup) = ERC20_total_supply.read();

        let (new_total_sup) = SafeUint256.sub_le(total_sup, protocol_seize_tokens);

        ERC20_total_supply.write(new_total_sup);

        let (borrower_balance) = ERC20_balances.read(borrower);
        let (new_borrower_balance) = borrower_balance - seize_tokens;

        ERC20_balances.write(borrower, new_borrower_balance);

        let (liquidator_balance) = ERC20_balances.read(liquidator);
        let (new_liquidator_balance) = liquidator_balance + liquidator_seize_tokens;

        ERC20_balances.write(liquidator, new_liquidator_balance);
        ReentrancyGuard._end();
        return ();
    }

    func _liquidate_borrow{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        liquidator: felt, borrower: felt, repay_amount: Uint256, token_collateral: felt
    ) {
        with_attr error_message("ERC20: amount is not a valid Uint256") {
            uint256_check(repay_amount);
        }

        with_attr error_message("ERC20: amount should be greater than 0") {
            assert_not_zero(repay_amount);
        }

        with_attr error_message("ERC20: cannot mint to the zero address") {
            assert_not_zero(borrower);
        }

        let (token_address) = get_contract_address();

        let (m_allowed) = liquidate_borrow_allowed(
            token_address, token_collateral, liquidator, borrower, repay_amount
        );

        with_attr error_message("ERC20: mint not allowed") {
            assert_nn(m_allowed);
        }

        // @todo add check for Verify market's block number equals current block number */
        let (accrual_b_n) = accrual_block_number.read();
        let (curr_b_n) = get_block_number();
        with_attr error_message("ERC20: liquidate borrow not allowed") {
            assert_not_equal(accrual_b_n, curr_b_n);
        }

        let (token_collateral_block_number) = ICToken.get_accrual_block_number(token_collateral);
        with_attr error_message("ERC20: liquidate borrow not allowed") {
            assert_not_equal(token_collateral_block_number, curr_b_n);
        }

        // liquidator should not be borrower
        with_attr error_message("ERC20: liquidate borrow not allowed") {
            assert_not_equal(liquidator, borrower);
        }

        ReentrancyGuard._start();
        let (actual_repay_amount) = _repay_borrow(liquidator, borrower, repay_amount);

        let (_err, seize_token) = liquidate_calculate_seize_tokens(
            borrower, token_address, token_collateral, actual_repay_amount
        );

        let (balance) = IERC20.balanceOf(token_collateral, borrower);

        if (token_collateral == token_address) {
            _seize_internal(token_address, liquidator, borrower, seize_token);
        } else {
            _seize_internal(token_collateral, liquidator, borrower, seize_token);
        }

        ReentrancyGuard._end();
        return ();
    }

    func _burn{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        account: felt, amount: Uint256
    ) {
        with_attr error_message("ERC20: amount is not a valid Uint256") {
            uint256_check(amount);
        }

        with_attr error_message("ERC20: cannot burn from the zero address") {
            assert_not_zero(account);
        }

        let (balance: Uint256) = ERC20_balances.read(account);
        with_attr error_message("ERC20: burn amount exceeds balance") {
            let (new_balance: Uint256) = SafeUint256.sub_le(balance, amount);
        }

        ERC20_balances.write(account, new_balance);

        let (supply: Uint256) = ERC20_total_supply.read();
        let (new_supply: Uint256) = SafeUint256.sub_le(supply, amount);
        ERC20_total_supply.write(new_supply);
        Transfer.emit(account, 0, amount);
        return ();
    }

    func _transfer{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        sender: felt, recipient: felt, amount: Uint256
    ) {
        with_attr error_message("ERC20: amount is not a valid Uint256") {
            uint256_check(amount);  // almost surely not needed, might remove after confirmation
        }

        with_attr error_message("ERC20: cannot transfer from the zero address") {
            assert_not_zero(sender);
        }

        with_attr error_message("ERC20: cannot transfer to the zero address") {
            assert_not_zero(recipient);
        }

        let (sender_balance: Uint256) = ERC20_balances.read(account=sender);
        with_attr error_message("ERC20: transfer amount exceeds balance") {
            let (new_sender_balance: Uint256) = SafeUint256.sub_le(sender_balance, amount);
        }

        ERC20_balances.write(sender, new_sender_balance);

        // add to recipient
        let (recipient_balance: Uint256) = ERC20_balances.read(account=recipient);
        // overflow is not possible because sum is guaranteed by mint to be less than total supply
        let (new_recipient_balance: Uint256) = SafeUint256.add(recipient_balance, amount);
        ERC20_balances.write(recipient, new_recipient_balance);
        Transfer.emit(sender, recipient, amount);
        return ();
    }

    func _approve{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        owner: felt, spender: felt, amount: Uint256
    ) {
        with_attr error_message("ERC20: amount is not a valid Uint256") {
            uint256_check(amount);
        }

        with_attr error_message("ERC20: cannot approve from the zero address") {
            assert_not_zero(owner);
        }

        with_attr error_message("ERC20: cannot approve to the zero address") {
            assert_not_zero(spender);
        }

        ERC20_allowances.write(owner, spender, amount);
        Approval.emit(owner, spender, amount);
        return ();
    }

    func _spend_allowance{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
        owner: felt, spender: felt, amount: Uint256
    ) {
        alloc_locals;
        with_attr error_message("ERC20: amount is not a valid Uint256") {
            uint256_check(amount);  // almost surely not needed, might remove after confirmation
        }

        let (current_allowance: Uint256) = ERC20_allowances.read(owner, spender);
        let (infinite: Uint256) = uint256_not(Uint256(0, 0));
        let (is_infinite: felt) = uint256_eq(current_allowance, infinite);

        if (is_infinite == FALSE) {
            with_attr error_message("ERC20: insufficient allowance") {
                let (new_allowance: Uint256) = SafeUint256.sub_le(current_allowance, amount);
            }

            _approve(owner, spender, new_allowance);
            return ();
        }
        return ();
    }
}
