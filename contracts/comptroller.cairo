// Declare this file as a StarkNet contract.
%lang starknet

from starkware.cairo.common.cairo_builtins import HashBuiltin
// from starkware.cairo.common.cairo_keccak.keccak import keccak_felts
from starkware.cairo.common.math import assert_not_equal
from starkware.cairo.common.math_cmp import is_nn
from starkware.cairo.common.uint256 import uint256_eq, uint256_add, uint256_signed_le, Uint256
from starkware.starknet.common.syscalls import get_caller_address
from starkware.cairo.common.hash import hash2
from starkware.starknet.common.syscalls import deploy
from starkware.cairo.common.alloc import alloc
from openzeppelin.security.safemath.library import SafeUint256
from openzeppelin.token.erc20.IERC20 import IERC20
// from starkware.cairo.common.cairo_builtins import BitwiseBuiltin
// from starkware.starknet.core.os.contract_address import get_contract_address

from interfaces.CtokenInterface import ICToken

const maxAssests = 10;

// struct Membership:
//     member isMember: felt
//     member address: felt
// end

// struct Market:
//     member isListed: felt
//     member collateralFactorMantissa: Uint256
//     member membership: Membership*
// end

@event
func market_entered_eve(token: felt, borrower: felt) {
}

@event
func market_exited_eve(token: felt, borrower: felt) {
}

@storage_var
func markets_is_listed(token: felt) -> (isListed: felt) {
}

@storage_var
func markets_is_listed_length(token: felt) -> (isListed_length: felt) {
}

@storage_var
func markets_account_mmebership(token: felt, borrower: felt) -> (is_member: felt) {
}

@storage_var
func markets_account_mmebership_length(token: felt, index: felt) -> (is_member_length: felt) {
}

@storage_var
func markets_collateral_factor(token: felt) -> (collateralFactorMantissa: felt) {
}

@storage_var
func markets_is_comped(token: felt) -> (isComped: felt) {
}

@storage_var
func markets_collateral_factor_length(token: felt) -> (collateralFactorMantissa_length: felt) {
}

@storage_var
func admin_store() -> (admin: felt) {
}

@storage_var
func account_assets(address: felt, index: felt) -> (token: felt) {
}

@storage_var
func account_assets_length(address: felt) -> (token_length: felt) {
}

@storage_var
func borrow_principal_re(address: felt) -> (principal: felt) {
}

@storage_var
func borrow_interest_re(address: felt) -> (interest_index: felt) {
}

@storage_var
func total_cash_re(address: felt) -> (cash: felt) {
}

@storage_var
func total_borrows_re(address: felt) -> (borrow: felt) {
}

@storage_var
func borrow_caps(address: felt) -> (borrow_caps: felt) {
}

@storage_var
func initial_exchange_rate_mantissa_re(token: felt) -> (exchange_rate: felt) {
}

@storage_var
func close_factor() -> (f: Uint256) {
}

@constructor
func constructor{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}() {
    let (admin) = get_caller_address();

    admin_store.write(admin);
    return ();
}

func uint256_to_address_felt(x: Uint256) -> (address: felt) {
    return (x.low + x.high * 2 ** 128,);
}

func _borrow_balance_stored_internal{
    syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr
}(account: felt) -> (balance: felt) {
    alloc_locals;

    let (principal) = borrow_principal_re.read(account);

    // let tokenA_Uint256 = Uint256(low=tokenA, high=0)
    // let tokenB_Uint256 = Uint256(low=tokenB, high=0)
    // let (v) = uint256_signed_le(tokenA_Uint256, tokenB_Uint256)

    if (principal == 0) {
        return (0,);
    }

    let (borrow_index) = borrow_interest_re.read(account);

    // borrow index
    let principalTimesIndex = principal * 1;
    let borrow_balance = principalTimesIndex / borrow_index;

    return (borrow_balance,);
}

func _exchange_rate_stored_internal{
    syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr
}(account: felt, token: felt) -> (exchange_rate: felt) {
    alloc_locals;

    let (tot_cash) = total_cash_re.read(account);
    let (tot_borrow) = total_borrows_re.read(account);
    let (total_supply) = IERC20.totalSupply(token);
    let (total_supply_felt) = uint256_to_address_felt(total_supply);
    // let (cmp) = uint256_signed_le(total_supply, Uint256(low=0, high=0))

    if (total_supply_felt == 0) {
        let (initial_rate) = initial_exchange_rate_mantissa_re.read(token);
        return (initial_rate,);
    }

    let cash_plus_borrow = tot_cash + tot_borrow;
    let exchnage_rate = cash_plus_borrow / total_supply_felt;

    return (exchnage_rate,);
}

func get_account_snapshot{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    account: felt, token: felt
) -> (token_balance: Uint256, borrow_balance: felt, exchange_rate: felt) {
    alloc_locals;

    let (tok_balance) = IERC20.balanceOf(token, account);
    let (borrow_balance) = _borrow_balance_stored_internal(account);
    let (exchange_rate) = _exchange_rate_stored_internal(account, token);

    return (tok_balance, borrow_balance, exchange_rate);
}

func _get_assets_in{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    all_account_assets: felt*, account: felt, size: felt, i: felt
) -> (tokens: felt*) {
    alloc_locals;

    if (i == size - 1) {
        return (all_account_assets,);
    }

    let (token) = account_assets.read(account, i);

    assert all_account_assets[i] = token;

    return _get_assets_in(all_account_assets, account, size, i + 1);
}

// todo main func
@external
func get_assets_in{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    account: felt
) -> (tokens_len: felt, tokens: felt*) {
    alloc_locals;

    let (acc_assets_len) = account_assets_length.read(account);
    let (all_account_assets: felt*) = alloc();

    let (toks) = _get_assets_in(all_account_assets, account, acc_assets_len, 0);

    return (acc_assets_len, toks);
}

func _add_to_market_internal{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    token: felt, borrower: felt
) -> (error: felt) {
    alloc_locals;

    // asert check is listed

    markets_account_mmebership.write(token, borrower, 1);
    let (acc_assets_len) = account_assets_length.read(borrower);
    account_assets.write(borrower, acc_assets_len - 1, token);
    account_assets_length.write(borrower, acc_assets_len + 1);
    market_entered_eve.emit(token, borrower);

    return (0,);
}

func _enter_markets{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    market_entered: felt*, caller: felt, tokens: felt*, size: felt, i: felt
) -> (market_eneterd_error: felt*) {
    alloc_locals;

    if (i == size - 1) {
        return (market_entered,);
    }

    let (add_to_market) = _add_to_market_internal(tokens[i], caller);

    assert market_entered[i] = add_to_market;

    return _enter_markets(market_entered, caller, tokens, size, i + 1);
}

@external
func enter_markets{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    tokens_len: felt, tokens: felt*
) -> (markets_len: felt, markets: felt*) {
    alloc_locals;
    let (market_entered: felt*) = alloc();
    let (caller) = get_caller_address();

    let (results) = _enter_markets(market_entered, caller, tokens, tokens_len, 0);

    return (tokens_len, results);
}

func _delete_account_asset{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    token: felt, account: felt, account_assets_len: felt, index: felt
) {
    alloc_locals;

    if (index == account_assets_len - 1) {
        return ();
    }

    let (account_asset) = account_assets.read(account, index);

    if (account_asset == token) {
        // move stuff

        let (last_token) = account_assets.read(account, account_assets_len);

        account_assets.write(account, index, last_token);
        account_assets_length.write(account, account_assets_len - 1);
        return ();
    }

    return _delete_account_asset(token, account, account_assets_len, index + 1);
}

@external
func exit_markets{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(token: felt) -> (
    error: felt
) {
    alloc_locals;
    let (market_entered: felt*) = alloc();
    let (caller) = get_caller_address();

    let (tok_balance, borrow_balance, exchange_rate) = get_account_snapshot(caller, token);

    let (is_account_member) = markets_account_mmebership.read(token, caller);

    if (is_account_member == 0) {
        return (0,);
    }

    // delete from account assets
    let (account_assets_len) = account_assets_length.read(caller);
    _delete_account_asset(token, caller, account_assets_len, 0);

    markets_account_mmebership.write(token, caller, 0);
    market_exited_eve.emit(token, caller);

    return (0,);
}

func _get_account_liquidity{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    address: felt,
    token_modify: felt,
    redeem_tokens: felt,
    borrow_amount: felt,
    size: felt,
    index: felt,
    sum_collateral: felt,
    sum_borrow_effect: felt,
) -> (coll: felt, borrow: felt) {
    alloc_locals;

    if (index == size - 1) {
        return (sum_collateral, sum_borrow_effect);
    }

    let (token) = account_assets.read(address, index);
    let (tok_balance, borrow_balance, exchange_rate) = get_account_snapshot(address, token);
    let (collateral_factor) = markets_collateral_factor.read(token);

    let (oracle_price) = ICToken.get_oracle_price(token);

    let token_den = collateral_factor * exchange_rate * oracle_price;

    let (tok_balance_felt) = uint256_to_address_felt(tok_balance);
    let sum_coll = token_den * tok_balance_felt;
    let borrow_effect = oracle_price * borrow_balance;

    if (token == token_modify) {
        let borrow_effect = token_den * redeem_tokens;

        let borrow_effect = oracle_price * borrow_amount;

        // oracle price multiplication
        return _get_account_liquidity(
            address,
            token_modify,
            redeem_tokens,
            borrow_amount,
            size,
            index + 1,
            sum_collateral + sum_coll,
            sum_borrow_effect + borrow_effect,
        );
    }

    return _get_account_liquidity(
        address,
        token_modify,
        redeem_tokens,
        borrow_amount,
        size,
        index + 1,
        sum_collateral + sum_coll,
        sum_borrow_effect + borrow_effect,
    );
}

@external
func get_account_liquidity{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    address: felt, token_modify: felt, redeem_tokens: felt, borrow_amount: felt
) -> (liquidity: felt, shortfall: felt) {
    alloc_locals;
    let (account_assets_len) = account_assets_length.read(address);

    let (sum_collateral, sum_borrow_effect) = _get_account_liquidity(
        address, token_modify, redeem_tokens, borrow_amount, account_assets_len, 0, 0, 0
    );

    let diff = sum_collateral - sum_borrow_effect;
    let cmp = is_nn(diff);

    if (cmp == 0) {
        return (diff, 0);
    } else {
        return (0, sum_borrow_effect - sum_collateral);
    }
}

@external
func mint_allowed{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    token: felt, address: felt, mint_amount: felt
) -> (err: felt) {
    alloc_locals;

    let (is_listed) = markets_is_listed.read(token);

    if (is_listed == 0) {
        return (1,);
    }

    // Add the reward part as COMP here

    return (0,);
}

func _borrow_allowed{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    token: felt, borrower: felt, borrow_amount: felt
) -> (err: felt) {
    alloc_locals;

    let (b_caps) = borrow_caps.read(token);
    let (total_token_borrow) = total_borrows_re.read(token);
    let next_total_borrow = total_token_borrow + borrow_amount;
    let diff = next_total_borrow - b_caps;
    let cmp = is_nn(diff);

    if (cmp == 0) {
        return (1,);
    }

    let (liquidity, shortfall) = get_account_liquidity(borrower, token, 0, borrow_amount);

    let cmp1 = is_nn(shortfall);

    if (cmp1 == 0) {
        return (1,);
    }

    // Add the reward part as COMP here

    return (0,);
}

@external
func borrow_allowed{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    token: felt, borrower: felt, borrow_amount: felt
) -> (err: felt) {
    alloc_locals;

    let (is_listed) = markets_is_listed.read(token);

    if (is_listed == 0) {
        return (1,);
    }

    let (is_member) = markets_account_mmebership.read(token, borrower);
    let (caller) = get_caller_address();

    if (is_member == 0) {
        let (_err) = _add_to_market_internal(caller, borrower);

        if (_err != 0) {
            return (_err,);
        }

        return _borrow_allowed(token, borrower, borrow_amount);
    }

    return _borrow_allowed(token, borrower, borrow_amount);
}

func _redeem_allowed{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    token: felt, redeemer: felt, redeem_tokens: felt
) -> (err: felt) {
    alloc_locals;

    let (is_listed) = markets_is_listed.read(token);

    if (is_listed == 0) {
        return (1,);
    }

    let (is_member) = markets_account_mmebership.read(token, redeemer);

    if (is_member == 0) {
        return (1,);
    }

    let (liquidity, shortfall) = get_account_liquidity(redeemer, token, redeem_tokens, 0);
    let cmp = is_nn(shortfall);

    if (cmp == 0) {
        return (1,);
    }

    return (0,);
}

@external
func redeem_allowed{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    token: felt, redeemer: felt, redeem_tokens: felt
) -> (err: felt) {
    alloc_locals;

    let (_err) = _redeem_allowed(token, redeemer, redeem_tokens);

    if (_err != 0) {
        return (_err,);
    }

    // update COMP here
    return (0,);
}

@external
func liquidate_borrow_allowed{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    token_borrow: felt,
    token_collateral: felt,
    liquidator: felt,
    borrower: felt,
    repay_amount: Uint256,
) -> (err: felt) {
    alloc_locals;

    let (is_listed_token_borrow) = markets_is_listed.read(token_borrow);

    if (is_listed_token_borrow == 0) {
        return (1,);
    }

    let (is_listed_token_collateral) = markets_is_listed.read(token_collateral);

    if (is_listed_token_collateral == 0) {
        return (1,);
    }

    let (borrow_bal) = ICToken.borrow_balance_stored(token_borrow, borrower);

    let (liquidity, shortfall) = get_account_liquidity(borrower, 0, 0, 0);

    if (shortfall == 0) {
        return (1,);
    }

    let (close_f) = close_factor.read();
    let (max_close) = SafeUint256.mul(close_f, borrow_bal);

    let (diff) = SafeUint256.sub_le(repay_amount, max_close);

    let (diff_felt) = uint256_to_address_felt(diff);

    let cmp = is_nn(diff_felt);

    if (cmp == 0) {
        return (1,);
    }

    return (0,);
}

@external
func seize_allowed{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    token_collateral: felt,
    token_borrow: felt,
    liquidator: felt,
    borrower: felt,
    seize_tokens: Uint256,
) -> (err: felt) {
    alloc_locals;

    let (is_listed_token_borrow) = markets_is_listed.read(token_borrow);

    if (is_listed_token_borrow == 0) {
        return (1,);
    }

    let (is_listed_token_collateral) = markets_is_listed.read(token_collateral);

    if (is_listed_token_collateral == 0) {
        return (1,);
    }

    // @todo put comptroller check :thinking
    return (0,);
}

@external
func repay_borrow_allowed{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    token_borrow: felt, payer: felt, borrower: felt, repay_amount: Uint256
) -> (err: felt) {
    alloc_locals;

    let (is_listed_token_borrow) = markets_is_listed.read(token_borrow);

    if (is_listed_token_borrow == 0) {
        return (1,);
    }

    return (0,);
}

@external
func liquidate_calculate_seize_tokens{
    syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr
}(account: felt, token_borrow: felt, token_collateral: felt, repay_amount: Uint256) -> (
    err: felt, seize_token: Uint256
) {
    alloc_locals;

    // move these two to oracle
    let (price_borrow) = ICToken.get_oracle_price(token_borrow);
    let (price_collateral) = ICToken.get_oracle_price(token_collateral);

    if (price_borrow == 0) {
        if (price_collateral == 0) {
            return (0, Uint256(0, 0));
        }
    }

    // Implement the calculation with oracle

    return (0, Uint256(0, 0));
}

@view
func _support_market{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}(
    token: felt
) -> (error: Uint256) {
    alloc_locals;

    markets_is_listed.write(token, 1);
    markets_collateral_factor.write(token, 0);
    markets_is_comped.write(token, 0);
    let v = Uint256(low=0, high=0);

    // @todo What is initialize market
    return (v,);
}
