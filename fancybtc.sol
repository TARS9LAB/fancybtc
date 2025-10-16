/**
 *Submitted for verification at BscScan.com on 2025-09-08
*/

// SPDX-License-Identifier: MIT
// File: @openzeppelin/contracts/utils/ReentrancyGuard.sol


// OpenZeppelin Contracts (last updated v5.1.0) (utils/ReentrancyGuard.sol)

pragma solidity ^0.8.20;

/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If EIP-1153 (transient storage) is available on the chain you're deploying at,
 * consider using {ReentrancyGuardTransient} instead.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant NOT_ENTERED = 1;
    uint256 private constant ENTERED = 2;

    uint256 private _status;

    /**
     * @dev Unauthorized reentrant call.
     */
    error ReentrancyGuardReentrantCall();

    constructor() {
        _status = NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        _nonReentrantBefore();
        _;
        _nonReentrantAfter();
    }

    function _nonReentrantBefore() private {
        // On the first call to nonReentrant, _status will be NOT_ENTERED
        if (_status == ENTERED) {
            revert ReentrancyGuardReentrantCall();
        }

        // Any calls to nonReentrant after this point will fail
        _status = ENTERED;
    }

    function _nonReentrantAfter() private {
        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = NOT_ENTERED;
    }

    /**
     * @dev Returns true if the reentrancy guard is currently set to "entered", which indicates there is a
     * `nonReentrant` function in the call stack.
     */
    function _reentrancyGuardEntered() internal view returns (bool) {
        return _status == ENTERED;
    }
}

// File: @openzeppelin/contracts/utils/Context.sol


// OpenZeppelin Contracts (last updated v5.0.1) (utils/Context.sol)

pragma solidity ^0.8.20;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}

// File: @openzeppelin/contracts/utils/Pausable.sol


// OpenZeppelin Contracts (last updated v5.3.0) (utils/Pausable.sol)

pragma solidity ^0.8.20;


/**
 * @dev Contract module which allows children to implement an emergency stop
 * mechanism that can be triggered by an authorized account.
 *
 * This module is used through inheritance. It will make available the
 * modifiers `whenNotPaused` and `whenPaused`, which can be applied to
 * the functions of your contract. Note that they will not be pausable by
 * simply including this module, only once the modifiers are put in place.
 */
abstract contract Pausable is Context {
    bool private _paused;

    /**
     * @dev Emitted when the pause is triggered by `account`.
     */
    event Paused(address account);

    /**
     * @dev Emitted when the pause is lifted by `account`.
     */
    event Unpaused(address account);

    /**
     * @dev The operation failed because the contract is paused.
     */
    error EnforcedPause();

    /**
     * @dev The operation failed because the contract is not paused.
     */
    error ExpectedPause();

    /**
     * @dev Modifier to make a function callable only when the contract is not paused.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    modifier whenNotPaused() {
        _requireNotPaused();
        _;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is paused.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    modifier whenPaused() {
        _requirePaused();
        _;
    }

    /**
     * @dev Returns true if the contract is paused, and false otherwise.
     */
    function paused() public view virtual returns (bool) {
        return _paused;
    }

    /**
     * @dev Throws if the contract is paused.
     */
    function _requireNotPaused() internal view virtual {
        if (paused()) {
            revert EnforcedPause();
        }
    }

    /**
     * @dev Throws if the contract is not paused.
     */
    function _requirePaused() internal view virtual {
        if (!paused()) {
            revert ExpectedPause();
        }
    }

    /**
     * @dev Triggers stopped state.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    function _pause() internal virtual whenNotPaused {
        _paused = true;
        emit Paused(_msgSender());
    }

    /**
     * @dev Returns to normal state.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    function _unpause() internal virtual whenPaused {
        _paused = false;
        emit Unpaused(_msgSender());
    }
}

// File: @openzeppelin/contracts/access/Ownable.sol


// OpenZeppelin Contracts (last updated v5.0.0) (access/Ownable.sol)

pragma solidity ^0.8.20;


/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * The initial owner is set to the address provided by the deployer. This can
 * later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    /**
     * @dev The caller account is not authorized to perform an operation.
     */
    error OwnableUnauthorizedAccount(address account);

    /**
     * @dev The owner is not a valid owner account. (eg. `address(0)`)
     */
    error OwnableInvalidOwner(address owner);

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the address provided by the deployer as the initial owner.
     */
    constructor(address initialOwner) {
        if (initialOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(initialOwner);
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        if (owner() != _msgSender()) {
            revert OwnableUnauthorizedAccount(_msgSender());
        }
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        if (newOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

// File: @openzeppelin/contracts/token/ERC20/IERC20.sol


// OpenZeppelin Contracts (last updated v5.4.0) (token/ERC20/IERC20.sol)

pragma solidity >=0.4.16;

/**
 * @dev Interface of the ERC-20 standard as defined in the ERC.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the value of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the value of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves a `value` amount of tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 value) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
     * caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 value) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from `from` to `to` using the
     * allowance mechanism. `value` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address from, address to, uint256 value) external returns (bool);
}

// File: @openzeppelin/contracts/interfaces/IERC20.sol


// OpenZeppelin Contracts (last updated v5.4.0) (interfaces/IERC20.sol)

pragma solidity >=0.4.16;


// File: @openzeppelin/contracts/utils/introspection/IERC165.sol


// OpenZeppelin Contracts (last updated v5.4.0) (utils/introspection/IERC165.sol)

pragma solidity >=0.4.16;

/**
 * @dev Interface of the ERC-165 standard, as defined in the
 * https://eips.ethereum.org/EIPS/eip-165[ERC].
 *
 * Implementers can declare support of contract interfaces, which can then be
 * queried by others ({ERC165Checker}).
 *
 * For an implementation, see {ERC165}.
 */
interface IERC165 {
    /**
     * @dev Returns true if this contract implements the interface defined by
     * `interfaceId`. See the corresponding
     * https://eips.ethereum.org/EIPS/eip-165#how-interfaces-are-identified[ERC section]
     * to learn more about how these ids are created.
     *
     * This function call must use less than 30 000 gas.
     */
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

// File: @openzeppelin/contracts/interfaces/IERC165.sol


// OpenZeppelin Contracts (last updated v5.4.0) (interfaces/IERC165.sol)

pragma solidity >=0.4.16;


// File: @openzeppelin/contracts/interfaces/IERC1363.sol


// OpenZeppelin Contracts (last updated v5.4.0) (interfaces/IERC1363.sol)

pragma solidity >=0.6.2;



/**
 * @title IERC1363
 * @dev Interface of the ERC-1363 standard as defined in the https://eips.ethereum.org/EIPS/eip-1363[ERC-1363].
 *
 * Defines an extension interface for ERC-20 tokens that supports executing code on a recipient contract
 * after `transfer` or `transferFrom`, or code on a spender contract after `approve`, in a single transaction.
 */
interface IERC1363 is IERC20, IERC165 {
    /*
     * Note: the ERC-165 identifier for this interface is 0xb0202a11.
     * 0xb0202a11 ===
     *   bytes4(keccak256('transferAndCall(address,uint256)')) ^
     *   bytes4(keccak256('transferAndCall(address,uint256,bytes)')) ^
     *   bytes4(keccak256('transferFromAndCall(address,address,uint256)')) ^
     *   bytes4(keccak256('transferFromAndCall(address,address,uint256,bytes)')) ^
     *   bytes4(keccak256('approveAndCall(address,uint256)')) ^
     *   bytes4(keccak256('approveAndCall(address,uint256,bytes)'))
     */

    /**
     * @dev Moves a `value` amount of tokens from the caller's account to `to`
     * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
     * @param to The address which you want to transfer to.
     * @param value The amount of tokens to be transferred.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function transferAndCall(address to, uint256 value) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from the caller's account to `to`
     * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
     * @param to The address which you want to transfer to.
     * @param value The amount of tokens to be transferred.
     * @param data Additional data with no specified format, sent in call to `to`.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function transferAndCall(address to, uint256 value, bytes calldata data) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from `from` to `to` using the allowance mechanism
     * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
     * @param from The address which you want to send tokens from.
     * @param to The address which you want to transfer to.
     * @param value The amount of tokens to be transferred.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function transferFromAndCall(address from, address to, uint256 value) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from `from` to `to` using the allowance mechanism
     * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
     * @param from The address which you want to send tokens from.
     * @param to The address which you want to transfer to.
     * @param value The amount of tokens to be transferred.
     * @param data Additional data with no specified format, sent in call to `to`.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function transferFromAndCall(address from, address to, uint256 value, bytes calldata data) external returns (bool);

    /**
     * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
     * caller's tokens and then calls {IERC1363Spender-onApprovalReceived} on `spender`.
     * @param spender The address which will spend the funds.
     * @param value The amount of tokens to be spent.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function approveAndCall(address spender, uint256 value) external returns (bool);

    /**
     * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
     * caller's tokens and then calls {IERC1363Spender-onApprovalReceived} on `spender`.
     * @param spender The address which will spend the funds.
     * @param value The amount of tokens to be spent.
     * @param data Additional data with no specified format, sent in call to `spender`.
     * @return A boolean value indicating whether the operation succeeded unless throwing.
     */
    function approveAndCall(address spender, uint256 value, bytes calldata data) external returns (bool);
}

// File: @openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol


// OpenZeppelin Contracts (last updated v5.3.0) (token/ERC20/utils/SafeERC20.sol)

pragma solidity ^0.8.20;



/**
 * @title SafeERC20
 * @dev Wrappers around ERC-20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    /**
     * @dev An operation with an ERC-20 token failed.
     */
    error SafeERC20FailedOperation(address token);

    /**
     * @dev Indicates a failed `decreaseAllowance` request.
     */
    error SafeERC20FailedDecreaseAllowance(address spender, uint256 currentAllowance, uint256 requestedDecrease);

    /**
     * @dev Transfer `value` amount of `token` from the calling contract to `to`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeCall(token.transfer, (to, value)));
    }

    /**
     * @dev Transfer `value` amount of `token` from `from` to `to`, spending the approval given by `from` to the
     * calling contract. If `token` returns no value, non-reverting calls are assumed to be successful.
     */
    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeCall(token.transferFrom, (from, to, value)));
    }

    /**
     * @dev Variant of {safeTransfer} that returns a bool instead of reverting if the operation is not successful.
     */
    function trySafeTransfer(IERC20 token, address to, uint256 value) internal returns (bool) {
        return _callOptionalReturnBool(token, abi.encodeCall(token.transfer, (to, value)));
    }

    /**
     * @dev Variant of {safeTransferFrom} that returns a bool instead of reverting if the operation is not successful.
     */
    function trySafeTransferFrom(IERC20 token, address from, address to, uint256 value) internal returns (bool) {
        return _callOptionalReturnBool(token, abi.encodeCall(token.transferFrom, (from, to, value)));
    }

    /**
     * @dev Increase the calling contract's allowance toward `spender` by `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     *
     * IMPORTANT: If the token implements ERC-7674 (ERC-20 with temporary allowance), and if the "client"
     * smart contract uses ERC-7674 to set temporary allowances, then the "client" smart contract should avoid using
     * this function. Performing a {safeIncreaseAllowance} or {safeDecreaseAllowance} operation on a token contract
     * that has a non-zero temporary allowance (for that particular owner-spender) will result in unexpected behavior.
     */
    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 oldAllowance = token.allowance(address(this), spender);
        forceApprove(token, spender, oldAllowance + value);
    }

    /**
     * @dev Decrease the calling contract's allowance toward `spender` by `requestedDecrease`. If `token` returns no
     * value, non-reverting calls are assumed to be successful.
     *
     * IMPORTANT: If the token implements ERC-7674 (ERC-20 with temporary allowance), and if the "client"
     * smart contract uses ERC-7674 to set temporary allowances, then the "client" smart contract should avoid using
     * this function. Performing a {safeIncreaseAllowance} or {safeDecreaseAllowance} operation on a token contract
     * that has a non-zero temporary allowance (for that particular owner-spender) will result in unexpected behavior.
     */
    function safeDecreaseAllowance(IERC20 token, address spender, uint256 requestedDecrease) internal {
        unchecked {
            uint256 currentAllowance = token.allowance(address(this), spender);
            if (currentAllowance < requestedDecrease) {
                revert SafeERC20FailedDecreaseAllowance(spender, currentAllowance, requestedDecrease);
            }
            forceApprove(token, spender, currentAllowance - requestedDecrease);
        }
    }

    /**
     * @dev Set the calling contract's allowance toward `spender` to `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful. Meant to be used with tokens that require the approval
     * to be set to zero before setting it to a non-zero value, such as USDT.
     *
     * NOTE: If the token implements ERC-7674, this function will not modify any temporary allowance. This function
     * only sets the "standard" allowance. Any temporary allowance will remain active, in addition to the value being
     * set here.
     */
    function forceApprove(IERC20 token, address spender, uint256 value) internal {
        bytes memory approvalCall = abi.encodeCall(token.approve, (spender, value));

        if (!_callOptionalReturnBool(token, approvalCall)) {
            _callOptionalReturn(token, abi.encodeCall(token.approve, (spender, 0)));
            _callOptionalReturn(token, approvalCall);
        }
    }

    /**
     * @dev Performs an {ERC1363} transferAndCall, with a fallback to the simple {ERC20} transfer if the target has no
     * code. This can be used to implement an {ERC721}-like safe transfer that rely on {ERC1363} checks when
     * targeting contracts.
     *
     * Reverts if the returned value is other than `true`.
     */
    function transferAndCallRelaxed(IERC1363 token, address to, uint256 value, bytes memory data) internal {
        if (to.code.length == 0) {
            safeTransfer(token, to, value);
        } else if (!token.transferAndCall(to, value, data)) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Performs an {ERC1363} transferFromAndCall, with a fallback to the simple {ERC20} transferFrom if the target
     * has no code. This can be used to implement an {ERC721}-like safe transfer that rely on {ERC1363} checks when
     * targeting contracts.
     *
     * Reverts if the returned value is other than `true`.
     */
    function transferFromAndCallRelaxed(
        IERC1363 token,
        address from,
        address to,
        uint256 value,
        bytes memory data
    ) internal {
        if (to.code.length == 0) {
            safeTransferFrom(token, from, to, value);
        } else if (!token.transferFromAndCall(from, to, value, data)) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Performs an {ERC1363} approveAndCall, with a fallback to the simple {ERC20} approve if the target has no
     * code. This can be used to implement an {ERC721}-like safe transfer that rely on {ERC1363} checks when
     * targeting contracts.
     *
     * NOTE: When the recipient address (`to`) has no code (i.e. is an EOA), this function behaves as {forceApprove}.
     * Opposedly, when the recipient address (`to`) has code, this function only attempts to call {ERC1363-approveAndCall}
     * once without retrying, and relies on the returned value to be true.
     *
     * Reverts if the returned value is other than `true`.
     */
    function approveAndCallRelaxed(IERC1363 token, address to, uint256 value, bytes memory data) internal {
        if (to.code.length == 0) {
            forceApprove(token, to, value);
        } else if (!token.approveAndCall(to, value, data)) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     *
     * This is a variant of {_callOptionalReturnBool} that reverts if call fails to meet the requirements.
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        uint256 returnSize;
        uint256 returnValue;
        assembly ("memory-safe") {
            let success := call(gas(), token, 0, add(data, 0x20), mload(data), 0, 0x20)
            // bubble errors
            if iszero(success) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0, returndatasize())
                revert(ptr, returndatasize())
            }
            returnSize := returndatasize()
            returnValue := mload(0)
        }

        if (returnSize == 0 ? address(token).code.length == 0 : returnValue != 1) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     *
     * This is a variant of {_callOptionalReturn} that silently catches all reverts and returns a bool instead.
     */
    function _callOptionalReturnBool(IERC20 token, bytes memory data) private returns (bool) {
        bool success;
        uint256 returnSize;
        uint256 returnValue;
        assembly ("memory-safe") {
            success := call(gas(), token, 0, add(data, 0x20), mload(data), 0, 0x20)
            returnSize := returndatasize()
            returnValue := mload(0)
        }
        return success && (returnSize == 0 ? address(token).code.length > 0 : returnValue == 1);
    }
}

// File: @openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol


// OpenZeppelin Contracts (last updated v5.4.0) (token/ERC20/extensions/IERC20Metadata.sol)

pragma solidity >=0.6.2;


/**
 * @dev Interface for the optional metadata functions from the ERC-20 standard.
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}


pragma solidity ^0.8.30;

	// ============ Chainlink ============
	// ============ 预言机接口（Chainlink V3 Aggregator） ============
	interface AggregatorV3Interface {
		function latestRoundData() external view returns (
			uint80, int256, uint256, uint256, uint80
		);
		function decimals() external view returns (uint8);
	}

	// ============ Pancake V3 Router 接口 ============
	interface IPancakeV3Router {
		// 单路径兑换参数结构体
		struct ExactInputSingleParams {
			address tokenIn;             // 输入代币
			address tokenOut;            // 输出代币
			uint24 fee;                  // 手续费档位（100/500/2500/10000）
			address recipient;           // 接收人地址
			uint256 deadline;            // 交易截止时间
			uint256 amountIn;            // 输入金额
			uint256 amountOutMinimum;    // 最少输出金额（防滑点保护）
			uint160 sqrtPriceLimitX96;   // 价格限制（一般填 0 表示无）
		}
		function exactInputSingle(ExactInputSingleParams calldata params)
			external
			payable
			returns (uint256 amountOut); // 返回实际换出的 token 数量
	}

	// ============ Pancake V3 QuoterV2 接口 ============
	// 用于链下/链上预估某笔交易大概能换多少
	interface IPancakeQuoterV2 {
		struct QuoteExactInputSingleParams {
			address tokenIn;             // 输入代币
			address tokenOut;            // 输出代币
			uint256 amountIn;            // 输入金额
			uint24  fee;                 // 手续费档位
			uint160 sqrtPriceLimitX96;   // 价格限制
		}
		function quoteExactInputSingle(
			QuoteExactInputSingleParams calldata params
		)
			external
			returns (
				uint256 amountOut,       // 预估输出
				uint160 sqrtPriceX96After,
				uint32  initializedTicksCrossed,
				uint256 gasEstimate      // gas 估算
			);
	}

	// ============ 主合约：FancyBTC_CommitmentVault ============
	contract FancyBTC_CommitmentVault is Ownable, Pausable, ReentrancyGuard {
		using SafeERC20 for IERC20Metadata;

		// ------- 核心依赖 -------
		IERC20Metadata public immutable USDT;     // USDT 合约
		IERC20Metadata public immutable BTCB;     // BTCB 合约
		IPancakeV3Router public immutable router; // Pancake V3 路由器
		IPancakeQuoterV2 public immutable quoter; // Pancake V3 报价器
		AggregatorV3Interface public immutable priceFeed; // Chainlink 预言机

		// ------- 费用参数（1e18 = 100%） -------
		uint256 public managementFeeRate;   // 管理费率（年化百分比）
		uint256 public performanceFeeRate;  // 业绩报酬费率
		uint256 public annualThreshold;     // 年化业绩费门槛
		uint256 public feeCapBps;           // 总费用上限（以 BPS 表示）
		uint256 public minDepositUSDT;      // 最小存入金额

		// ------- 总份额 -------
		uint256 public totalShares;         // 系统内总的份额（类似基金份额）

		// ------- 预言机保护参数 -------
		bool    public oracleGuardEnabled = true;         // 是否启用预言机保护
		uint256 public oracleStaleAfter   = 10 minutes;   // 预言机数据过期时间
		uint256 public oracleMaxDeviationBps = 100;       // 最大允许偏差（BPS，100=1%）

		// ------- 存款批次结构 -------
		struct Lot {
			uint256 shares;      // 份额
			uint256 principal;   // 本金（USDT）
			uint256 depositTime; // 存款时间戳
		}
		mapping(bytes32 => Lot) public lotByCommitment; // commitment → 存款信息

		// ------- 事件 -------
		event DepositCommitment(
			bytes32 indexed commitment, // 存款批次 ID
			uint256 usdtIn,             // 存入的 USDT 金额
			uint256 sharesMinted        // 铸造的份额
		);

		event WithdrawCommitment(
			bytes32 indexed commitment,
			address indexed recipient,
			uint256 sharesRedeemed,     // 赎回的份额
			uint256 usdtGross,          // 毛额 USDT
			uint256 mgmtFee,            // 管理费
			uint256 perfFee,            // 业绩费
			uint256 usdtNet             // 实际到账 USDT
		);

		event WithdrawPartialCommitment(
			bytes32 indexed commitment,
			address indexed recipient,
			uint256 sharesRedeemed,     // 部分赎回份额
			uint256 usdtGross,
			uint256 mgmtFee,
			uint256 perfFee,
			uint256 usdtNet
		);

		event AllParamsUpdated(
			uint256 mgmt, uint256 perf, uint256 threshold, uint256 capBps, uint256 minDepositUSDT
		);

		event OracleGuardUpdated(
			bool enabled, uint256 staleAfter, uint256 maxDeviationBps
		);

		// ------- 构造函数 -------
		constructor(
			address _usdt,       // USDT 合约地址
			address _btcb,       // BTCB 合约地址
			address _router,     // Pancake V3 Router 地址
			address _quoter,     // Pancake V3 Quoter 地址
			address _priceFeed,  // Chainlink 价格预言机地址
			address initialOwner // 初始合约拥有者
		) Ownable(initialOwner) {
			// 参数有效性检查
			require(
				_usdt != address(0) && 
				_btcb != address(0) && 
				_router != address(0) && 
				_quoter != address(0) && 
				_priceFeed != address(0), 
				"zero"
			);

			// 设置依赖
			USDT = IERC20Metadata(_usdt);
			BTCB = IERC20Metadata(_btcb);
			router = IPancakeV3Router(_router);
			quoter = IPancakeQuoterV2(_quoter);
			priceFeed = AggregatorV3Interface(_priceFeed);

			// 检查代币小数位必须是 18（便于统一处理）
			require(USDT.decimals() == 18, "USDT decimals != 18");
			require(BTCB.decimals() == 18, "BTCB decimals != 18");

			// 初始化默认参数
			managementFeeRate  = 1e16;   // 管理费率 = 1%（1e16 / 1e18）
			performanceFeeRate = 20e16;  // 业绩费率 = 20%
			annualThreshold    = 10e16;  // 年化门槛 = 10%
			feeCapBps          = 3000;   // 总费用上限 = 30%（3000/10000）
			minDepositUSDT     = (10 ** USDT.decimals()) / 10; // 最小存款 = 0.1 USDT
		}	
	

		// ========================
		// ====== 存入 ============
		// ========================
		function depositWithCommitment(
			uint256 amountUSDT,   // 存款的 USDT 数量
			bytes32 commitment,   // 唯一的存款承诺值（防止伪造和重复使用）
			uint256 slippageBps,  // 用户可容忍的滑点（基点，1%=100）
			uint24 poolFee        // Pancake V3 交易池费率（100/500/2500/10000）
		)
			external
			whenNotPaused         // 合约未暂停时才允许执行
			nonReentrant          // 防止重入攻击
		{
			// ---- 基础校验 ----
			require(amountUSDT >= minDepositUSDT, "amount<minDeposit");  // 金额必须大于最小存款限制
			require(slippageBps <= 200, "slippage>2%");                  // 最大滑点限制为 2%
			require(
				poolFee == 100 || poolFee == 500 || poolFee == 2500 || poolFee == 10000,
				"invalid poolFee"
			);                                                           // 只允许 Pancake V3 的合法费档
			require(lotByCommitment[commitment].depositTime == 0, "commitment used"); 
			// commitment 必须未被使用过，避免重复存入

			// ---- 存款前状态记录 ----
			uint256 fundValueBefore   = getFundValue();   // 记录存入前基金净值（USDT估算）
			uint256 totalSharesBefore = totalShares;      // 记录存入前的总份额数

			// ---- 转账 USDT ----
			uint256 usdtBefore = USDT.balanceOf(address(this));                   // 存款前合约 USDT 余额
			USDT.safeTransferFrom(msg.sender, address(this), amountUSDT);         // 从用户转入 USDT
			uint256 received = USDT.balanceOf(address(this)) - usdtBefore;        // 实际到账金额
			require(received == amountUSDT, "USDT fee-on-transfer not supported");
			// 要求实际到账金额和用户输入一致（不支持带手续费的代币）

			// ---- 向 Pancake Quoter 查询报价 ----
			IPancakeQuoterV2.QuoteExactInputSingleParams memory qparams =
				IPancakeQuoterV2.QuoteExactInputSingleParams({
					tokenIn: address(USDT),      // 输入 USDT
					tokenOut: address(BTCB),     // 兑换 BTCB
					amountIn: amountUSDT,        // 兑换数量
					fee:      poolFee,           // 费档
					sqrtPriceLimitX96: 0         // 不设价格限制
				});

			uint256 quoted;
			try quoter.quoteExactInputSingle(qparams)
				returns (uint256 amountOut, uint160, uint32, uint256)
			{
				quoted = amountOut;              // 预估可兑换的 BTCB 数量
			} catch {
				revert("QuoterV2 failed");       // 如果 Quoter 调用失败则回滚
			}
			require(quoted > 0, "quote=0");      // 报价必须大于 0

			// ---- 计算最小可接受 BTCB 数量 ----
			uint256 minBtcOut = (quoted * (10_000 - slippageBps)) / 10_000; 
			// 按照滑点限制计算最小可接受的 BTCB
			if (oracleGuardEnabled) {
				uint256 floorByOracle = _oracleMinBtcOutForUsdt(amountUSDT); 
				require(minBtcOut >= floorByOracle, "minOut < oracle floor");
				// 如果开启预言机保护，要求 minOut 不低于预言机估值
			}

			// ---- 确保路由器有足够的 USDT 授权 ----
			_ensureAllowance(USDT, address(router), amountUSDT);

			// ---- 执行实际兑换（USDT → BTCB）----
			IPancakeV3Router.ExactInputSingleParams memory params =
				IPancakeV3Router.ExactInputSingleParams({
					tokenIn: address(USDT),      // 输入代币
					tokenOut: address(BTCB),     // 输出代币
					fee: poolFee,                // 费档
					recipient: address(this),    // 收款方为合约自身
					deadline: block.timestamp + 300, // 交易有效期（5分钟）
					amountIn: amountUSDT,        // 输入 USDT 数量
					amountOutMinimum: minBtcOut, // 最小可接受输出（防止滑点）
					sqrtPriceLimitX96: 0         // 不设价格限制
				});

			uint256 btcbOut = router.exactInputSingle(params);   // 实际兑换得到的 BTCB 数量
			require(btcbOut >= minBtcOut, "slippage");           // 校验滑点不超标

			if (oracleGuardEnabled) {
				uint256 floorAgain = _oracleMinBtcOutForUsdt(amountUSDT);
				require(btcbOut >= floorAgain, "actual < oracle floor");  
				// 再次校验实际结果不低于预言机下限
			}

			// ---- 计算新铸造的份额 ----
			uint256 sharesMinted = (totalSharesBefore == 0)
				? amountUSDT                               // 如果是首笔存入，份额=金额
				: (amountUSDT * totalSharesBefore) / fundValueBefore;
				// 否则按照比例计算：新金额 / 基金净值 * 总份额

			// ---- 记录本次存入的批次信息 ----
			lotByCommitment[commitment] = Lot({
				shares:      sharesMinted,     // 新增份额
				principal:   amountUSDT,       // 存入本金
				depositTime: block.timestamp   // 存入时间
			});
			totalShares = totalSharesBefore + sharesMinted;  // 更新全局总份额

			// ---- 事件日志 ----
			emit DepositCommitment(commitment, amountUSDT, sharesMinted);
		}

		// ========================
		// ===== 全额赎回 =========
		// ========================
		function withdrawCommitment(
			bytes32 depositId,       // 存款批次ID（用户入金时生成）
			bytes32 secret,          // 用户密钥（防伪造）
			address recipient,       // 赎回资金接收人
			uint256 slippageBps,     // 滑点容忍度（基点，100=1%）
			uint24 poolFee           // Pancake V3 交易池费率（100/500/2500/10000）
		) external whenNotPaused nonReentrant {
			require(recipient != address(0), "recipient=0");          // 接收人不能为空
			require(slippageBps <= 200, "slippage>2%");               // 最大滑点限制为2%
			require(
				poolFee == 100 || poolFee == 500 || poolFee == 2500 || poolFee == 10000,
				"invalid poolFee"                                    // 检查费率是否合法
			);

			// commitment = depositId + secret 的哈希值，用于唯一标识存款批次
			bytes32 commitment = keccak256(abi.encodePacked(depositId, secret));
			Lot storage lotS = lotByCommitment[commitment];           // 取出对应存款批次
			require(lotS.depositTime != 0 && lotS.shares > 0, "this lots not found"); // 必须存在且有份额

			uint256 shares = lotS.shares;                             // 该存款批次的总份额
			uint256 fundValue = getFundValue();                       // 当前基金净值
			uint256 grossUSDT = (fundValue * shares) / totalShares;   // 按份额比例计算应得USDT（毛额）

			// ===== 逻辑：强制卖出 份额的BTCB =====
			uint256 btcBal = BTCB.balanceOf(address(this));
			require(btcBal > 0, "no BTCB");

			// 按份额比例，计算应卖出的 BTCB 数量
			uint256 btcToSell = (btcBal * shares) / totalShares;
			require(btcToSell > 0, "btcToSell=0");

			// 调用新函数，把 btcToSell 全部换成 USDT
			uint256 redeemed = _doSwapExactBtcForUsdt(btcToSell, slippageBps, poolFee);

			// 进入结算逻辑，会扣管理费、业绩费，并发起资金转账
			_settlePayout(commitment, recipient, shares, redeemed, lotS.principal, lotS.depositTime, true);
		}

		// ========================
		// ===== 部分赎回 =========
		// ========================
		function withdrawPartialCommitment(
			bytes32 depositId,       // 存款批次ID（用户入金时生成）
			bytes32 secret,          // 用户密钥（防伪造）
			address recipient,       // 赎回资金接收人
			uint256 sharesToRedeem,  // 本次要赎回的份额（不能超过该批次的剩余份额）
			uint256 slippageBps,     // 滑点容忍度（基点，100=1%）
			uint24 poolFee           // Pancake V3 交易池费率（100/500/2500/10000）
		) external whenNotPaused nonReentrant {
			require(recipient != address(0), "recipient=0");           // 接收人不能为空，防止资金打入黑洞
			require(sharesToRedeem > 0, "shares=0");                   // 必须赎回大于0的份额
			require(slippageBps <= 200, "slippage>2%");                // 最大滑点限制为2%（你的硬性底线）
			require(
				poolFee == 100 || poolFee == 500 || poolFee == 2500 || poolFee == 10000,
				"invalid poolFee"                                      // 检查池子费率是否合法
			);

			// 1) 定位本次赎回对应的 commitment（存款批次）
			bytes32 commitment = keccak256(abi.encodePacked(depositId, secret)); // commitment = depositId + secret 的哈希
			Lot storage lotS = lotByCommitment[commitment];           // 取出该存款批次
			require(lotS.depositTime != 0 && lotS.shares > 0, "not found");      // 批次必须存在且份额>0
			require(sharesToRedeem <= lotS.shares, "exceed lot shares");         // 不能超过该批次可赎回的份额

			// 2) 基于当前基金净值，计算“理论毛额”和“本金切片”
			//    注意：下面的 grossUSDT 为“理论值”，实际兑付按 swap 得到的 usdt 计（见第5步）
			uint256 fundValue = getFundValue();                                     // 全局基金净值（以USDT计）
			uint256 grossUSDT = (fundValue * sharesToRedeem) / totalShares;         // 理论应得USDT（毛额）
			uint256 principalSlice = (lotS.principal * sharesToRedeem) / lotS.shares; // 按赎回份额比例切分的本金

			// 3) 资产处置策略（核心变更点）：
			//    —— 不再“优先用库存USDT”，而是“按份额比例”卖出合约中持有的BTCB
			//    —— 这样可避免BTCB长期滞留在仓内，与全额赎回逻辑保持一致
			uint256 btcBal = BTCB.balanceOf(address(this));                          // 合约当前BTCB持仓
			require(btcBal > 0, "no BTCB");                                          // 若无BTCB则无法按比例卖出
			uint256 btcToSell = (btcBal * sharesToRedeem) / totalShares;             // 该笔部分赎回应承担卖出的BTCB数量（按全局份额占比计算）
			require(btcToSell > 0, "btcToSell=0");                                   // 防止因整数除法造成的零值（极小份额或btcBal过小）

			// 4) 执行卖出：将“本次应卖出的BTCB份额”全部换成USDT
			//    这里使用你新增的 _doSwapExactBtcForUsdt(btcAmount, slippageBps, poolFee)
			//    —— ExactInputSingle：输入固定BTCB数量，得到尽可能多的USDT，但必须 >= (Quoter-滑点)下限
			uint256 redeemed = _doSwapExactBtcForUsdt(btcToSell, slippageBps, poolFee); // 实际换到的USDT数量（作为“毛额”进入结算）

			// 5) 结算与转账：
			//    —— 费用计算以 “redeemed（实际换到的USDT）” 为基础，符合你“只接受<=2%滑点”的风险控制
			//    —— _settlePayout 内部会根据 isFull=false 更新该 commitment 的剩余份额与本金
			_settlePayout(
				commitment,
				recipient,
				sharesToRedeem,
				redeemed,          // 这里传入“实际换到的USDT”作为毛额参与扣费与结算
				principalSlice,     // 本次赎回对应的本金部分
				lotS.depositTime,
				false               // isFull = false，表示部分赎回
			);
		}

		/// @notice 按“当前剩余份额”的比例（BPS）进行部分赎回
		/// @dev percentBps ∈ (0, 10000)，10000=100%（想全额请走 withdrawCommitment）
		///      份额是动态的，这里显式以“当前剩余份额”为基准计算 sharesToRedeem
		function withdrawPartialByPercent(
			bytes32 depositId,
			bytes32 secret,
			address recipient,
			uint16  percentBps,   // 1 = 0.01%, 10000 = 100%
			uint256 slippageBps,
			uint24  poolFee
		) external whenNotPaused nonReentrant {
			require(recipient != address(0), "recipient=0");
			require(percentBps > 0 && percentBps < 10_000, "percent out of range");
			require(slippageBps <= 200, "slippage>2%");
			require(
				poolFee == 100 || poolFee == 500 || poolFee == 2500 || poolFee == 10000,
				"invalid poolFee"
			);

			// 1) 定位 commitment
			bytes32 commitment = keccak256(abi.encodePacked(depositId, secret));
			Lot storage lotS = lotByCommitment[commitment];
			require(lotS.depositTime != 0 && lotS.shares > 0, "not found");

			// 2) 由“当前剩余份额 * 比例(BPS)”得到赎回份额（向上取整，避免极小比例算成0）
			//    ceil(x*y/10000) = (x*y + 9999) / 10000
			uint256 sharesToRedeem = (lotS.shares * percentBps + 9_999) / 10_000;
			if (sharesToRedeem > lotS.shares) sharesToRedeem = lotS.shares; // 边界保护
			require(sharesToRedeem > 0, "shares=0");

			// 3) 计算理论毛额/本金切片（实际兑付按 swap 得到的 USDT）
			uint256 fundValue = getFundValue();
			uint256 grossUSDT = (fundValue * sharesToRedeem) / totalShares;
			uint256 principalSlice = (lotS.principal * sharesToRedeem) / lotS.shares;

			// 4) 按份额占比卖出 BTCB → USDT（与全额赎回保持一致）
			uint256 btcBal = BTCB.balanceOf(address(this));
			require(btcBal > 0, "no BTCB");
			uint256 btcToSell = (btcBal * sharesToRedeem) / totalShares;
			require(btcToSell > 0, "btcToSell=0");

			uint256 redeemed = _doSwapExactBtcForUsdt(btcToSell, slippageBps, poolFee);

			// 5) 结算（_settlePayout 内会减少 lotS.shares、lotS.principal）
			_settlePayout(
				commitment,
				recipient,
				sharesToRedeem,
				redeemed,        // 用实际成交的 USDT 作为毛额参与扣费
				principalSlice,
				lotS.depositTime,
				false
			);
		}

        /// @dev 执行一次精确输入的兑换操作：卖出指定数量的BTCB，换取USDT
        /// @param btcToSell 卖出的BTCB数量（单位：最小精度）
        /// @param slippageBps 用户允许的最大滑点（基点，100=1%）
        /// @param poolFee Pancake V3交易池费率（100/500/2500/10000）
        /// @return redeemedUSDT 实际兑换得到的USDT数量
        function _doSwapExactBtcForUsdt(
            uint256 btcToSell, // 卖出的BTCB数量
            uint256 slippageBps,
            uint24 poolFee
        ) internal returns (uint256 redeemedUSDT) {
            // ---- 基础安全校验 ----
            // 要求卖出数量不能过小，避免dust交易造成失败或浪费gas
            require(btcToSell >= 10 ** (BTCB.decimals() - 6), "amountIn too small"); 

            // ---- 使用 Quoter 模拟询价，预估兑换结果 ----
            IPancakeQuoterV2.QuoteExactInputSingleParams memory qparams =
                IPancakeQuoterV2.QuoteExactInputSingleParams({
                    tokenIn: address(BTCB),          // 输入代币：BTCB
                    tokenOut: address(USDT),         // 输出代币：USDT
                    amountIn: btcToSell,             // 卖出的BTCB数量
                    fee: poolFee,                    // 交易池费率
                    sqrtPriceLimitX96: 0             // 不设置价格限制
                });

            uint256 quoted;
            try quoter.quoteExactInputSingle(qparams)
                returns (uint256 amountOut, uint160, uint32, uint256)
            {
                quoted = amountOut;                  // 预估能兑换得到的USDT
            } catch {
                revert("Quoter failed for BTCB to USDT swap");
            }
            require(quoted > 0, "quote=0");          // 确保有有效报价

            // ---- 计算最小可接受USDT数量（滑点 + 预言机双重保护） ----
            // 按用户设置的最大滑点折扣，计算最低可接受输出
            uint256 minUsdtOut = (quoted * (10_000 - slippageBps)) / 10_000;

            if (oracleGuardEnabled) {
                // 基于预言机，计算相同输入btcToSell下应得到的最低USDT（带安全系数）
                uint256 floorByOracle = _oracleMinUsdtOutForBtc(btcToSell);
                if (floorByOracle > minUsdtOut) {
                    // 取预言机下限作为最终保护
                    minUsdtOut = floorByOracle;
                }
            }

            // ---- 授权路由合约使用BTCB ----
            _ensureAllowance(BTCB, address(router), btcToSell);

            // 构造实际swap参数
            IPancakeV3Router.ExactInputSingleParams memory params =
                IPancakeV3Router.ExactInputSingleParams({
                    tokenIn: address(BTCB),          // 输入：BTCB
                    tokenOut: address(USDT),         // 输出：USDT
                    fee: poolFee,                    // 使用的费率档位
                    recipient: address(this),        // 收款地址=当前合约
                    deadline: block.timestamp + 300, // 交易有效期=当前时间+5分钟
                    amountIn: btcToSell,             // 精确卖出的BTCB数量
                    amountOutMinimum: minUsdtOut,    // 防滑点保护：最少能得到的USDT
                    sqrtPriceLimitX96: 0             // 不设置价格限制
                });

            // ---- 执行实际swap ----
            uint256 swapOut = router.exactInputSingle(params);

            // 校验兑换结果满足最低要求
            require(swapOut >= minUsdtOut, "swap output below minimum due to slippage");

            return swapOut;

        }
	

		/// @dev 结算赎回时的费用与实际支付
		/// @param commitment 存款承诺ID（对应唯一一笔存款）
		/// @param recipient  赎回资金接收人
		/// @param sharesRedeemed 本次赎回的份额
		/// @param grossUSDT 本次赎回对应的总USDT（未扣费）
		/// @param principalSlice 本次赎回对应的本金部分
		/// @param depositTime 该笔存款的起始时间
		/// @param isFull 是否为全额赎回（true=全额，false=部分）
		//  当总费用超过上限时，管理费=上限（比如15%），业绩费为 0
		function _settlePayout(
			bytes32 commitment,
			address recipient,
			uint256 sharesRedeemed,
			uint256 grossUSDT,
			uint256 principalSlice,
			uint256 depositTime,
			bool isFull
		) internal {
			uint256 daysHeld = (block.timestamp - depositTime) / 1 days;        // 持有天数 = 当前时间 - 存款时间
			(uint256 mgmtFee, uint256 perfFee) = _calcFees(grossUSDT, principalSlice, daysHeld); // 根据规则计算管理费+业绩费

			uint256 feeCap = (grossUSDT * feeCapBps) / 10000;                   // 费用上限（按BPS基点计算）
			uint256 fees   = mgmtFee + perfFee;                                 // 总费用
			if (fees > feeCap && fees > 0) {                                    // 如果总费用超过上限
				mgmtFee = feeCap;                                               // 按照总费用上限=》管理费
				perfFee = 0;                                                    // 业绩费为0
			}
			require(grossUSDT >= mgmtFee + perfFee, "fees>gross");              // 确认扣除费用后不会为负数

			if (isFull) {
				totalShares -= sharesRedeemed;                                  // 全额赎回：减少总份额
				delete lotByCommitment[commitment];                             // 删除该存款记录
			} else {
				Lot storage lotS = lotByCommitment[commitment];                 // 部分赎回：更新该存款记录
				lotS.shares    -= sharesRedeemed;                               // 减少对应份额
				lotS.principal -= principalSlice;                               // 减少对应本金
				totalShares    -= sharesRedeemed;                               // 总份额也减少
			}

			uint256 payout = grossUSDT - mgmtFee - perfFee;                                // 实际支付给用户的金额 = 总额 - 各种费用
			if ( mgmtFee + perfFee > 0) USDT.safeTransfer(owner(), mgmtFee+perfFee);       // 管理费+业绩费转给合约所有者（基金管理方）
			USDT.safeTransfer(recipient, payout);                                          // 剩余资金支付给赎回人

			if (isFull) {
				emit WithdrawCommitment(commitment, recipient, sharesRedeemed, grossUSDT, mgmtFee, perfFee, payout); // 触发全额赎回事件
			} else {
				emit WithdrawPartialCommitment(commitment, recipient, sharesRedeemed, grossUSDT, mgmtFee, perfFee, payout); // 触发部分赎回事件
			}
		}

		// ==================================
		// ===== CHAINLINK Oracle 工具 ======
		// ==================================
		/// @dev 确保当前合约对某个spender的授权额度足够
		function _ensureAllowance(IERC20Metadata token, address spender, uint256 needed) internal {
			uint256 cur = token.allowance(address(this), spender);  // 查询本合约对spender的当前授权额度
			if (cur < needed) {                                     // 如果小于所需额度
				token.approve(spender, type(uint256).max);          // 则一次性授权最大值（避免重复approve）
			}
		}

		/// @dev 从预言机获取BTC价格
		/// @return price 价格数值（uint256）
		/// @return pdec  小数位精度（预言机的decimals）
		function getBTCPrice() public view returns (uint256 price, uint8 pdec) {
			(, int256 p,, uint256 updatedAt,) = priceFeed.latestRoundData(); // 调用Chainlink预言机获取最新价格与时间戳
			require(p > 0, "bad price");                                     // 确认价格大于0
			require(block.timestamp - updatedAt < oracleStaleAfter, "stale");// 确认价格没有过期（时间差小于阈值）
			return (uint256(p), priceFeed.decimals());                       // 返回价格与小数精度
		}

		/// @dev 给定BTC数量，计算根据预言机价格最少应得到的USDT数量
		/// @param btcAmount 输入的BTC数量
		/// @return 最少应得的USDT数量（已考虑偏差折扣）
		function _oracleMinUsdtOutForBtc(uint256 btcAmount) internal view returns (uint256) {
			(uint256 px, uint8 pdec) = getBTCPrice();                // 获取BTC价格与精度
			uint256 usdt = (btcAmount * px) / (10 ** pdec);          // 按价格计算BTC对应的USDT
			return (usdt * (10_000 - oracleMaxDeviationBps)) / 10_000; // 按允许的最大偏差打折，返回保守值
		}

		/// @dev 给定USDT数量，计算根据预言机价格最少应得到的BTC数量
		/// @param usdtAmount 输入的USDT数量
		/// @return 最少应得的BTC数量（已考虑偏差折扣）
		function _oracleMinBtcOutForUsdt(uint256 usdtAmount) internal view returns (uint256) {
			(uint256 px, uint8 pdec) = getBTCPrice();                // 获取BTC价格与精度
			uint256 btc = (usdtAmount * (10 ** pdec)) / px;          // 按价格计算USDT对应的BTC
			return (btc * (10_000 - oracleMaxDeviationBps)) / 10_000; // 按允许的最大偏差打折，返回保守值
		}

		/// @dev 给定所需USDT数量，反推出至少需要多少BTC才能满足（包含安全buffer）
		/// @param usdtNeed 所需的USDT数量
		/// @return est 所需的BTC数量（已放大，保证足够换到目标USDT）
		function _oracleBtcForUsdt(uint256 usdtNeed) internal view returns (uint256) {
			(uint256 px, uint8 pdec) = getBTCPrice();                // 获取BTC价格与精度
			uint256 est = (usdtNeed * (10 ** pdec)) / px;            // 计算对应的BTC需求
			return (est * 10_000) / (10_000 - oracleMaxDeviationBps); // 放大需求，确保能满足所需USDT
		}

		// ========================
		// ===== 费用计算 =========
		// ========================

		/**
		 * @notice 费用计算（严格顺序：先管理费 -> 后业绩费 -> 费用上限cap）
		 * @dev
		 *  1) 先按市值 cashSlice 计提管理费（与盈亏无关；按天计提/365）
		 *  2) 再以「扣除管理费后的市值」与本金 principalSlice 比较计算收益；
		 *     若扣完管理费后的收益 > 阈值收益（比如年化10%），则对“超出阈值的部分”收业绩费
		 *  3) 最后将管理费+业绩费整体受 feeCapBps 的上限约束（按比例缩减）
		 *
		 * @param cashSlice      本次计算对应的资产“当前市值”（未扣费）
		 * @param principalSlice 本次计算对应的“本金份额”
		 * @param daysHeld       该资金片段持有天数（建议外层用 (now - depositTime)/1 days 计算）
		 * @return mgmtFee       管理费
		 * @return perfFee       业绩费（按“扣管费后”的超额收益计算）
		 */
		function _calcFees(
			uint256 cashSlice,
			uint256 principalSlice,
			uint256 daysHeld
		) internal view returns (uint256 mgmtFee, uint256 perfFee) {
			// ====== 快速返回与防御性判断 ======
			if (cashSlice == 0) {
				return (0, 0);
			}

			// ====== 1) 先计提管理费（不管盈亏） ======
			// 管理费 = 市值 × 管理费率 × 持有天数 / 365
			// 费率为1e18精度，故除以 1e18
			mgmtFee = (cashSlice * managementFeeRate * daysHeld) / (1e18 * 365);

			// 极端保护：若管理费已覆盖全部市值，直接吃掉全部，业绩费必为0
			if (mgmtFee >= cashSlice) {
				mgmtFee = cashSlice;
				return (mgmtFee, 0);
			}

			// 扣除管理费后的市值（用于后续业绩费计算的基准）
			uint256 afterMgmt = cashSlice - mgmtFee;

			// ====== 2) 计算业绩费（在扣除管理费后再看是否有“超额收益”） ======
			// 阈值收益（hurdle）= 本金 × 年化阈值 × 天数 / 365
			uint256 thresholdGain = (principalSlice * annualThreshold * daysHeld) / (1e18 * 365);

			// 扣管费后的名义收益：若仍低于本金则视为0（不收业绩费）
			uint256 gainAfterMgmt = afterMgmt > principalSlice ? (afterMgmt - principalSlice) : 0;

			if (gainAfterMgmt > thresholdGain) {
				// 超过阈值的部分才参与业绩分成
				uint256 excess = gainAfterMgmt - thresholdGain;
				// 业绩费 = 超额收益 × 业绩费率
				perfFee = (excess * performanceFeeRate) / 1e18;
			} else {
				perfFee = 0;
			}

			// ====== 3) 费用上限 cap（对“本次片段”的总费用进行封顶） ======
			// 上限以“片段的未扣费市值”为基数：feeCap = cashSlice × feeCapBps / 10000
			uint256 feeCap = (cashSlice * feeCapBps) / 10000;
			uint256 totalFees = mgmtFee + perfFee;

			if (totalFees > feeCap) {
				mgmtFee = feeCap;
				perfFee = 0;
				totalFees = feeCap; // 记录最终总费用
			}
			return (mgmtFee, perfFee);
		}

		// ========================
		// ===== 管理函数 =========
		// ========================

		/**
		 * @notice 返回基金池合约当前持有的 USDT 和 BTCB 余额
		 * @dev 主要用于前端展示基金资产构成，或者链上调用时查看基金的实时代币余额
		 * @return usdtBalance 合约中当前的 USDT 余额
		 * @return btcBalance  合约中当前的 BTCB 余额
		 */
		function getTokenBalances() 
			external 
			view 
			returns (uint256 usdtBalance, uint256 btcBalance) 
		{
			// 1. 查询合约地址持有的 USDT 数量
			usdtBalance = USDT.balanceOf(address(this));

			// 2. 查询合约地址持有的 BTCB 数量
			btcBalance  = BTCB.balanceOf(address(this));
		}

		/**
		 * @notice 计算基金当前的总净值（以 USDT 计价）
		 * @dev 总净值 = 合约内持有的 USDT + 合约内持有的 BTCB 折算成 USDT
		 * @return uint256 返回基金总净值（单位：USDT）
		 */
		function getFundValue() public view returns (uint256) {
			// 1. 获取 BTC 的最新价格（来自 Chainlink 预言机）
			//    - btcPrice: BTC 单价（例如 60000 USDT）
			//    - pdec: 价格小数精度（通常是 8）
			(uint256 btcPrice, uint8 pdec) = getBTCPrice();

			// 2. 查询合约当前持有的 USDT 余额
			uint256 usdtBal = USDT.balanceOf(address(this));

			// 3. 查询合约当前持有的 BTCB 余额
			uint256 btcBal  = BTCB.balanceOf(address(this));

			// 4. 计算 BTCB 价值（折算成 USDT）
			//    btcVal = BTC 数量 × BTC 单价 ÷ 10^小数位
			uint256 btcVal  = (btcBal * btcPrice) / (10 ** pdec);

			// 5. 返回总净值（USDT + BTC 折算值）
			return usdtBal + btcVal;
		}


		/**
		 * @notice 计算用户某笔投资（commitment）的当前净值和费用情况
		 * @param commitment 投资承诺（存款批次）的唯一标识
		 * @return grossValue    当前该笔投资的总市值（未扣除费用）
		 * @return mgmtFee       累计管理费
		 * @return perfFee       累计业绩分成
		 * @return netValue      扣除费用后的净值
		 * @return principalLeft 剩余本金（可能因部分赎回而减少）
		 */
		function estimateCommitmentValue(bytes32 commitment) 
			external 
			view 
			returns (
				uint256 grossValue,
				uint256 mgmtFee,
				uint256 perfFee,
				uint256 netValue,
				uint256 principalLeft
			) 
		{
			// 1. 查找该 commitment 对应的投资批次信息
			Lot storage lot = lotByCommitment[commitment];
			require(lot.shares > 0, "no shares"); // 必须有份额，否则报错

			// 2. 计算该 commitment 当前的总市值
			uint256 fundValue = getFundValue();                   // 获取基金当前总净值
			grossValue = (lot.shares * fundValue) / totalShares;  // 投资市值 = 用户份额 × 单位净值

			// 3. 返回剩余本金（可能因部分赎回而变化）
			principalLeft = lot.principal;

			// 4. 计算累计管理费
			uint256 daysHeld = (block.timestamp - lot.depositTime) / 1 days; // 持有天数
			// 管理费 = 总市值 × 管理费率 × 持有天数 / 365
			mgmtFee = (grossValue * managementFeeRate * daysHeld) / 1e18 / 365;

			// 5. 计算业绩分成的门槛收益（阈值收益）
			// 阈值收益 = 本金 × 年化阈值 × 持有天数 / 365
			uint256 thresholdGain = (principalLeft * annualThreshold * daysHeld) / 1e18 / 365;

			// 实际收益（总市值 - 本金，若亏损则为 0）
			uint256 grossGain = grossValue > principalLeft ? (grossValue - principalLeft) : 0;

			// 如果超过阈值收益，则对超出部分收取业绩费
			if (grossGain > thresholdGain) {
				uint256 excess = grossGain - thresholdGain;          // 超过的部分
				perfFee = (excess * performanceFeeRate) / 1e18;      // 业绩分成
			}

			// 6. 检查费用上限（cap）
			// 费用上限 = 总市值 × cap百分比
			uint256 feeCap = (grossValue * feeCapBps) / 10000;
			uint256 fees = mgmtFee + perfFee;
			if (fees > feeCap) {
				// 如果超过 cap，feeCap全部给管理费
				mgmtFee = feeCap;
				perfFee = 0;
			}

			// 7. 计算净值（扣除费用后）
			netValue = grossValue - mgmtFee - perfFee;
		}

		/**
		 * @notice 更新基金合约的所有关键参数（仅限合约所有者调用）
		 * @param newMgmtRate       新的管理费率（年化），单位：wei，最大值为 5% (5e16)
		 * @param newPerfRate       新的业绩分成费率，单位：wei，最大值为 30% (30e16)
		 * @param newThreshold      新的收益阈值，单位：wei，最大值为 10% (10e16)
		 * @param newFeeCapBps      新的总费用上限（基点表示，1% = 100），最大为 3000 (即 30%)
		 * @param newMinDepositUSDT 新的最低存款金额（单位：USDT，必须 > 0）
		 */
		function updateAllParams(
			uint256 newMgmtRate,
			uint256 newPerfRate,
			uint256 newThreshold,
			uint256 newFeeCapBps,
			uint256 newMinDepositUSDT
		) external onlyOwner {
			// ============ 参数合法性校验 ============
			require(newMgmtRate   <= 5e16,  "mgmt>5%");      // 管理费不得超过 5%
			require(newPerfRate   <= 30e16, "perf>30%");     // 业绩费不得超过 30%
			require(newThreshold  <= 10e16, "thresh>10%");   // 阈值不得超过 10%
			require(newFeeCapBps  <= 3000,  "cap>30%");      // 总费用上限不得超过 30%（3000 基点）
			require(newMinDepositUSDT > 0,  "minDeposit=0"); // 最低存款金额必须大于 0

			// ============ 更新存储变量 ============
			managementFeeRate  = newMgmtRate;       // 更新管理费率
			performanceFeeRate = newPerfRate;       // 更新业绩费率
			annualThreshold    = newThreshold;      // 更新收益阈值
			feeCapBps          = newFeeCapBps;      // 更新总费用上限
			minDepositUSDT     = newMinDepositUSDT; // 更新最低存款金额

			// ============ 触发事件 ============
			// 方便前端或链上监听，记录参数的变更
			emit AllParamsUpdated(
				newMgmtRate,
				newPerfRate,
				newThreshold,
				newFeeCapBps,
				newMinDepositUSDT
			);
		}

    /**
     * @notice 暂停合约（如遇到类似黑客攻击等事故，全局性暂停，存取款均不可执行）
     * @dev 只有合约所有者可以调用
     */
    function pauseVault() external onlyOwner {
        _pause(); // 调用 OZ 的内部函数
    }

    /**
     * @notice 恢复合约（恢复正常运行）
     * @dev 只有合约所有者可以调用
     */
    function unpauseVault() external onlyOwner {
        _unpause(); // 调用 OZ 的内部函数
    }

}
