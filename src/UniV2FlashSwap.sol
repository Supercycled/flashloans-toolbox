// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

interface IUniswapV2Callee {
    function uniswapV2Call(address sender, uint amount0, uint amount1, bytes calldata data) external;
}

interface IUniswapV2Pair {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;

    event Mint(address indexed sender, uint amount0, uint amount1);
    event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint);
    function factory() external view returns (address);
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
    function price0CumulativeLast() external view returns (uint);
    function price1CumulativeLast() external view returns (uint);
    function kLast() external view returns (uint);

    function mint(address to) external returns (uint liquidity);
    function burn(address to) external returns (uint amount0, uint amount1);
    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;
    function skim(address to) external;
    function sync() external;

    function initialize(address, address) external;
}

// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC20/IERC20.sol)

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
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
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
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
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}

// OpenZeppelin Contracts (last updated v4.7.0) (token/ERC20/utils/SafeERC20.sol)

// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/draft-IERC20Permit.sol)

/**
 * @dev Interface of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on {IERC20-approve}, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 */
interface IERC20Permit {
    /**
     * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
     * given ``owner``'s signed approval.
     *
     * IMPORTANT: The same issues {IERC20-approve} has related to transaction
     * ordering also apply here.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `deadline` must be a timestamp in the future.
     * - `v`, `r` and `s` must be a valid `secp256k1` signature from `owner`
     * over the EIP712-formatted function arguments.
     * - the signature must use ``owner``'s current nonce (see {nonces}).
     *
     * For more information on the signature format, see the
     * https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP
     * section].
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    /**
     * @dev Returns the current nonce for `owner`. This value must be
     * included whenever a signature is generated for {permit}.
     *
     * Every successful call to {permit} increases ``owner``'s nonce by one. This
     * prevents a signature from being used multiple times.
     */
    function nonces(address owner) external view returns (uint256);

    /**
     * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}

// OpenZeppelin Contracts (last updated v4.7.0) (utils/Address.sol)

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verify that a low level call to smart-contract was successful, and revert (either by bubbling
     * the revert reason or using the provided one) in case of unsuccessful call or if target was not a contract.
     *
     * _Available since v4.8._
     */
    function verifyCallResultFromTarget(
        address target,
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        if (success) {
            if (returndata.length == 0) {
                // only check isContract if the call was successful and the return data is empty
                // otherwise we already know that it was a contract
                require(isContract(target), "Address: call to non-contract");
            }
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    /**
     * @dev Tool to verify that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason or using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    function _revert(bytes memory returndata, string memory errorMessage) private pure {
        // Look for revert reason and bubble it up if present
        if (returndata.length > 0) {
            // The easiest way to bubble the revert reason is using memory via assembly
            /// @solidity memory-safe-assembly
            assembly {
                let returndata_size := mload(returndata)
                revert(add(32, returndata), returndata_size)
            }
        } else {
            revert(errorMessage);
        }
    }
}

/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
    }

    function safePermit(
        IERC20Permit token,
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        uint256 nonceBefore = token.nonces(owner);
        token.permit(owner, spender, value, deadline, v, r, s);
        uint256 nonceAfter = token.nonces(owner);
        require(nonceAfter == nonceBefore + 1, "SafeERC20: permit did not succeed");
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}

/*
 * @title Solidity Bytes Arrays Utils
 * @author Gonçalo Sá <goncalo.sa@consensys.net>
 *
 * @dev Bytes tightly packed arrays utility library for ethereum contracts written in Solidity.
 *      The library lets you concatenate, slice and type cast bytes arrays both in memory and storage.
 */

library BytesLib {
    
    function slice(
        bytes memory _bytes,
        uint256 _start,
        uint256 _length
    ) internal pure returns (bytes memory) {
        require(_length + 31 >= _length, 'slice_overflow');
        require(_start + _length >= _start, 'slice_overflow');
        require(_bytes.length >= _start + _length, 'slice_outOfBounds');

        bytes memory tempBytes;

        assembly {
            switch iszero(_length)
                case 0 {
                    // Get a location of some free memory and store it in tempBytes as
                    // Solidity does for memory variables.
                    tempBytes := mload(0x40)

                    // The first word of the slice result is potentially a partial
                    // word read from the original array. To read it, we calculate
                    // the length of that partial word and start copying that many
                    // bytes into the array. The first word we copy will start with
                    // data we don't care about, but the last `lengthmod` bytes will
                    // land at the beginning of the contents of the new array. When
                    // we're done copying, we overwrite the full first word with
                    // the actual length of the slice.
                    let lengthmod := and(_length, 31)

                    // cete operation  and eqiuivaut à mod(_length, 32)!!
                    // on obtiens ainsi le bout de _bytes qui va rester une fois qu'on l'aura fetch par block de 32 bytes

                    // The multiplication in the next line is necessary
                    // because when slicing multiples of 32 bytes (lengthmod == 0)
                    // the following copy loop was copying the origin's length
                    // and then ending prematurely not copying everything it should.
                    let mc := add(add(tempBytes, lengthmod), mul(0x20, iszero(lengthmod)))
                    
                    // ici, mc est soit == fmp + lengthmod, soit == fmp + 32
                    
                    let end := add(mc, _length)

                    for {
                        // The multiplication in the next line has the same exact purpose
                        // as the one above.
                        let cc := add(add(add(_bytes, lengthmod), mul(0x20, iszero(lengthmod))), _start)
                    } lt(mc, end) {
                        mc := add(mc, 0x20)
                        cc := add(cc, 0x20)
                    } {
                        mstore(mc, mload(cc))
                    }

                    mstore(tempBytes, _length)

                    //update free-memory pointer
                    //allocating the array padded to 32 bytes like the compiler does now
                    mstore(0x40, and(add(mc, 31), not(31)))
                }
                //if we want a zero-length slice let's just return a zero-length array
                default {
                    tempBytes := mload(0x40)
                    //zero out the 32 bytes slice we are about to return
                    //we need to do it because Solidity does not garbage collect
                    mstore(tempBytes, 0)

                    mstore(0x40, add(tempBytes, 0x20))
                }
        }

        return tempBytes;
    }

    function toAddress(bytes memory _bytes, uint256 _start) internal pure returns (address) {
        
        require(_start + 20 >= _start, 'toAddress_overflow');
        require(_bytes.length >= _start + 20, 'toAddress_outOfBounds');
        address tempAddress;

        assembly {
            tempAddress := div(mload(add(add(_bytes, 0x20), _start)), 0x1000000000000000000000000)
        }

        return tempAddress;
    }

    function toUint24(bytes memory _bytes, uint256 _start) internal pure returns (uint24) {
        require(_start + 3 >= _start, 'toUint24_overflow');
        require(_bytes.length >= _start + 3, 'toUint24_outOfBounds');
        uint24 tempUint;

        assembly {

             
            tempUint := mload(add(add(_bytes, 0x3), _start))
            // le memory slot qui est load ici peut ressembler a SSSSSSSVVVVVVVVVVVV (size, value) ou on load une partie du size word
            // tout ce qu'on sait c'est que les 3 derniers bytes de ce word == notre uint 24
        }

        return tempUint; // l'implicit convertion uint256 => uint24 fait le taff en ne gardant que les 3 derniers bytes 
    }

    function toUint256(bytes memory _bytes, uint256 _start) internal pure returns (uint256 value){
        require(_start + 20 >= _start, 'toUint256_overflow');
        require(_bytes.length >= _start + 20, 'toUint256_outOfBounds');

        assembly {
            value := mload(add(add(_bytes, 0x20), _start))
        }
    }
}

       
contract RepaimentStorage {

    // loans storage. Erased after each flashSwap call with repayLoans()
    mapping(address => Loan[]) loans; 
    mapping(address => uint256) totalBorrowPerToken;
    address[] public borrowedTokens; 

    struct Loan {
        address pool;
        address token;
        uint256 amount;
        uint256 fee;
    }

    // use this function if you want to du multiple flashloans
    function cleanupRepaimentStorage() internal {

        if (borrowedTokens.length > 0) {

            for (uint256 i = 0; i < borrowedTokens.length; i++) {

                address token = borrowedTokens[i];
                delete totalBorrowPerToken[token];
                delete loans[token];
            }
        }
        delete borrowedTokens;
    }
}

    
    

abstract contract UniV2FlashSwap is IUniswapV2Callee,  RepaimentStorage {
    
    using BytesLib for bytes;
    using SafeERC20 for IERC20;

    uint256 private constant ONEFLASHSWAPUNIV2 = 84;
    address private constant FACTORYV2 = 0x1F98431c8aD98523631AE4a59f267346ea31F984;

    // pool storage 
    mapping(address => uint256) public numberOfPoolForAsset;
    mapping(address => mapping(uint256 => address)) public poolsForAsset;

    event FlashSwap(
        address indexed token,
        uint256 indexed amount,
        uint256 indexed feePaid
    );

    constructor(){
        initializeKnownPools();
    }

    // main pools for BSC
    // should be overriden if you want to use other pools or other networks 
    function initializeKnownPools() internal virtual {

        address WBNB = 0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c;
        address BUSD = 0xe9e7CEA3DedcA5984780Bafc599bD69ADd087D56;
        address CAKE = 0x0E09FaBB73Bd3Ade0a17ECC321fD13a19e81cE82;
        address USDT = 0x55d398326f99059fF775485246999027B3197955;
        address WETH = 0x2170Ed0880ac9A755fd29B2688956BD959F933F8;
        address BTCB = 0x7130d2A12B9BCbFAe4f2634d864A1Ee1Ce3Ead9c;

        numberOfPoolForAsset[WBNB] = 5;
        numberOfPoolForAsset[BUSD] = 3;
        numberOfPoolForAsset[USDT] = 3;
        numberOfPoolForAsset[BTCB] = 3;

        poolsForAsset[WBNB][1] = 0x16b9a82891338f9bA80E2D6970FddA79D1eb0daE; // USDTWBNB
        poolsForAsset[WBNB][2] = 0x58F876857a02D6762E0101bb5C46A8c1ED44Dc16; // WBNBBUSD
        poolsForAsset[WBNB][3] = 0x0eD7e52944161450477ee417DE9Cd3a859b14fD0; // CAKEWBNB
        poolsForAsset[WBNB][4] = 0x74E4716E431f45807DCF19f284c7aA99F18a4fbc; // WETHWBNB
        poolsForAsset[WBNB][5] = 0x61EB789d75A95CAa3fF50ed7E47b96c132fEc082; // BTCBWBNB

        poolsForAsset[BUSD][1] = 0x58F876857a02D6762E0101bb5C46A8c1ED44Dc16; // WBNBBUSD
        poolsForAsset[BUSD][2] = 0x7EFaEf62fDdCCa950418312c6C91Aef321375A00; // USDTBUSD
        poolsForAsset[BUSD][3] = 0xF45cd219aEF8618A92BAa7aD848364a158a24F33; // BTCBBUSD

        poolsForAsset[USDT][1] = 0x16b9a82891338f9bA80E2D6970FddA79D1eb0daE; // USDTWBNB
        poolsForAsset[USDT][2] = 0x7EFaEf62fDdCCa950418312c6C91Aef321375A00; // USDTBUSD
        poolsForAsset[USDT][3] = 0xcd9D281a588b69EcDFfA411363661954Aa339C7b; // USDTTAU

        poolsForAsset[BTCB][1] = 0xF45cd219aEF8618A92BAa7aD848364a158a24F33; // BTCBBUSD
        poolsForAsset[BTCB][2] = 0x61EB789d75A95CAa3fF50ed7E47b96c132fEc082; // BTCBWBNB
        poolsForAsset[BTCB][3] = 0xD171B26E4484402de70e3Ea256bE5A2630d7e88D; // WETHBTCB
    }

    function maxFlashSwap(address token) public view virtual returns(uint256 amount){
        if (numberOfPoolForAsset[token] == 0) return 0;

        for (uint256 i = 1; i <= numberOfPoolForAsset[token]; i++){

            address pair = poolsForAsset[token][i];
            (uint112 reserve0, uint112 reserve1,) = IUniswapV2Pair(pair).getReserves();
            uint256 increment = token == IUniswapV2Pair(pair).token0() ? reserve0 : reserve1;
            amount += (increment -1); // amountOut must be < reserve
        }
    }

    function estimateFlashSwapFee(address token, uint256 amount) public view virtual returns(uint256 feesEstimated){
        
        address[] memory tokens = new address[](1);
        uint256[] memory amounts = new uint256[](1);
        tokens[0] = token;
        amounts[0] = amount;
        bytes memory flashSwapPath = _buildFlashSwapsArray(tokens, amounts);

        while (flashSwapPath.length > 0){
            (, uint256 amount0, uint256 amount1) = decodeFirstFlashSwap(flashSwapPath);
            uint256 _amount = amount0 > 0? amount0 : amount1;
            feesEstimated += _amount * 3 / 997 + 1; // 0.3%
            flashSwapPath = skipFlashSwap(flashSwapPath);
        }
    }

    function _updateRepaimentStorage(address token, address pool, uint256 amount,uint256 fee) private {
        if (totalBorrowPerToken[token] == 0) borrowedTokens.push(token);
        loans[token].push() = Loan(pool, token, amount, fee);
        totalBorrowPerToken[token] += (amount + fee);
    }

    function pancakeCall(address sender, uint amount0, uint amount1, bytes calldata data) external{
        uniswapV2FlashCallback(sender, amount0, amount1, data);
    }

    function uniswapV2Call(address sender, uint amount0, uint amount1, bytes calldata data) external{
        uniswapV2FlashCallback(sender, amount0, amount1, data);
    }

    function uniswapV2FlashCallback(address sender, uint amount0, uint amount1, bytes calldata data) internal {
        require(sender == address(this), "UniV2FlashSwap: unauthorized");
        bytes memory flashSwapPath = data;
        (address pair,,) = decodeFirstFlashSwap(flashSwapPath);
        require(msg.sender == pair);
        
        // edit repaiement storage
        if (amount0 > 0){
            address token0 = IUniswapV2Pair(pair).token0();
            _updateRepaimentStorage(token0, pair, amount0, (amount0 * 3 / 997) + 1);
        }
        if (amount1 > 0){
            address token1 = IUniswapV2Pair(pair).token1();
            _updateRepaimentStorage(token1, pair, amount1, (amount1 * 3 / 997) + 1);
        }

        // edit flashSwaps
        flashSwapPath = skipFlashSwap(flashSwapPath);
        _executeFlashSwaps(flashSwapPath);
    }

    function repayLoans() private {

        for (uint256 i = 0; i < borrowedTokens.length; i++){
            
            address token = borrowedTokens[i];
            Loan[] memory tokenLoans = loans[token];
            uint256 feeTotal;
            uint256 amountTotal;

            // repay the loans
            for (uint256 j; j < tokenLoans.length; j++){
                Loan memory loan = tokenLoans[j];
        
                require(
                    IERC20(token).balanceOf(address(this)) >= (loan.amount + loan.fee), 
                    "UniV2FlashSwap: repay loan: not enough balance to repay loan"
                );
                feeTotal += loan.fee;
                amountTotal += loan.amount;
                IERC20(token).safeTransfer(loan.pool, loan.amount + loan.fee);
            }
            emit FlashSwap(token, amountTotal, feeTotal);
        }
    }

    function _buildFlashSwapsArray(
        
        address[] memory tokens, 
        uint256[] memory amounts) internal view returns(bytes memory flashSwapPath){
        
        require(tokens.length == amounts.length, "UniV2FlashSwap: length of amounts and tokens doesnt match");
    
        for (uint256 i = 0; i < tokens.length; ++i){

            address token = tokens[i];
            uint256 amount = amounts[i];

            require(numberOfPoolForAsset[token] > 0, "UniV2FlashSwap: asset not supported");
            require(amount <= maxFlashSwap(token), "UniV2FlashSwap: amount to fs > maxFlashSwap");

            uint256 counter = 0;
            uint256 tempAmount = amount;

            // build the flashSwaps byte array
            // [pair][amount0][amount1]
            while (tempAmount > 0) {
                
                address nextPair = poolsForAsset[token][counter + 1];
                (uint112 reserve0, uint112 reserve1,) = IUniswapV2Pair(nextPair).getReserves();
                uint256 pairReserve = token == IUniswapV2Pair(nextPair).token0() ? reserve0: reserve1;     
                pairReserve -=1; // amountOut must be < reserve           
                uint256 increment = pairReserve >= tempAmount? tempAmount: pairReserve;
                uint256 amount0 = pairReserve + 1 == reserve0 ? increment : 0;                
                uint256 amount1 = amount0 > 0? 0 : increment;

                if (flashSwapPath.length == 0){
                    flashSwapPath = abi.encodePacked(nextPair, amount0, amount1);
                    continue;
                }

                bool expendPath = true;

                assembly {

                    let numberOfFlashSwaps := div(mload(flashSwapPath), ONEFLASHSWAPUNIV2)
                    let startPtr := add(flashSwapPath, 0x20)

                    // check if the pool is already registered in flashSwapPath
                    for {let j := 0} lt(j, numberOfFlashSwaps) {j:= add(j, 1)}{
                        
                        let swapptr := add(startPtr, mul(j, ONEFLASHSWAPUNIV2))
                        let pool := shr(96, mload(swapptr))

                        if eq(pool, nextPair) {
                            // if amount0 == 0 , store amount1 
                            if iszero(amount0) {mstore(add(swapptr, 52), amount1)}
                            // if amount1 == 0 , store amount0 
                            if iszero(amount1) {mstore(add(swapptr, 20), amount0)}
                            expendPath := 0
                        }
                    }
                }

                if (expendPath) flashSwapPath = abi.encodePacked(
                    flashSwapPath, 
                    nextPair, 
                    amount0, 
                    amount1);

                tempAmount -= increment;
                ++counter;
            }
        }
    }

    function _executeFlashSwaps(bytes memory flashSwapPath) private {
        
        // actually execute the flashSwaps here. reentrancy is desired 
        if (flashSwapPath.length > 0) {
                (address pool, uint256 amount0, uint256 amount1) = decodeFirstFlashSwap(flashSwapPath);
                IUniswapV2Pair(pool).swap(amount0, amount1, address(this), flashSwapPath);
        } 
        // if the length is only 1, it means all the flashswaps are done
        else {
            onUniV2FlashSwap();
            repayLoans();
        }
    }

    function flashSwap(address[] memory tokens, uint256[] memory amounts) internal {
        bytes memory flashSwapPath = _buildFlashSwapsArray(tokens, amounts);
        _executeFlashSwaps(flashSwapPath);
    }

    function flashSwap(address token, uint256 amount) internal {
        address[] memory tokens = new address[](1);
        uint256[] memory amounts = new uint256[](1);
        tokens[0] = token;
        amounts[0] = amount;
        flashSwap(tokens, amounts);
    }
    
    function decodeFirstFlashSwap(bytes memory flashSwapPath)
        private
        pure
        returns (
            address pool,
            uint256 amount0,
            uint256 amount1
        ) {
            pool = flashSwapPath.toAddress(0);
            amount0 = flashSwapPath.toUint256(20);
            amount1 = flashSwapPath.toUint256(52);
    }

    function skipFlashSwap(bytes memory flashSwapPath) private pure returns (bytes memory){
        return flashSwapPath.slice(ONEFLASHSWAPUNIV2, flashSwapPath.length - ONEFLASHSWAPUNIV2);
    }

    // should be overriden with your own logic 
    function onUniV2FlashSwap() internal virtual;
}
