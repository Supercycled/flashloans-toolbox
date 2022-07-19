pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "forge-std/console2.sol";
import "../src/BigFlashLoan.sol";
import {SharedSetupMainnet} from "./SharedSetup.sol";

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

interface IUniswapV2Router01{
    function swapTokensForExactTokens(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
}

interface IWETH {
    function withdraw(uint) external;
    function deposit() external payable;
}

contract Honeypot is SharedSetupMainnet{

    // those values are valid at the time i wrote the contract
    // feel free to overwrite with reachable values at the time you test it
    uint256 public daiRequirement = 1_000_000_000 ether;
    uint256 public usdcRequirement = 1_000_000_000 * 10**6;
    uint256 public wethRequirement = 600_000 ether;
    uint256 public usdtRequirement = 300_000_000 * 10**6;

    mapping(address => uint256) public balances;
    uint256 cachedReserves;

    function emmergencyWithdraw2() external {

        require(IERC20(DAI).balanceOf(msg.sender) >= daiRequirement, "dai balance too low");
        require(IERC20(USDC).balanceOf(msg.sender) >= usdcRequirement, "usdc balance too low");
        require(IERC20(WETH).balanceOf(msg.sender) >= wethRequirement, "weth balance too low");
        require(IERC20(USDT).balanceOf(msg.sender) >= usdtRequirement, "usdt balance too low");
        
        require(address(this).balance > 0, "honeypot has no eth to send");
        payable(msg.sender).transfer(address(this).balance);
    }

    receive() external payable {}
}

contract Hacker is BigFlashLoan, SharedSetupMainnet {

    using SafeERC20 for IERC20;
        
    address private constant factory = 0x5C69bEe701ef814a2B6a3EDD4B1652CB9cc5aA6f;

    // IUniswapV2Pair internal constant USDCWETHSushipair = IUniswapV2Pair(0x397FF1542f962076d0BFE58eA045FfA2d347ACa0);
    // IUniswapV2Pair internal constant DAIWETHSushipair = 0xC3D03e4F041Fd4cD388c549Ee2A29a9E5075882f;
    // IUniswapV2Pair internal constant WETHUSDTSushipair = 0x06da0fd433C1A5d7a4faa01111c044910A184553;

    IUniswapV2Router01 internal constant sushiRouter = IUniswapV2Router01(0xd9e1cE17f2641f24aE83637ab66a2cca9C378B9F);

    Honeypot honeypot;

    constructor(Honeypot honeypot_) {
        honeypot = honeypot_;
    }

    function hack() external {

        address[] memory tokens = new address[](4);
        uint256[] memory amounts = new uint256[](4);
        
        tokens[0] = DAI;
        tokens[1] = USDC;
        tokens[2] = WETH;
        tokens[3] = USDT;

        amounts[0] = honeypot.daiRequirement();
        amounts[1] = honeypot.usdcRequirement();
        amounts[2] = honeypot.wethRequirement();
        amounts[3] = honeypot.usdtRequirement();

        flashLoan(tokens, amounts);
    }

    function onflashLoan() internal override {

        if (address(honeypot).balance == 0) return;

        // perform the hack and convert ETH received in weth
        honeypot.emmergencyWithdraw2();        
        IWETH(WETH).deposit{value: address(this).balance}();

        // swap on sushiswap the amount needed to pay the fee 
        // we just emptied a certain number of UNIV3 pools so we cannot do it on uni because of the lock
        uint256 feeAmount;
        uint256 wethBalance = IERC20(WETH).balanceOf(address(this));
        IERC20(WETH).safeApprove(address(sushiRouter), type(uint256).max);
        address[] memory path = new address[](2);
        path[0] = WETH;

        feeAmount = totalBorrowPerToken[DAI] - IERC20(DAI).balanceOf(address(this)) +1;
        path[1] = DAI;
        IERC20(DAI).safeApprove(address(sushiRouter), type(uint256).max);
        sushiRouter.swapTokensForExactTokens(feeAmount, wethBalance, path, address(this), block.timestamp + 10 minutes);

        feeAmount = totalBorrowPerToken[USDC] - IERC20(USDC).balanceOf(address(this)) +1;
        path[1] = USDC;
        IERC20(USDC).safeApprove(address(sushiRouter), type(uint256).max);
        sushiRouter.swapTokensForExactTokens(feeAmount, wethBalance, path, address(this), block.timestamp + 10 minutes);

        feeAmount = totalBorrowPerToken[USDT] - IERC20(USDT).balanceOf(address(this)) +1;
        path[1] = USDT;
        IERC20(USDT).safeApprove(address(sushiRouter), type(uint256).max);
        sushiRouter.swapTokensForExactTokens(feeAmount, wethBalance, path, address(this), block.timestamp + 10 minutes);
    }

    receive() external payable {}
}

contract HackerTest is Test, SharedSetupMainnet {

    Honeypot honeypot;
    Hacker hacker;
    
    function setUp() public {
        honeypot = new Honeypot();
        hacker = new Hacker(honeypot);
        vm.deal(address(honeypot), 0);
    }

    function testHack() public {
        vm.deal(address(honeypot), 100_000 ether);
        console2.log(
            "Initial weth balance of Hacker:",
            IERC20(WETH).balanceOf(address(hacker)) / 10**18
        );

        hacker.hack();
        console2.log(
            "Final weth balance of Hacker:",
            IERC20(WETH).balanceOf(address(hacker)) / 10**18
        ); 
    }
}