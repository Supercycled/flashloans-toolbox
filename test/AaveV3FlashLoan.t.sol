pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "../src/AaveV3FlashLoan.sol";
import "forge-std/console2.sol";
import {SharedSetupAvax} from "./SharedSetup.sol";

// tests done on avax-main network
// rpc: https://api.avax.network/ext/bc/C/rpc 

contract Foo is AaveV3FlashLoan , SharedSetupAvax{

    function maxFlashWeth() external {
        uint256 amountToLoan = maxFlashLoan(WETH);
        flashLoan(WETH, amountToLoan);
    }

    function maxFlashAll() external{
        address[] memory tokens = new address[](4);
        uint256[] memory amounts = new uint256[](4);
        tokens[0] = DAI;
        tokens[1] = USDC;
        tokens[2] = WETH;
        tokens[3] = USDT;
        
        amounts[0] = maxFlashLoan(DAI);
        amounts[1] = maxFlashLoan(USDC);
        amounts[2] = maxFlashLoan(WETH);
        amounts[3] = maxFlashLoan(USDT);

        flashLoan(tokens, amounts);
    }

    function onAaveV3FlashLoan() override internal {
        console.log("=> borrowed DAI balance:", IERC20(DAI).balanceOf(address(this)));
        console.log("=> borrowed USDC balance:", IERC20(USDC).balanceOf(address(this)));
        console.log("=> borrowed WETH balance:", IERC20(WETH).balanceOf(address(this)));
        console.log("=> borrowed USDT balance:", IERC20(USDT).balanceOf(address(this)));
    }
}

contract AaveV3FlashLoanTest is Test, SharedSetupAvax{
    using SafeERC20 for IERC20;

    Foo foo;

    function setUp() public {
        foo = new Foo();
        vm.deal(address(foo), 0);
    }

    function testmaxFlashWeth() public {

        vm.startPrank(wethProvider);
        IERC20(WETH).safeTransfer(address(foo), IERC20(WETH).balanceOf(wethProvider));
        vm.stopPrank();

        uint256 maxAmount = foo.maxFlashLoan(WETH);
        console2.log("=> amount expected to borrow:", maxAmount);
        console2.log("=> estimated amount of fees:", foo.estimateFlashLoanFee(WETH, maxAmount));

        foo.maxFlashWeth();
    }

    function testmaxFlashAll() public {

        vm.startPrank(wethProvider);
        IERC20(WETH).safeTransfer(address(foo), IERC20(WETH).balanceOf(wethProvider));
        vm.stopPrank();

        vm.startPrank(usdcProvider);
        IERC20(USDC).safeTransfer(address(foo), IERC20(USDC).balanceOf(usdcProvider));
        vm.stopPrank();

        vm.startPrank(daiProvider);
        IERC20(DAI).safeTransfer(address(foo), IERC20(DAI).balanceOf(daiProvider));
        vm.stopPrank();

        vm.startPrank(usdtProvider);
        IERC20(USDT).safeTransfer(address(foo), IERC20(USDT).balanceOf(usdtProvider));
        vm.stopPrank();

        foo.maxFlashAll();
    }
}