pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "../src/BigFlashLoan.sol";
import "forge-std/console2.sol";
import {SharedSetupMainnet} from "./SharedSetup.sol";

// tests done on mainnet

contract Foo is BigFlashLoan, SharedSetupMainnet {

    function maxFlashWeth() external {
        uint256 amountToLoan = maxLoan(WETH);
        flashLoan(WETH, amountToLoan);
    }

    function maxFlashAll() external{
        address[] memory tokens = new address[](4);
        uint256[] memory amounts = new uint256[](4);
        
        tokens[0] = DAI;
        tokens[1] = USDC;
        tokens[2] = WETH;
        tokens[3] = USDT;
        
        amounts[0] = maxLoan(DAI);
        amounts[1] = maxLoan(USDC);
        amounts[2] = maxLoan(WETH);
        amounts[3] = maxLoan(USDT);

        flashLoan(tokens, amounts);
    }

    function onflashLoan() override internal {}
}

contract BigFlashLoanTest is Test , SharedSetupMainnet{
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

        uint256 maxAmount = foo.maxLoan(WETH);
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

        console2.log("=> flash borrowed WETH amount:", foo.maxLoan(WETH) / 1e18);
        console2.log("=> flash borrowed DAI amount:", foo.maxLoan(DAI) / 1e18);
        console2.log("=> flash borrowed USDC amount:", foo.maxLoan(USDC)/1e6);
        console2.log("=> flash borrowed USDT amount:", foo.maxLoan(USDT)/1e6);

        foo.maxFlashAll();
    }
}