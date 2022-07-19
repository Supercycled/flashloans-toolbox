pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "forge-std/console2.sol";
import "../src/UniV3FlashSwap.sol";
import {SharedSetupMainnet} from "./SharedSetup.sol";

// tests done on mainnet

contract Foo is UniV3FlashSwap, SharedSetupMainnet {

    function maxLoanWeth() external {
        flashSwap(WETH, maxFlashSwap(WETH));
    }

    function maxLoanAll() external {
        address[] memory tokens = new address[](3);
        uint256[] memory amounts = new uint256[](3);
        
        tokens[0] = DAI;
        tokens[1] = USDC;
        tokens[2] = WETH;
        amounts[0] = maxFlashSwap(DAI);
        amounts[1] = maxFlashSwap(USDC);
        amounts[2] = maxFlashSwap(WETH);
        flashSwap(tokens, amounts);
    }

    function onUniV3FlashSwap() internal override {
        console.log("=> borrowed DAI balance:", IERC20(DAI).balanceOf(address(this)));
        console.log("=> borrowed USDC balance:", IERC20(USDC).balanceOf(address(this)));
        console.log("=> borrowed WETH balance:", IERC20(WETH).balanceOf(address(this)));
    }
}


contract UniV3FlashSwapTest is Test , SharedSetupMainnet {
    using SafeERC20 for IERC20;

    Foo foo;
    
    function setUp() public {
        foo = new Foo();
        vm.deal(address(foo), 0);
    }

    function testmaxLoanWeth() public {

        // transfer weth to foo so that it can repay the loan
        vm.startPrank(wethProvider);
        IERC20(WETH).safeTransfer(address(foo), IERC20(WETH).balanceOf(wethProvider));
        vm.stopPrank();

        uint256 expectedFee = foo.estimateFlashSwapFee(WETH ,foo.maxFlashSwap(WETH));
        console2.log("=> estimated fee in weth:",expectedFee);

        foo.maxLoanWeth();
    }

    function testmaxLoanAll() public {

        // transfer weth to foo so that it can repay the loan
        vm.startPrank(wethProvider);
        IERC20(WETH).safeTransfer(address(foo), IERC20(WETH).balanceOf(wethProvider));
        vm.stopPrank();

        // transfer usdc to foo so that it can repay the loan
        vm.startPrank(usdcProvider);
        IERC20(USDC).safeTransfer(address(foo), IERC20(USDC).balanceOf(usdcProvider));
        vm.stopPrank();
        
        // transfer dai to foo so that it can repay the loan
        vm.startPrank(daiProvider);
        IERC20(DAI).safeTransfer(address(foo), IERC20(DAI).balanceOf(daiProvider));
        vm.stopPrank();

        foo.maxLoanAll();
    }
}