pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "forge-std/console2.sol";
import "../src/UniV2FlashSwap.sol";
import {SharedSetupBsc} from "./SharedSetup.sol";

// tests done on bsc network
// rpc: https://bsc-dataseed.binance.org 

contract Foo is UniV2FlashSwap, SharedSetupBsc {

    function maxLoanWbnb() external {
        flashSwap(WBNB, maxFlashSwap(WBNB));
    }

    function maxLoanAll() external {
        address[] memory tokens = new address[](4);
        uint256[] memory amounts = new uint256[](4);
        
        tokens[0] = WBNB;
        tokens[1] = BUSD;
        tokens[2] = USDT;
        tokens[3] = BTCB;
        amounts[0] = maxFlashSwap(WBNB);
        amounts[1] = maxFlashSwap(BUSD);
        amounts[2] = maxFlashSwap(USDT);
        amounts[3] = maxFlashSwap(BTCB);
        flashSwap(tokens, amounts);
    }

    function onUniV2FlashSwap() internal override {}
}


contract UniV2FlashSwapTest is Test , SharedSetupBsc {
    using SafeERC20 for IERC20;

    Foo foo;

    constructor(){
        vm.label(WBNB, "WBNB");
        vm.label(BUSD, "BUSD");
        vm.label(USDT, "USDT");
        vm.label(BTCB, "BTCB");
    }
    
    function setUp() public {
        foo = new Foo();
        vm.deal(address(foo), 0);
    }

    function testmaxLoanWbnb() public {

        // transfer weth to foo so that it can repay the loan
        vm.startPrank(wbnbProvider);
        IERC20(WBNB).safeTransfer(address(foo), IERC20(WBNB).balanceOf(wbnbProvider));
        vm.stopPrank();

        uint256 expectedFee = foo.estimateFlashSwapFee(WBNB ,foo.maxFlashSwap(WBNB));
        console2.log("=> estimated fee in wbnb:",expectedFee / 10**18);
        console2.log("=> max amount wbnb to borrow:", foo.maxFlashSwap(WBNB) / 10**18);
        console2.log("=> wbnb balance at start :", IERC20(WBNB).balanceOf(address(foo)) / 10**18);

        foo.maxLoanWbnb();
    }

    function testmaxLoanAll() public {

        // transfer wbnb to foo so that it can repay the loan
        vm.startPrank(wbnbProvider);
        IERC20(WBNB).safeTransfer(address(foo), IERC20(WBNB).balanceOf(wbnbProvider));
        vm.stopPrank();
        

        // transfer busd to foo so that it can repay the loan
        vm.startPrank(busdProvider);
        IERC20(BUSD).safeTransfer(address(foo), IERC20(BUSD).balanceOf(busdProvider));
        vm.stopPrank();
        
        // transfer usdt to foo so that it can repay the loan
        vm.startPrank(usdtProvider);
        IERC20(USDT).safeTransfer(address(foo), IERC20(USDT).balanceOf(usdtProvider));
        vm.stopPrank();

        // transfer btcb to foo so that it can repay the loan
        vm.startPrank(btcbProvider);
        IERC20(BTCB).safeTransfer(address(foo), IERC20(BTCB).balanceOf(btcbProvider));
        vm.stopPrank();

        console2.log("=> flash borrowed WBNB amount:", foo.maxFlashSwap(WBNB) / 1e18);
        console2.log("=> flash borrowed BUSD amount:", foo.maxFlashSwap(BUSD) / 1e18);
        console2.log("=> flash borrowed USDT amount:", foo.maxFlashSwap(USDT)/1e18);
        console2.log("=> flash borrowed BTCB amount:", foo.maxFlashSwap(BTCB)/1e18);

        foo.maxLoanAll();
    }
}